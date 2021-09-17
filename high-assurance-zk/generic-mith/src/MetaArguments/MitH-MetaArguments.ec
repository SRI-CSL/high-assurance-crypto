require import AllCore List Real Distr Dexcepted.

import RField.

theory ZKprot.

type witness_t.
type statement_t.

(* membership in language [L] is defined through relation [R] *)
op R : witness_t -> statement_t -> bool.


(* TYPES *)
type pauxdata_t.	(* Prover auxiliary data *)
type commitment_t.	(* Prover commitment *)
type vauxdata_t.	(* Verifier auxiliary data *)
type challenge_t.	(* Verifier challenge *)
type vstate_t.		(* Verifier internal state *)
type pstate_t.		(* Prover internal state *)
type response_t.	(* Prover response *)

(* single-execution verifier's view (see remarks bellow) *)
type view_t = commitment_t * challenge_t * vstate_t * response_t.
(* full views (possibly in iterated execution) *)
type fullview_t = view_t list.
(* Verifier view = (random_coins, communication_trace, result) *)
(* REMARK: w.l.o.g., we include the verifier's state in its view
 instead of the random coins -- notice that we shall quantify over
 all (possibly malicious) adversaries, hence we can assume it will
 include his random coins it the state. Moreover, we don't consider
 the result as it is determiniscally determined by the remaining
 components (additionally, we are concerned with perfectly-complete
 protocols, hende the preconditions of the ZK property shall enforce
 the "true" outcome). *)

(************************************)
(* 3-move Interactive Proof-Systems *)
(************************************)

(* PROVERS *)
type Prover_t =
 { commit: pauxdata_t -> witness_t -> statement_t -> (commitment_t*pstate_t) distr
 ; response: pstate_t -> challenge_t -> response_t * pauxdata_t
 }.

(* VERIFIERS *)
type Verifier_t =
 { challenge: vauxdata_t -> statement_t -> commitment_t -> (challenge_t*vstate_t) distr
 ; check: vstate_t -> response_t -> bool * vauxdata_t
 }.


module IPS = {
 (* prover/verifier auxiliary inputs *)
 var paux: pauxdata_t
 var vaux: vauxdata_t
 var view: view_t
 var fullview: fullview_t
 (* a single execution of the protocol *)
 proc exec(_P: Prover_t, _V: Verifier_t,
           _w: witness_t, _x: statement_t): bool = {
  var com, pst, chlv, vst, resp, b;
  (com, pst) <$ _P.`commit paux _w _x;
  (chlv, vst) <$ _V.`challenge vaux _x com;
  (resp, paux) <- _P.`response pst chlv;
  (b, vaux) <- _V.`check vst resp;
  view <- (com,chlv,vst,resp);
  return b;
 }
 (* N-sequential repetitions of the protocol 
   remark: notice that auxiliary inputs are chained *)
 proc execN(_N: int, _P: Prover_t, _V: Verifier_t,
            _w: witness_t, _x: statement_t): bool = {
  var i, b, initial_vaux;
  initial_vaux <- vaux;
  fullview <- [];
  b <- true;
  i <- 0;
  while (b && i < _N) {
   b <@ exec(_P,_V,_w,_x);
   fullview <- view::fullview; (* collects the single-execution trace (in reverse-order, for commodity) *)
   i <- i + 1;
  }
  return b;
 }
}.

(* a concrete Interactive Proof-System (P,V) *)
op P: Prover_t.
axiom Pcommit_ll paux w x: is_lossless (P.`commit paux w x).

op V: Verifier_t.
axiom Vchallenge_ll vaux x com: is_lossless (V.`challenge vaux x com).


(***********************)
(* perfect COMPLETNESS *)
(***********************)

section Completness.

axiom completness1 w x &m:
 R w x =>
 Pr [ IPS.exec(P,V,w,x) @ &m : res ] = 1%r.

lemma completness1_ph w x:
 R w x =>
 phoare [ IPS.exec
        : _P=P /\ _V=V /\ _w=w /\ _x=x ==> res ] = 1%r.
proof.
move=> /> onR .
 bypr => /> &m -> -> -> ->.
by apply (completness1 _ _ &m onR).
qed.

lemma completnessN N w x &m:
 0 < N =>
 R w x =>
 Pr [ IPS.execN(N,P,V,w,x) @ &m : res ] = 1%r.
proof.
move=> Npos onR.
byphoare (_: _N=N /\ _P=P /\ _V=V /\ _w=w /\ _x=x ==> _) => //.
proc; wp; sp; simplify.
while (0 <= i <= N /\ _N = N /\ _P=P /\ _V=V /\ _w=w /\ _x=x) (_N-i) N 1%r.
+ by move=> /> /#.
+ by move=> />.
+ by move=> /> * /#.
+ move=> hrec.
  exlim i => _i.
  seq 3: b 1%r 1%r 0%r 0%r
         (i=_i+1 /\ 0<=i<=N/\ _N=N /\ _P=P /\ _V=V /\ _w=w /\ _x=x).
  * by inline*; wp; rnd; rnd; wp; skip => /#.
  * wp; call (completness1_ph w x onR).
    by skip => /> *.
  * by conseq hrec => /> *.
  * wp; hoare; simplify.
    call (_:  _P = P /\ _V = V /\ _w = w /\ _x = x ==> res).
    by conseq (completness1_ph w x onR).
  * by move=> /> *.
  * by move=> /> *.
+ by inline*; wp; rnd predT; rnd predT; wp; skip => /> *; smt(Pcommit_ll Vchallenge_ll).
+ by move=> /> z; inline*; auto => /> *; smt(Pcommit_ll Vchallenge_ll).
qed.


end section Completness.


(*************)
(* SOUNDNESS *)
(*************)

section Soundness.

op sound1_err : real.
axiom soundness1 w x P' &m:
 (forall paux w x, is_lossless (P'.`commit paux w x)) =>
 (forall w, R w x = false) =>
 Pr [ IPS.exec(P',V,w,x) @ &m : res ] <= sound1_err.

lemma soundness1_spec w x P':
 (forall paux w x, is_lossless (P'.`commit paux w x)) =>
 (forall w, R w x = false) =>
 phoare [ IPS.exec : _P=P' /\ _V=V /\ _w=w /\ _x=x ==> res ] <= sound1_err.
proof.
move=> P_ll notR.
bypr => &m /> ->.
by apply (soundness1 _ _ _ &m); auto.
qed.

lemma soundnessN N w x P' &m:
 0 < N =>
 (forall paux w x, is_lossless (P'.`commit paux w x)) =>
 (forall w, R w x = false) =>
 Pr [ IPS.execN(N,P',V,w,x) @ &m : res ] <= sound1_err^N.
proof.
move=> Npos commit_ll notR.
byphoare (_: _N=N /\ _P=P' /\ _V=V /\ _w=w /\ _x=x ==> _) => //.
proc; wp; sp; simplify.
conseq (_: _ : (b2r b * sound1_err ^ (N - i))) => />.
while (0 <= i <= N /\ _N = N /\ _P=P' /\ _V=V /\ _w=w /\ _x=x) (_N-i) N 1%r.
+ by move=> /> /#.
+ by move=> />.
+ by move=> /> * /#.
+ move=> hrec.
  exlim i => _i.
  seq 3: b sound1_err (sound1_err^(N-(_i+1)))
         (1%r-sound1_err) 0%r
         (i=_i+1 /\ 0<=i<=N/\ _N=N /\ _P=P' /\ _V=V /\ _w=w /\ _x=x).
  * by inline*; wp; rnd; rnd; wp; skip => /> /#.
  * wp 1; call (soundness1_spec w x P' commit_ll notR).
    by skip => />. 
  * by conseq hrec => /> *.
  * rcondf 1; first by (auto => /#).
    by hoare; skip => /#.
  * move=> /> *.
    by rewrite -exprS /#.
+ by inline*; wp; rnd predT; rnd predT; wp; skip => /> *; smt(Vchallenge_ll).
+ by move=> /> z; inline*; auto => /> *; smt(Vchallenge_ll).
qed.

end section Soundness.

(******************)
(* ZERO-KNOWLEDGE *)
(******************)

(* section ZK1.*)

(* VIEW distinguisher (used for single executions)
 We omit the result of the verifier's check from the view, since
 we are dealing with perfectly complete protocols. 
*)
module type DRoI_t = {
 proc rOi(_V: Verifier_t,		(* !! malicious verifier *)
          _vaux: vauxdata_t,		(* auxiliary input *)
          _x: statement_t, 		(* statement *)
          _t: view_t		(* verifier's view *)
         ) : bool
}.

(* Ideal World (simulator) *)
type sstate_t.
(* [obs: apparently, EC gets in trouble with this declaration...]
op [lossless] scommit: statement_t -> challenge_t -> (commitment_t * sstate_t) distr.
*)
op scommit (x:statement_t) (c:challenge_t): (commitment_t * sstate_t) distr.
axiom scommit_ll x c: is_lossless (scommit x c).

op sresponse : sstate_t -> challenge_t -> response_t.
op [lossless] rnd_challenge: challenge_t distr.

(* The simulator guesses adversary's challenge. It's success is capture
 by the [good_challenge] predicate (for now, defined as equality! :-()  *)
op good_challenge (c1 c2: challenge_t): bool = c1=c2.
op guess_pr : real.
axiom prob_guess (c: challenge_t):
  mu rnd_challenge (good_challenge c) = guess_pr.

op Nsim: int. (* maximum number of tries to guess a [good_challenge] *)
axiom Nsim_pos: 0 < Nsim.

module ZK (D: DRoI_t) = {
  proc simulator(_V: Verifier_t, _vaux: vauxdata_t,
                 _x: statement_t) : view_t*vauxdata_t = {
  var i, bad, chl, com, sst, vaux', chlv, vst, resp, b, t;
  b <- witness; vaux' <- witness; t <- (witness,witness,witness,witness);
  chlv <- witness; com <- witness; sst <- witness; vst <- witness;
  i <- 0;
  bad <- true;
  while (bad && i < Nsim) {
   chl <$ rnd_challenge;
   (com, sst) <$ scommit _x chl;
   (chlv, vst) <$ _V.`challenge _vaux _x com;
   bad <- !good_challenge chl chlv;
   if (!bad) {
    resp <- sresponse sst chlv;
    (b, vaux') <- _V.`check vst resp;
    t <- (com,chlv,vst,resp);
   }
  i <- i + 1;
  }
 (* remark: returns '((witness,witness,witness),witness)' on failure *) 
  return (t,vaux'); 
 }
 proc game(_V: Verifier_t,
           _w: witness_t, _x: statement_t,
           _roi: bool): bool = {
  var b, b', vaux, vaux', t;
  vaux <- IPS.vaux;
  if (_roi) {
   b <@ IPS.exec(P,_V,_w,_x);
   t <- IPS.view;
  } else {
   (t,vaux') <@ simulator(_V,vaux,_x);
  }
  b' <@ D.rOi(_V,vaux,_x,t);
  return b';
 }
}.

(*
    OVERVIEW OF THE PROOF STRATEGY FOR THE ZK PROPERTY

 As have been mentioned, the simulation strategy is based on guessing
the Verifier's challenge (a polynomial number of attempts), so that it
would be possible to produce a valid transcript without knowing the
witness. In this meta-result, we will take as an assumption that we are
able to exhibit a computationally indistinguishable transcript for a
single execution under the hypothesis of a successful guess.
We would like to show that iterating the above procedure would allow
to reduce the failure probability to a neglible value.

The proof is structured in two hops:

 Hop 1: replace the real world experiment [real] with a modified version
        that iterates while trying to guess the adversary's challenge
        (but not really making any use of that guess). This new experiment
        is called [realn].

 Hop 2: [ideal] behaves as [realn], but relies on the guessed challenge
        to produce the commitment(s) (no longer relying on the knowledge of
        the witness).
    This second hop is further splitted in the following two hybrid arguments:
     1) | Pr[realn /\ !bad] - Pr[ideal /\ !bad] | <= N*eps_sim1
     2) | Pr[realn /\ bad] - Pr[realn' /\ bad] | <= eps_fail^N + N*eps_sim1
    where [N] is the number of attempts; [fail_prob] the probability of failure
    in guessing the challenge, and [eps_sim1] distinguishing probabilty for
    the replacement of commitments.

    Combined, they establish the result:

           | Pr[realn] - Pr[ideal] | <= fail_prob^N + 2*N*eps_sim1

 Overall, the ZK property would established that:

         | Pr[real] - Pr[ideal] | <= fail_prob^N + 2*N*eps_sim1
*)


module Hops(D : DRoI_t) = {
 var bad: bool
 proc real0(_V: Verifier_t, _paux: pauxdata_t, _vaux:vauxdata_t,
            _w: witness_t, _x: statement_t)
           : (commitment_t*pstate_t)*(challenge_t*vstate_t) = {
  var com,pst,chl,vst;
  (com,pst) <$ P.`commit _paux _w _x;
  (chl,vst) <$ _V.`challenge _vaux _x com;
  return ((com,pst),(chl,vst));
 }
 proc real(_V, _w: witness_t, _x: statement_t): bool = {
   var b, vaux, pp, pp', vv;
   vaux <- IPS.vaux;
   (pp,vv) <@ real0(_V, IPS.paux, IPS.vaux, _w, _x);
   pp' <- P.`response pp.`2 vv.`1;
   b <@ D.rOi(_V,vaux, _x, (pp.`1,vv.`1,vv.`2,pp'.`1));
   return b;
 }
 proc realn0(_V: Verifier_t, _paux: pauxdata_t, _vaux: vauxdata_t,
             _w: witness_t, _x: statement_t)
            : (commitment_t*pstate_t)*(challenge_t*vstate_t) = {
  var i,com,pst,chl,chlv,vst;
  chl <- witness; com <- witness; pst <- witness; chlv <- witness; vst <- witness;
  i <- 0;
  bad <- true;
  while (bad && i < Nsim) { 
   chl <$ rnd_challenge;
   (com,pst) <$ P.`commit _paux _w _x;
   (chlv,vst) <$ _V.`challenge _vaux _x com;
   bad <- !good_challenge chl chlv;
   i <- i + 1; 
  }
  return ((com,pst),(chlv,vst));
 }
 proc realn1(_V: Verifier_t, _w : witness_t, _x : statement_t)
            : view_t = {
  var pp,vv,resp;
  resp <- witness;
  (pp,vv) <@ realn0(_V,IPS.paux,IPS.vaux,_w,_x);
  resp <- (P.`response pp.`2 vv.`1).`1;
  return (pp.`1,vv.`1,vv.`2,resp);
 }
 proc realn(_l: int,
            _V: Verifier_t,
            _w: witness_t, _x: statement_t
           ): bool = {
  var com, pst, sst, chl, chlv, vst, i, b, t;
  com <- witness; pst <- witness; sst <- witness;
  chlv <- witness; vst <- witness;
  t <- (witness,witness,witness,witness);
  i <- 0;
  bad <- true;
  while (bad && i < _l) { 
   chl <$ rnd_challenge;
   (com, sst) <$ scommit _x chl;
   (chlv, vst) <$ _V.`challenge IPS.vaux _x com;
   bad <- !good_challenge chl chlv;
   if (!bad) {
    t <- (com, chlv, vst, sresponse sst chlv);
   } else {
    t <- (witness,witness,witness,witness);
   }
   i <- i + 1; 
  }
  while (bad && i < Nsim) {
   chl <$ rnd_challenge;
   (com, pst) <$ P.`commit IPS.paux _w _x;
   (chlv, vst) <$ _V.`challenge IPS.vaux _x com;
   bad <- !good_challenge chl chlv;
   t <- (com, chlv, vst, (P.`response pst chlv).`1);
   i <- i + 1; 
  }
  b <@ D.rOi(_V,IPS.vaux, _x, t);
  return b;
 }
}.


(* HOP1 - [real] ~ [realn] 
   where [realn] loops [real] in trying to guess a [good_challenge] *)

lemma real0_pr (D <: DRoI_t{IPS,Hops}) V' paux vaux w x &m y:
 Pr [ Hops(D).real0(V',paux,vaux,w,x) @ &m : res=y ] =
 mu1 (P.`commit paux w x) y.`1 * mu1 (V'.`challenge vaux x y.`1.`1) y.`2.
proof.
byphoare (_: _V=V' /\ _paux=paux /\ _vaux=vaux /\ _w=w /\ _x=x ==> _) => //.
proc; simplify; wp.
seq 1: ((com,pst) = y.`1)
       (mu1 (P.`commit paux w x) y.`1) (mu1 (V'.`challenge vaux x y.`1.`1) y.`2)
       (1%r-(mu1 (P.`commit paux w x)) y.`1) 0%r
       (_V=V' /\ _paux=paux /\ _vaux=vaux /\ _w=w /\ _x=x) => //.
+ rnd; skip; smt().
+ rnd ((=) y.`1); skip; smt().
+ rnd ((=) y.`2); skip; smt().
+ hoare; rnd; skip; smt().
qed.

lemma realn0_pr (D <: DRoI_t{IPS,Hops}) (V':Verifier_t)  paux vaux w x &m y:
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 Pr [ Hops(D).realn0(V',paux,vaux,w,x) @ &m : res=y ] =
 mu1 (P.`commit paux w x) y.`1 * mu1 (V'.`challenge vaux x y.`1.`1) y.`2.
proof.
(* actualmente, sem alternativas a manter o predicado [good_challenge] como sendo a igualdade!!! :-( *)
move=> V_ll.
have Nsim_pos := Nsim_pos.
byphoare (_: _V=V' /\ _paux=paux /\ _vaux=vaux /\ _w=w /\ _x=x ==> _) => //.
proc; simplify; wp; sp.
while (#[8:]pre /\ 0 <= i <= Nsim) (Nsim-i) Nsim 1%r.
- by move=> * /#.
- by move=> /> * /#.
- by move=> /> * /#.
- move=> /> hrec.
  pose PrCom := mu1 (P.`commit paux w x) y.`1.
  pose PrChal := mu1 (V'.`challenge vaux x y.`1.`1) y.`2.
  swap 1 2.
  case (i+1=Nsim).
   rcondf 6; first by wp; do 3! rnd; skip => /> /#.
   seq 1: ((com,pst)=y.`1)
          PrCom PrChal
          (1%r-PrCom) 0%r
          (_V=V' /\ _vaux=vaux /\ _x=x).
   + by rnd; skip => /> *.
   + by rnd ((=) y.`1); skip => /> /#.
   + seq 1: ((chlv,vst)=y.`2)
            PrChal 1%r
            (1%r-PrChal) 0%r
            ((com,pst)=y.`1).
     * by rnd; skip; auto.
     * by rnd ((=) y.`2); skip => /#.
     * by wp; rnd predT ; skip; smt(rnd_challenge_ll).
     * by hoare; wp; rnd; skip => /#.
     * by auto.
  + by hoare; wp; rnd; rnd; skip => /#.
  + by auto.
  seq 2: (((com,pst),(chlv,vst)) = y)
         (PrCom*PrChal)
         (guess_pr + (1%r-guess_pr)*PrCom*PrChal)
         (1%r-PrCom*PrChal)
         ((1%r-guess_pr)*PrCom*PrChal)
         (#[/:6]pre /\ 0 <= i < Nsim).
  + by rnd; rnd; skip => /> /#.
  + seq 1: ((com,pst)=y.`1)
           PrCom PrChal
           (1%r-PrCom) 0%r
           (#[/:6]pre).
    * by rnd; skip => /> *.
    * by rnd ((=) y.`1); skip => /> /#.
    * by rnd ((=) y.`2);  skip => /> /#.
    * by hoare; rnd; skip => /> /#.
    * by auto.
  + seq 1: (good_challenge chl chlv)
           guess_pr 1%r
           (1%r-guess_pr) (PrCom*PrChal)
           (#[/:6]pre /\ 0 <= i < Nsim /\ ((com,pst),(chlv,vst))=y).
    * by wp; rnd; skip => /> * /#.
    * wp; rnd; skip => /> &hr; progress.
      move: (prob_guess chlv{hr}); smt(). 
    * rcondf 3.
       by wp;skip => /> *.
      by wp;skip => * /#.
    * wp; rnd; skip => /> &m' *.
      rewrite (mu_eq _ _ (predC (pred1 chlv{m'}))) 1:/#.
      rewrite mu_not rnd_challenge_ll; smt (prob_guess).
    * by sp; conseq hrec => /> /#.
    * by move => /> /#.
  + seq 1: ((com,pst)=y.`1)
           PrCom (1%r-PrChal)
           (1%r-PrCom) 1%r
           (#[/:6]pre).
    * by rnd; skip => /> *.
    * by rnd ((=) y.`1); skip => /> /#.
    * rnd (predC ((=) y.`2));  skip => /> *.
      by rewrite !mu_not !V_ll /#.
    * rnd (predC ((=) y.`1)); skip => /> *.
      by rewrite !mu_not !Pcommit_ll /#.
    * rnd predT; skip => /> *; smt().
    * smt().
  + seq 1: (good_challenge chl chlv)
           guess_pr 0%r
           (1%r-guess_pr) (PrCom*PrChal)
           (#[/:6]pre /\ ((com, pst), (chlv, vst)) <> y /\ 0 <= i < Nsim).
    * by wp; rnd; skip => /> /#.
    * by hoare; sp; rcondf 1; skip => />.
    * wp; rnd; skip => /> &m' *.
      rewrite (mu_eq _ _ (predC (pred1 chlv{m'}))) 1:/#.
      by rewrite mu_not rnd_challenge_ll -(prob_guess chlv{m'}) /good_challenge /#.
    * by sp; conseq hrec => /> * /#.
    * by move => /> /#.
  + by move=> /> /#.
- wp; rnd. 
  rnd predT; rnd; skip;
  smt(Pcommit_ll rnd_challenge_ll).
- move=> /> *. 
  by wp; rnd; rnd predT; rnd; skip; progress;
  smt(Pcommit_ll rnd_challenge_ll).
qed.

lemma hop1 (D <: DRoI_t{IPS,Hops}) V' w x &m:
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 Pr [ ZK(D).game(V',w,x,true) @ &m : res ]
 = Pr [ Hops(D).realn(0,V',w,x) @ &m : res ].
proof.
move=> V'_ll.
have ->: Pr[ZK(D).game(V', w, x, true) @ &m : res]
         = Pr[Hops(D).real(V', w, x) @ &m : res].
 byequiv (_:  ={_V,_w,_x,IPS.paux,IPS.vaux,glob D} /\ _roi{1} ==> ={res}) => //.
 proc; simplify; rcondt {1} 2; first by auto.
 call (_: true); simplify.
 by inline*; wp; rnd; rnd; wp; skip.
byequiv (_:  ={_V,_w,_x,IPS.paux,IPS.vaux,glob D} /\ (_V,_l){2}=(V',0)  ==> ={res}) => //.
have Nsim_pos := Nsim_pos.
proc.
rcondf {2} 9; first by move=> *; auto.
simplify.
transitivity {2} { t <@ Hops(D).realn1(V',_w,_x); 
                   b <@ D.rOi(_V,IPS.vaux, _x, t); }
             ( ={_V,_w,_x,IPS.paux,IPS.vaux,glob D} /\ _V{2}=V' ==> ={b} )
             ( ={_V,_w,_x,IPS.paux,IPS.vaux,glob D} /\ _V{2}=V' ==> ={b} ).
+ by move=> &1 &2 /> *; exists (glob D){2} IPS.paux{2} IPS.vaux{2} _V{2} _w{2} _x{2}.
+ by auto.
+ inline Hops(D).realn1; call (_:true).
  wp; call (_: ={_V,_paux,_vaux,_w,_x} /\ _V{2}=V'==> ={res}).
   bypr res{1} res{2} => /=; first smt().
   move=> &1 &2 [[com pst]chlv] /> -> ->.
   rewrite (real0_pr D) (realn0_pr D) // /#.
  by wp; skip; progress.
+ inline*.
  call (_:true); wp; simplify.
  while (={Hops.bad} /\
         (i0,_paux,_vaux,_V1,_w1,_x1,com0,pst0,chlv0,vst0){1}
         = (i,IPS.paux,IPS.vaux,_V,_w,_x,com,pst,chlv,vst){2} /\
         (0<=i<=Nsim /\ (Hops.bad /\ i=0 \/ t=(com,chlv,vst,(P.`response pst chlv).`1))){2}).
   by wp; rnd; rnd; rnd; skip => /> /#.
  by wp; skip => /> /#.
qed.

(* 

  HOP2 - | Pr[realn] - Pr[ideal] | <= fail_prob^N + 2*N*eps_sim1 

*)


(*
    BAD EVENT LEMMATA
 Some auxiliary results concerning the bad event (failure in guessing
 the challenge) in both the Real/Ideal worlds.               
*)

(* bad event directly as distributions... *)
op dbad_real paux V' vaux w x =
 dmap (rnd_challenge `*` (dfst (dlet (dfst (P.`commit paux w x)) (V'.`challenge vaux x))))
      (fun cc:_*_ => !good_challenge cc.`1 cc.`2).

lemma dbad_real_ll paux V' vaux w x:
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 is_lossless (dbad_real paux V' vaux w x).
proof.
move=> V_ll.
rewrite /dbad_real dmap_ll dprod_ll rnd_challenge_ll /=.
rewrite dmap_ll dlet_ll.
 by rewrite dmap_ll Pcommit_ll. 
by move => *; rewrite V_ll.
qed.

op dbad_ideal V' vaux x =
 dmap (dlet rnd_challenge
       (fun c => dunit c
                 `*` dfst (dlet (dfst (scommit x c)) (V'.`challenge vaux x))))
      (fun x:_*_ => !good_challenge x.`1 x.`2).

lemma dbad_ideal_ll V' vaux x:
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 is_lossless (dbad_ideal V' vaux x).
proof.
move=> V_ll.
rewrite /dbad_ideal dmap_ll dlet_ll ?rnd_challenge_ll /= => c Hc.
rewrite dprod_ll {1}/is_lossless dunit_ll /= dmap_ll dlet_ll.
 by rewrite dmap_ll scommit_ll.
by move => *; rewrite V_ll.
qed.

module BadProcs = {
 proc pbad_real(_paux: pauxdata_t, _V: Verifier_t, _vaux: vauxdata_t,
                _w: witness_t, _x: statement_t) : bool = {
  var b, chl, com, pst, chlv, vst;
  chl <$ rnd_challenge;
  (com,pst) <$ P.`commit _paux _w _x;
  (chlv,vst) <$ _V.`challenge _vaux _x com;
  b <- !good_challenge chl chlv;
  return b;
 }
 proc dbad_real(_paux: pauxdata_t, _V: Verifier_t, _vaux: vauxdata_t,
                _w: witness_t, _x: statement_t) : bool = {
  var b;
  b <$ dbad_real _paux _V _vaux _w _x;
  return b;
 }
 proc pbad_ideal(_V: Verifier_t, _vaux: vauxdata_t, _x: statement_t): bool = {
  var b, chl, com, sst, chlv, vst;
  chl <$ rnd_challenge;
  (com,sst) <$ scommit _x chl;
  (chlv,vst) <$ _V.`challenge _vaux _x com;
  b <- !good_challenge chl chlv;
  return b;
 }
 proc dbad_ideal(_V: Verifier_t, _vaux: vauxdata_t, _x: statement_t): bool = {
  var b;
  b <$ dbad_ideal _V _vaux _x;
  return b;
 }
 proc dbad_lor(_paux: pauxdata_t, _V: Verifier_t, _vaux: vauxdata_t,
               _w: witness_t, _x: statement_t, _lor: bool) : bool = {
   var b;
   if (_lor) {
    b <@ dbad_real(_paux,_V,_vaux,_w,_x);
   } else {
    b <@ dbad_ideal(_V,_vaux,_x);
   }
   return b;
 }
 proc pbad_lor(_paux: pauxdata_t, _V: Verifier_t, _vaux: vauxdata_t,
               _w: witness_t, _x: statement_t, _lor: bool) : bool = {
   var b;
   if (_lor) {
    b <@ pbad_real(_paux,_V,_vaux,_w,_x);
   } else {
    b <@ pbad_ideal(_V,_vaux,_x);
   }
   return b;
 }
 proc pbad_iter(_paux: pauxdata_t, _V: Verifier_t, _vaux: vauxdata_t,
                _w: witness_t, _x: statement_t, _lor: bool, _n:int) : bool = {
  var i, b;
  b <- true;
  i <- 0;
  while (b && i < _n) {
   b <@ pbad_lor(_paux,_V,_vaux,_w,_x,_lor);
   i <- i + 1;
  }
  return b;
  }
 proc dbad_iter(_paux: pauxdata_t, _V: Verifier_t, _vaux: vauxdata_t,
                _w: witness_t, _x: statement_t, _lor: bool, _n:int) : bool = {
  var i, b;
  b <- true;
  i <- 0;
  while (b && i < _n) {
   b <@ dbad_lor(_paux,_V,_vaux,_w,_x,_lor);
   i <- i + 1;
  }
  return b;
  }
 }.

require import DProd DMap.
clone DMapSampling as DMapBad
 with type t1 <- challenge_t*challenge_t,
      type t2 <- bool.
clone ProdSampling as DProdCC
 with type t1 <- challenge_t,
      type t2 <- challenge_t.
clone DMapSampling as DfstP
 with type t1 <- commitment_t * pstate_t,
      type t2 <- commitment_t.
clone DLetSampling as DLetPV
 with type t <- commitment_t,
      type u <- challenge_t * vstate_t.
clone DMapSampling as DfstV
 with type t1 <- challenge_t * vstate_t,
      type t2 <- challenge_t.

equiv bad_real_eq:
 BadProcs.pbad_real ~ BadProcs.dbad_real 
 : ={_paux, _V, _vaux, _w, _x} ==> ={res}.
proof.
proc; simplify.
transitivity {1}
 { b <@ DMapBad.S.map(rnd_challenge `*` (dfst (dlet (dfst (P.`commit _paux _w _x)) (_V.`challenge _vaux _x))), fun cc:_*_ => !good_challenge cc.`1 cc.`2); }
 (={_paux, _V, _vaux, _w, _x} ==> ={b})
 (={_paux, _V, _vaux, _w, _x} ==> ={b}) => //.
  by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2}.
 inline*.
 swap {2} 2 1; wp; simplify.
 transitivity {1}
  { chl <$ rnd_challenge;
    chlv <$ (dfst (dlet (dfst (P.`commit _paux _w _x)) (_V.`challenge _vaux _x))); }
  (={_paux, _V, _vaux, _w, _x} ==> ={chl, chlv})
  (={_paux, _V, _vaux, _w, _x} ==> (chl, chlv){1}=(r1.`1,r1.`2){2}).
    by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2}.
   by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2}.
  seq 1 1: (#pre /\ ={chl}); first by rnd; skip.
  transitivity {1}
   { chlv <@ DfstV.S.sample(dlet (dfst (P.`commit _paux _w _x)) (_V.`challenge _vaux _x), fst); }
   ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={chl,chlv} )
   ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={chl,chlv} ) => //.
    by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2} chl{2}.
   transitivity {2}
    { chlv <@ DfstV.S.map(dlet (dfst (P.`commit _paux _w _x)) (_V.`challenge _vaux _x), fst); }
    ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={chl,chlv} )
    ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={chl,chlv} ) => //.
     by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2} chl{2}.
    inline*.
    transitivity {1}
     { (chlv,vst) <@ DLetPV.SampleDep.sample(dfst (P.`commit _paux _w _x), _V.`challenge _vaux _x); }
     ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={chl, chlv} )
     ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={chl, chlv} ) => //.
      by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2} chl{2}.
     inline*; swap {2} 2 1; wp; rnd; wp.
     transitivity {1}
      { com <@ DfstP.S.map(P.`commit _paux _w _x, fst); }
      ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={_V,_vaux,_x,chl,com})
      ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={_V,_vaux,_x,chl} /\ com{1}=t{2}) => //.
       by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2} chl{2}.
      by inline*; wp; rnd; wp; skip.
     transitivity {2}
      { t <@ DfstP.S.sample(P.`commit _paux _w _x, fst); }
      ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={_V,_vaux,_x,chl} /\ com{1}=t{2} )
      ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={_V,_vaux,_x,chl,t}) => //.
       by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2} chl{2}.
      by symmetry; call DfstP.sample; skip.
     by inline*; wp; rnd; wp; skip.
    swap {2} 2 1; wp; simplify.
    transitivity {2}
     { r1 <@ DLetPV.SampleDLet.sample(dfst (P.`commit _paux _w _x), _V.`challenge _vaux _x); }
     ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={chl} /\ chlv{1} = r1{2}.`1 )
     ( ={_paux, _V, _vaux, _w, _x, chl} ==> ={chl, r1} ) => //.
      by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2} chl{2}.
     by call DLetPV.SampleDepDLet.
    by inline*; wp; rnd; wp; skip.
   by symmetry; call DfstV.sample.
  by inline*; wp; rnd; wp; skip.
 transitivity {1}
  { (chl,chlv) <@ DProdCC.S.sample2(rnd_challenge, dfst (dlet (dfst (P.`commit _paux _w _x)) (_V.`challenge _vaux _x))); }
  (={_paux, _V, _vaux, _w, _x} ==> ={chl, chlv})
  (={_paux, _V, _vaux, _w, _x} ==> (chl, chlv){1}=(r1.`1,r1.`2){2}) => //.
   by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2}.
  by inline*; wp; rnd; rnd; wp; skip.
 transitivity {2}
  { r1 <@ DProdCC.S.sample(rnd_challenge, dfst (dlet (dfst (P.`commit _paux _w _x)) (_V.`challenge _vaux _x))); }
  (={_paux, _V, _vaux, _w, _x} ==> (chl, chlv){1}=(r1.`1,r1.`2){2})
  (={_paux, _V, _vaux, _w, _x} ==> ={r1}) => //.
   by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2}.
  by symmetry; call DProdCC.sample_sample2; skip.
 by inline*; wp; rnd; wp; skip.
transitivity {2}
 { b <@ DMapBad.S.sample(rnd_challenge `*` (dfst (dlet (dfst (P.`commit _paux _w _x)) (_V.`challenge _vaux _x))), fun cc:_*_ => !good_challenge cc.`1 cc.`2); }
 (={_paux, _V, _vaux, _w, _x} ==> ={b})
 (={_paux, _V, _vaux, _w, _x} ==> ={b}) => //.
  by move=> /> &2; exists _V{2} _paux{2} _vaux{2} _w{2} _x{2}.
 by symmetry; call DMapBad.sample.
by inline*; wp; rnd; wp; auto.
qed.

lemma dbad_real_pr paux V' vaux w x:
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 phoare [ BadProcs.dbad_real : _paux=paux/\_V=V'/\_vaux=vaux/\_w=w/\_x=x ==> res ]
 = (mu1 (dbad_real paux V' vaux w x) true).
proof.
move=> V_ll; proc; rnd; skip => />; progress; smt.
qed.

lemma pbad_real_pr V': 
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 phoare [ BadProcs.pbad_real : _V=V' ==> res ] = (1%r-guess_pr).
proof.
move=> V_ll; proc.
swap 1 2; wp; rnd; do 2! (rnd predT); skip => />; progress.
+ smt(Pcommit_ll).
+ smt().
+ rewrite /good_challenge mu_not rnd_challenge_ll -(prob_guess v0.`1) /good_challenge /#.
qed.

lemma dbad_real_guess_pr paux V' vaux w x &m:
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 mu1 (dbad_real paux V' vaux w x) true = 1%r - guess_pr.
proof.
move=> V_ll.
have <-: Pr[ BadProcs.dbad_real(paux,V',vaux,w,x) @ &m : res ]
         = mu1 (dbad_real paux V' vaux w x) true.
 by byphoare (dbad_real_pr paux V' vaux w x V_ll).
have <-: Pr[ BadProcs.pbad_real(paux,V',vaux,w,x) @ &m : res ]
         = (1%r - guess_pr).
 by byphoare (pbad_real_pr V' V_ll).
by rewrite eq_sym; byequiv bad_real_eq.
qed.

clone DLetSampling as DLetCSV
 with type t <- challenge_t,
      type u <- challenge_t * challenge_t.
clone DLetSampling as DLetSV
 with type t <- commitment_t,
      type u <- challenge_t * vstate_t.
clone import DMapSampling as DSfst
 with type t1 <- commitment_t * sstate_t,
      type t2 <- commitment_t.
clone DMapSampling as DfstS
 with type t1 <- commitment_t * sstate_t,
      type t2 <- commitment_t.

equiv bad_ideal_eq:
 BadProcs.pbad_ideal ~ BadProcs.dbad_ideal
 : ={_V, _vaux, _x} ==> ={res}.
proof.
proc; simplify.
transitivity {1}
 { b <@ DMapBad.S.map(dlet rnd_challenge
            (fun c => dunit c
                      `*` dfst (dlet (dfst (scommit _x c)) (_V.`challenge _vaux _x))), fun cc:_*_ => !good_challenge cc.`1 cc.`2); }
 (={_V, _vaux, _x} ==> ={b})
 (={_V, _vaux, _x} ==> ={b}) => //;
  1:(by move=> /> &2; exists _V{2} _vaux{2} _x{2}); last first.
 transitivity {2}
  { b <@ DMapBad.S.sample(dlet rnd_challenge
                     (fun c => dunit c
                      `*` dfst (dlet (dfst (scommit _x c)) (_V.`challenge _vaux _x))), fun cc:_*_ => !good_challenge cc.`1 cc.`2); }
  (={_V, _vaux, _x} ==> ={b})
  (={_V, _vaux, _x} ==> ={b}) => //.
   by move=> /> &2; exists _V{2} _vaux{2} _x{2}.
  by symmetry; call DMapBad.sample.
 by inline*; wp; rnd; wp; auto.
inline*; swap {2} 2 1; wp; simplify.
transitivity {1}
 { (chl,chlv) <@ DLetCSV.SampleDep.sample(rnd_challenge,
                  fun c => dunit c
                      `*` dfst (dlet (dfst (scommit _x c)) (_V.`challenge _vaux _x))); }
 (={_V, _vaux, _x} ==> ={chl,chlv})
 (={_V, _vaux, _x} ==> (chl,chlv){1}=(r1.`1,r1.`2){2}) => //;
  1:( by move=> /> &2; exists _V{2} _vaux{2} _x{2}); last first.
 transitivity {2}
  { r1 <@ DLetCSV.SampleDLet.sample(rnd_challenge,
                  fun c => dunit c
                      `*` dfst (dlet (dfst (scommit _x c)) (_V.`challenge _vaux _x))); }
  (={_V, _vaux, _x} ==> (chl,chlv){1}=(r1.`1,r1.`2){2})
  (={_V, _vaux, _x} ==> ={r1}) => //.
   by move=> /> &2; exists _V{2} _vaux{2} _x{2}.
  by call DLetCSV.SampleDepDLet.
 by inline*; wp; rnd; wp; skip. 
inline*; swap {2} 2 1.
seq 1 2: (#pre /\ chl{1}=t{2}); first by rnd; wp; skip.
transitivity {1}
 { (chl, chlv) <@ DProdCC.S.sample2(dunit chl,dfst (dlet (dfst (scommit _x chl)) (_V.`challenge _vaux _x))); }
 ( ={_V, _vaux, _x, chl} ==> ={chl, chlv} )
 ( ={_V, _vaux, _x} /\ chl{1} = t{2} ==> ={chl, chlv} ) => //;
 1:(by move=> /> &2; exists _V{2} _vaux{2} _x{2} t{2}); last first.
 wp. transitivity {2}
  { u <@ DProdCC.S.sample(dunit t,dfst (dlet (dfst (scommit _x t)) (_V.`challenge _vaux _x))); }
  ( ={_V, _vaux, _x} /\ chl{1} = t{2} ==> (chl, chlv){1}=u{2} )
  ( ={_V,_vaux,_x,t} ==> ={u} ) => //;
   1:(by move=> /> &2; exists _V{2} _vaux{2} _x{2} t{2});
   last first.
  by inline*; wp; rnd; wp; skip.
 by symmetry; call DProdCC.sample_sample2; skip => /> /#.
inline*; swap {2} 2 1.
seq 0 2: (#pre /\ chl{1}=r1{2}).
 by rnd {2}; wp; skip => /> &2; smt (dunit_ll supp_dunit).
transitivity {1}
 { chlv <@ DfstV.S.map(dlet (dfst (scommit _x chl)) (_V.`challenge _vaux _x), fst); }
 ( ={_V, _vaux, _x, chl} ==> ={chl, chlv} )
 ( ={_V, _vaux, _x, chl} /\ r1{2} = chl{2} ==> ={chl, chlv} ) => //;
  1:(by move=> /> &2 *; exists _V{2} _vaux{2} _x{2} r1{2}); last first.
 wp; transitivity {2}
  { r2 <@ DfstV.S.sample(dlet (dfst (scommit _x r1)) (_V.`challenge _vaux _x), fst); }
 ( ={_V, _vaux, _x} /\ r1{2}=chl{1} ==> (chl, chlv){1}=(r1,r2){2} )
 ( ={_V, _vaux, _x, r1} /\ (r1=chl){2} ==> ={r1, r2} /\ (r1=chl){2}) => //;
  1:(by move=> /> &2 *; exists _V{2} _vaux{2} _x{2} chl{2});
  last first.
  by inline*; wp; rnd; wp; skip.
 by symmetry; call DfstV.sample.
inline*; swap {2} 2 1; wp; simplify.
transitivity {1}
 { (chlv,vst) <@ DLetSV.SampleDep.sample(dfst (scommit _x chl), _V.`challenge _vaux _x); }
 ( ={_V, _vaux, _x, chl} ==> ={chl, chlv} )
 ( ={_V, _vaux, _x, chl} ==> ={chl} /\ chlv{1}=r1{2}.`1 ) => //;
  1:(by move=> /> &2; exists _V{2} _vaux{2} _x{2} chl{2});
 last first.
 transitivity {2}
  { r1 <@  DLetSV.SampleDLet.sample(dfst (scommit _x chl), _V.`challenge _vaux _x); }
  ( ={_V, _vaux, _x, chl} ==> ={chl} /\ chlv{1}=r1{2}.`1 )
  (  ={_V, _vaux, _x, chl} ==> ={chl,r1} ) => //;
   1:(by move=> /> &2; exists _V{2} _vaux{2} _x{2} chl{2});
   last first.
  by inline*; wp; rnd; wp; skip. 
 by call DLetSV.SampleDepDLet.
inline*; swap {2} 2 1; wp; rnd; wp.
transitivity {1}
 { com <@ DfstS.S.map(scommit _x chl, fst); }
 ( ={_V, _vaux, _x, chl} ==> ={_V,_vaux,_x,chl,com})
 ( ={_V, _vaux, _x, chl} ==> ={_V,_vaux,_x,chl} /\ com{1}=t{2}) => //.
  by move=> /> &2; exists _V{2} _vaux{2} _x{2} chl{2}.
 by inline*; wp; rnd; wp; skip.
transitivity {2}
 { t <@ DfstS.S.sample(scommit _x chl, fst); }
 ( ={_V, _vaux, _x, chl} ==> ={_V,_vaux,_x,chl} /\ com{1}=t{2} )
 ( ={_V, _vaux, _x, chl} ==> ={_V,_vaux,_x,chl,t}) => //.
  by move=> /> &2; exists _V{2} _vaux{2} _x{2} chl{2}.
 by symmetry; call DfstS.sample; skip.
by inline*; wp; rnd; wp; skip.
qed.

equiv bad_lor_eq:
 BadProcs.pbad_lor ~ BadProcs.dbad_lor
 : ={_paux,_V,_vaux,_w,_x,_lor} ==> ={res}.
proof.
proc; simplify; if => //.
 by call bad_real_eq.
by call bad_ideal_eq.
qed.

lemma bad_lor_pr paux V' vaux w x lor:
 phoare [ BadProcs.pbad_lor 
        : _paux=paux /\ _V=V' /\ _vaux=vaux /\ _w=w /\ _x=x /\ _lor=lor
        ==> res
        ] = (mu1 (if lor then dbad_real paux V' vaux w x else dbad_ideal V' vaux x) true).
proof.
bypr => &m' [->[->[->[->[->->]]]]].
have ->: 
 Pr[BadProcs.pbad_lor(paux, V', vaux, w, x, lor) @ &m': res]
 = Pr[BadProcs.dbad_lor(paux, V', vaux, w, x, lor) @ &m': res]
 by byequiv bad_lor_eq.
byphoare (_:_paux=paux /\ _V=V' /\ _vaux=vaux /\ _w=w /\ _x=x /\ _lor=lor
        ==> res) => //.
proc; inline*; if.
 wp; rnd; wp; skip => />; smt.
wp; rnd; wp; skip => />; smt.
qed.

lemma bad_iter_eq n:
 0 <= n =>
 equiv [ BadProcs.pbad_iter ~ BadProcs.dbad_iter
       : ={_paux,_V,_vaux,_w,_x,_lor,_n} /\ _n{2}=n ==> ={res} ].
proof.
move=> Hn; proc; simplify.
while (#pre /\ ={i,b} /\ 0 <= i{2} <= _n{2}).
 by wp; call bad_lor_eq; skip => /#.
by wp; skip => /#.
qed.

lemma dbad_iter_pr lor paux V' vaux w x n &m:
 0 <= n =>
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 Pr [ BadProcs.dbad_iter(paux,V',vaux,w,x,lor,n) @ &m : res ]
 = (mu1 (if lor
         then dbad_real paux V' vaux w x
         else dbad_ideal V' vaux x) true)^n.
proof.
move=> Hn V_ll.
pose dbad := if lor then dbad_real paux V' vaux w x else dbad_ideal V' vaux x.
byphoare (_: _paux=paux /\ _V=V' /\ _vaux=vaux /\ _w=w /\ _x=x
             /\ _lor=lor /\ _n=n ==> res) => //.
proc; simplify; inline*.
sp; conseq (_:_: (b2r b * (mu1 dbad true)^(n-i))) => //.
while (#[3:]pre /\ 0 <= i <= n) (n-i) n 1%r => //.
move=> *.
+ by move=> /> * /#.
+ move=> hrec.
  pose epsguess := mu1 dbad true.
  exlim i => _i.
  case (i+1=n).
   rcondf 10; first by wp; sp; if => //; wp; rnd; wp; skip => /> /#.
   wp; sp; if => //; wp; rnd; wp; skip => />; progress.
    rewrite /dbad H3 /= (_:_i+1-_i=1) 1:/# expr1; smt.
   rewrite /dbad H3 /= (_:_i+1-_i=1) 1:/# expr1; smt.
  seq 9: (b) 
         (mu1 dbad true) ((mu1 dbad true)^(n-(_i+1)))
         (mu1 dbad false) 0%r 
         (#[/2:9]pre /\ 0 <= i < n /\ i = _i + 1).
  - wp; sp; if => //; wp; rnd; wp; skip => /#.
  - wp; sp; if => //; wp; rnd; wp; skip; progress; smt.
  - conseq hrec => />; progress.
    + smt().
    + by hoare; rcondf 1; skip; smt().
    + move => /> *.
      by rewrite (_:n-_i=(n-(_i+1))+1) 1:/# exprS /#.
+ wp; sp; if => //; wp; rnd; wp; skip; smt(dbad_real_ll dbad_ideal_ll).
+ move => /> *.
  wp; sp; if => //; wp; rnd; wp; skip; smt(dbad_real_ll dbad_ideal_ll).
qed.

lemma pbad_iter_pr lor paux V' vaux w x n &m:
 0 <= n =>
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 Pr [ BadProcs.pbad_iter(paux,V',vaux,w,x,lor,n) @ &m : res ]
 = (mu1 (if lor
         then dbad_real paux V' vaux w x
         else dbad_ideal V' vaux x) true)^n.
proof.
move=> Hn V_ll.
have ->: Pr[BadProcs.pbad_iter(paux, V', vaux, w, x, lor, n) @ &m : res] 
         = Pr[BadProcs.dbad_iter(paux, V', vaux, w, x, lor, n) @ &m : res]
 by byequiv (bad_iter_eq n Hn).
by apply dbad_iter_pr.
qed.

lemma pbad_iter_ph lor paux V' vaux w x n &m:
 0 <= n =>
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 phoare [ BadProcs.pbad_iter
        : _paux=paux /\ _V=V' /\ _vaux=vaux /\ _w=w /\ _x=x
          /\ _lor=lor /\ _n=n ==> res
        ] = ((mu1 (if lor
                    then dbad_real paux V' vaux w x
                    else dbad_ideal V' vaux x) true)^n).
proof.
move=> npos V_ll.
pose dbad := if lor then dbad_real paux V' vaux w x else dbad_ideal V' vaux x.
bypr => /> &m' -> -> -> -> -> -> ->.
by apply pbad_iter_pr.
qed.

lemma realn_bad_pr (D <: DRoI_t{IPS,Hops}) V' w x &m:
 islossless D.rOi =>
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 Pr [ Hops(D).realn(0,V',w,x) @ &m : Hops.bad ] = (1%r - guess_pr)^Nsim.
proof.
have Nsim_pos D_ll V_ll := Nsim_pos.
have ->: Pr[Hops(D).realn(0, V', w, x) @ &m : Hops.bad]
         = Pr[BadProcs.pbad_iter(IPS.paux{m}, V', IPS.vaux{m}, w, x, true, Nsim) @ &m : res].
 byequiv (_: ={_V,_w,_x} /\ _l{1}=0 /\ _paux{2}=IPS.paux{1} /\ _vaux{2}=IPS.vaux{1} /\ _n{2}=Nsim /\ _lor{2} ==> Hops.bad{1}=res{2}) => //.
 proc; inline*; simplify.
 rcondf {1} 9; first by move=> *; wp; skip => /#.
 call{1} (_:true ==> true).
 while (={i,_V,_w,_x} /\ (Hops.bad,IPS.paux,IPS.vaux,Nsim){1}=(b,_paux,_vaux,_n){2} /\ _lor{2}).
  rcondt {2} 7; first by move=> *; wp; skip.
  by wp; do 3! rnd; wp; skip.
 by wp; skip.
move: (pbad_iter_pr true IPS.paux{m} V' IPS.vaux{m} w x Nsim &m _ _) => //; first smt().
move=> /= ->.
by rewrite (dbad_real_guess_pr _ _ _ _ _ &m).
qed.

(* Protocol data to be distinguished 
 We split the data in two components: one that is unconditionally indistinguishable
-- the bad event, and another that is is conditioned on the [!bad] event.  *)
type data_t = bool * view_t.

(* oracle given to the Distinguisher *)
module type Orcl_t = {
 proc get_data(): data_t
}.

(* the concrete oracle implementation that changes commitments *)
module ComChg = {
 var t: view_t
 var bad: bool
 proc init(_V: Verifier_t, _vaux: vauxdata_t, _paux: pauxdata_t,
           _w: witness_t, _x: statement_t, _lor: bool): unit = {
  var chl,com,pst,sst,chlv,vst,resp;
  if (_lor) { (* REAL transcript *)
   chl <$ rnd_challenge;
   (com,pst) <$ P.`commit _paux _w _x;
   (chlv,vst) <$ _V.`challenge _vaux _x com;
   resp <- (P.`response pst chlv).`1;
  } else { (* IDEAL transcript *)
   chl <$ rnd_challenge;
   (com,sst) <$ scommit _x chl;
   (chlv,vst) <$ _V.`challenge _vaux _x com;
   resp <- sresponse sst chlv;
  }
  bad <- !good_challenge chl chlv;
  if (!bad) {
   t <- (com,chlv,vst,resp);
  } else {
   t <- (witness,witness,witness,witness);
  }
 }
 proc get_data(): data_t = {
  return (bad,t);
}
}.


(* Distinguisher *)
module type Distinguisher_t(O: Orcl_t) = {
 proc lOr(_l: int, _V: Verifier_t, _vaux: vauxdata_t, _paux: pauxdata_t,
          _w: witness_t, _x: statement_t): bool
}.

module Distinguish(D: Distinguisher_t) = {
 proc game(_l: int, _V: Verifier_t, _vaux: vauxdata_t, _paux: pauxdata_t,
           _w: witness_t, _x: statement_t, _lor: bool): bool = {
  var b;
  ComChg.init(_V,_vaux,_paux,_w,_x,_lor);
  b <@ D(ComChg).lOr(_l,_V,_vaux,_paux,_w,_x);
  return b;
 }
}.


(*
   COMPUTATIONAL ASSUMPTION
   ========================
*)

op eps_sim: real.

axiom replace_commitments (D<:Distinguisher_t{ComChg}) V' vaux paux w x &m i:
 0 <= i < Nsim =>
 `| Pr [ Distinguish(D).game(i,V',vaux,paux,w,x,false) @ &m : res ]
    - Pr [ Distinguish(D).game(i,V',vaux,paux,w,x,true) @ &m : res ] |
 <= eps_sim.


(* We can always bound the [bad] event on the distinguisher... *)
module Adv_bad (D: Distinguisher_t) (O: Orcl_t) = {
proc lOr(_l: int, _V: Verifier_t, _vaux: vauxdata_t, _paux: pauxdata_t, _w: witness_t, _x: statement_t): bool = {
 var data, b;
 data <@ O.get_data();
 b <@ D(O).lOr(_l,_V,_vaux,_paux,_w,_x);
 return data.`1;
 }
}.

equiv Adv_bad_eq (D<:Distinguisher_t{ComChg}):
 Distinguish(D).game ~ Distinguish(Adv_bad(D)).game
 : ={_l,_V,_w,_x,_lor,_vaux,_paux,glob D} ==> ComChg.bad{1} = res{2}.
proof.
proc; inline Adv_bad(D, ComChg).lOr; wp.
wp; call (_: ={glob ComChg}); first by proc; skip; auto.
simplify.
call {2} (_: true ==> res=(ComChg.bad,ComChg.t)); first by proc.
by inline*; wp; sp; if => //;
 wp; do 3! rnd; skip => /> *.
qed.

lemma replace_commitments_bad (D<:Distinguisher_t{ComChg}) V' vaux paux w x &m i:
 0 <= i < Nsim =>
 `| Pr [ Distinguish(D).game(i,V',vaux,paux,w,x,false) @ &m : ComChg.bad ]
    - Pr [ Distinguish(D).game(i,V',vaux,paux,w,x,true) @ &m : ComChg.bad ] |
 <= eps_sim.
proof.
move => *.
have ->: Pr[Distinguish(D).game(i, V', vaux,paux,w, x, false) @ &m : ComChg.bad]
         = Pr[Distinguish(Adv_bad(D)).game(i, V', vaux,paux,w, x, false) @ &m : res]
 by byequiv (Adv_bad_eq D).
have ->: Pr[Distinguish(D).game(i, V', vaux,paux,w, x, true) @ &m : ComChg.bad]
         = Pr[Distinguish(Adv_bad(D)).game(i, V',vaux,paux, w, x, true) @ &m : res]
 by byequiv (Adv_bad_eq D).
by apply (replace_commitments (Adv_bad(D))).
qed.

lemma lOr_bad_pr (D <: Distinguisher_t{ComChg}) lor
                      l paux V' vaux w x &m:
 phoare [ D(ComChg).lOr : _V=V' /\ _l=l ==> true ] = 1%r =>
 0 <= l < Nsim =>
 Pr[Distinguish(D).game(l, V', vaux, paux, w, x, lor) @ &m : ComChg.bad]
 = mu1 (if lor then dbad_real paux V' vaux w x else dbad_ideal V' vaux x) true.
proof.
move=> D_ll Hl.
have ->: Pr[Distinguish(D).game(l, V', vaux,paux,w, x, lor) @ &m : ComChg.bad]
         = Pr[BadProcs.dbad_lor(paux,V',vaux,w, x,lor) @ &m : res].
 byequiv (_: ={_V,_w,_x,_lor,_vaux,_paux,glob D} /\ (_V,_l){1}=(V',l) ==> ComChg.bad{1} = res{2}) => //.
 proc; simplify.
 call {1} (_: _V=V' /\ _l=l ==> true).
 conseq (_: ={_V, _w, _x, _lor, _vaux, _paux, glob D} ==> ComChg.bad{1} = b{2}); first 2 smt().
 transitivity {2}
  { if (_lor) {
     b <@ BadProcs.pbad_real(_paux, _V, _vaux, _w, _x);
    } else {
     b <@ BadProcs.pbad_ideal(_V, _vaux, _x);
    }
  }
  ( ={_V, _w, _x, _lor, _vaux, _paux, glob D} ==> ComChg.bad{1} = b{2})
  ( ={_V, _w, _x, _lor, _vaux, _paux, glob D} ==> ={b}) => //.
   by move=> /> &2; exists (glob D){2} _V{2} _lor{2} _paux{2} _vaux{2} _w{2} _x{2}.
  by inline*; wp; sp; if => //; wp; do 3! rnd; wp; skip => /> /#.
 by if => //; [ call bad_real_eq | call bad_ideal_eq ].
byphoare (_:_paux=paux /\ _V=V' /\ _vaux=vaux /\ _w=w /\ _x=x /\ _lor=lor ==> _) => //.
proc; inline*; simplify.
if => //.
 wp; rnd; wp; skip => />; progress; smt.
wp; rnd; wp; skip => />; progress; smt.
qed.

lemma replace_commitments_dbad (D<:Distinguisher_t{ComChg}) V' vaux paux w x &m (l: int):
 0 <= l < Nsim =>
 phoare [ D(ComChg).lOr : _V=V' /\ _l=l ==> true ] = 1%r =>
 `| mu1 (dbad_ideal V' vaux x) true - mu1 (dbad_real paux V' vaux w x) true |
  <= eps_sim.
proof.
move=> Hl D_ll.
move: (replace_commitments_bad D V' vaux paux w x &m l Hl).
by rewrite (lOr_bad_pr D true) // (lOr_bad_pr D false).
qed.

(* 
   REDUCTION
*)

module AdvComChg (D : DRoI_t, O : Orcl_t) = {
 proc lOr(_l: int, _V: Verifier_t, _vaux: vauxdata_t, _paux: pauxdata_t,
          _w : witness_t, _x : statement_t): bool = {
  var bad, com, pst, sst, chl, chlv, vst, i, b, t;
  t <- witness;
  i <- 0;
  bad <- true;
  while (bad && i < _l) { 
   chl <$ rnd_challenge;
   (com, sst) <$ scommit _x chl;
   (chlv, vst) <$ _V.`challenge _vaux _x com;
   bad <- !good_challenge chl chlv;
   if (!bad) {
    t <- (com,chlv,vst,sresponse sst chlv);
   } else {
    t <- (witness,witness,witness,witness);
   }
   i <- i + 1; 
  }
  if (bad && i < _l+1) { 
   (bad,t) <@ O.get_data();
   i <- i + 1;
  }
  while (bad && i < Nsim) {
   chl <$ rnd_challenge;
   (com, pst) <$ P.`commit _paux _w _x;
   (chlv, vst) <$ _V.`challenge _vaux _x com;
   bad <- !good_challenge chl chlv;
   t <- (com, chlv,vst,(P.`response pst chlv).`1);
   i <- i + 1; 
  }
  Hops.bad <- bad;
  b <@ D.rOi(_V,_vaux, _x, t);
  return b /\ !Hops.bad;
 }
}.

module AUX (D : DRoI_t) = {
 (* auxiliary proc. specialized for the bad event *)
 proc lOr_dbad(_l: int, _V: Verifier_t, _vaux: vauxdata_t, _paux: pauxdata_t,
              _w : witness_t, _x : statement_t, _lor: bool): bool = {
  var bad, b, t;
  t <- witness;
  bad <@ BadProcs.pbad_iter(_paux,_V,_vaux,_w,_x,false,_l);
  if (bad)
   bad <@ BadProcs.pbad_lor(_paux,_V,_vaux,_w,_x,_lor);
  if (bad)
   bad <@ BadProcs.pbad_iter(_paux,_V,_vaux,_w,_x,true,Nsim-_l-1);
  Hops.bad <- bad;
  b <@ D.rOi(_V,_vaux, _x, t);
  return b;
 }
}.

lemma lOr_dbad_eq (D <: DRoI_t{Hops,ComChg,AdvComChg,IPS}) l V':
 islossless D.rOi =>
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 0 <= l < Nsim => 
 equiv [ Distinguish(AdvComChg(D)).game ~ AUX(D).lOr_dbad
       : ={_l,_paux,_V,_vaux,_w,_x,_lor,glob D} /\ (_l,_V){2}=(l,V')
       ==> ={Hops.bad} ].
proof.
move=> D_ll V_ll Hl.
have P_ll:= Pcommit_ll.
have S_ll:= scommit_ll.
proc; inline AdvComChg(D, ComChg).lOr.
swap {1} 1 10.
wp; call {1}(_: true ==> true); call {2}(_: true ==> true).
wp; simplify; sp 6 1.
seq 4 1: (#pre /\ ={bad} /\ 0 <= i{1} /\ (bad{1} => i{1} = _l0{1})).
 inline*; wp; sp 0 7.
 while (={i,_lor,_paux0,_V0,_vaux0,_w0,_x0} /\
        (false,bad,_l0){1}=(_lor0,b0,_n){2} /\ 0 <= i{2} <= _n{2}).
  sp; rcondf {2} 1; first by move=> *; skip.
  by wp; do 3! rnd; wp; skip => /#.
 by wp; skip => /#.
seq 2 1: (#[:-1]pre /\ (bad => i=_l0+1){1}).
 case (bad{1}); last first.
  rcondf {1} 2.
   by move=> *; inline*; sp; if; wp; do 3! rnd; skip => /#.
  rcondf {2} 1; first by move=> *; skip.
  by inline*; sp; if {1}; wp; do 3! rnd{1}; skip => /> /#.
 rcondt {2} 1; first by auto.
 by inline*; sp; if => //; wp; do 3! rnd; wp; skip => /> /#.
case (bad{1}); last first.
 rcondf {1} 1; first by move=> *; skip => /#.
 rcondf {2} 1; first by move=> *; skip.
 by skip.
inline*; rcondt {2} 1; first by auto.
wp; while (={_paux0,_V0,_vaux0,_w0,_x0,_l} /\
           (true,_l0,_l,i-_l-1,bad,Nsim-_l0-1){1}=(_lor0,l,l,i,b0,_n){2} /\ 0 <= i{2} <= _n{2} /\ (bad => i<=Nsim){1}).
 sp; rcondt {2} 1; first by move=> *; skip.
 by wp; do 3! rnd; wp; skip => /> /#.
by wp; skip => /> /#.
qed.

lemma rOi_dbad_ph (D <: DRoI_t{Hops,ComChg,AdvComChg,IPS})
                  paux V' vaux w x l lor:
 islossless D.rOi =>
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 0 <= l < Nsim => 
 phoare [ Distinguish(AdvComChg(D)).game 
        : _l=l /\ _paux=paux /\ _V=V' /\ _vaux=vaux /\ _w=w /\ _x=x /\ _lor=lor
        ==> Hops.bad
        ] = ((mu1 (dbad_ideal V' vaux x) true)^l
   * (mu1 (dbad_real paux V' vaux w x) true)^(Nsim-l-1)
   * mu1 (if lor then dbad_real paux V' vaux w x else dbad_ideal V' vaux x) true).
proof.
move=> D_ll V_ll Hl.
bypr => &m' [->[->[->[->[->[-> ->]]]]]].
have ->: 
 Pr[Distinguish(AdvComChg(D)).game(l, V', vaux, paux, w, x, lor) @ &m' : Hops.bad]
 = Pr[AUX(D).lOr_dbad(l, V', vaux, paux, w, x, lor) @ &m': Hops.bad].
 by byequiv (lOr_dbad_eq D l V' _ _ _).
byphoare (_:_l=l /\ _paux=paux /\ _V=V' /\ _vaux=vaux /\ _w=w /\ _x=x /\ _lor=lor
        ==> Hops.bad).
proc; simplify.
seq 2: (bad)
 (mu1 (dbad_ideal V' vaux x) true ^ l)
 (mu1 (dbad_real paux V' vaux w x) true ^ (Nsim - l - 1) *
  mu1 (if lor then dbad_real paux V' vaux w x else dbad_ideal V' vaux x) true)
 _ 0%r
 (#pre).
+ inline*; wp; while (#pre).
   by sp; if => //; wp; do 3! rnd; wp; skip.
  by wp; skip.
+ call (pbad_iter_ph false paux V' vaux w x l &m' _ _).
   by smt(). 
  by wp; skip; smt().
+ rcondt 1; first by auto.
  seq 1: (bad)
   (mu1 (if lor then dbad_real paux V' vaux w x else dbad_ideal V' vaux x) true)
   (mu1 (dbad_real paux V' vaux w x) true ^ (Nsim - l - 1))
   _ 0%r
   (#[:-1]pre).
  - by inline*; sp; if => //; wp; do 3! rnd; wp; skip.
  - by call (bad_lor_pr paux V' vaux w x lor).
  - rcondt 1; first by auto.
    seq 1: (bad)
     (mu1 (dbad_real paux V' vaux w x) true ^ (Nsim - l - 1)) 1%r
     _ 0%r
     (#[:-1]pre).
    * inline*; wp; while (#pre).
       by sp; if => //; wp; do 3! rnd; wp; skip.
      by wp; skip.
    * call (pbad_iter_ph true paux V' vaux w x (Nsim - l - 1) &m' _ _).
       by smt().
      by skip => /#.
    * by call (_: true ==> true); wp; skip.
    * hoare; call (_: true ==> true); first done.
      by wp; skip.
    * by move=> * /#.
  - hoare; rcondf 1; first by auto.
    call (_: true ==> true); first done.
    by wp; skip.
  - by move=> * /#.
+ hoare; do 2! (rcondf 1; first by auto).
  call (_: true ==> true); first done.
  by wp; skip.
  by move=> /> /#. 
+ by smt(). 
done.
qed.

import StdOrder.RealOrder.

lemma rOi_bad_pr (D <: DRoI_t{Hops,ComChg,AdvComChg,IPS})
                 l paux V' vaux w x &m:
 islossless D.rOi =>
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 0 <= l < Nsim =>
 `|Pr[Distinguish(AdvComChg(D)).game(l, V', vaux, paux, w, x, false) @ &m : Hops.bad] -
   Pr[Distinguish(AdvComChg(D)).game(l, V', vaux, paux, w, x, true) @ &m : Hops.bad]|
 <= eps_sim.
proof.
move=> D_ll V_ll Hl.
apply (ler_trans `|mu1 (dbad_ideal V' vaux x) true - mu1 (dbad_real paux V' vaux w x) true|); last first.
 apply (replace_commitments_dbad (AdvComChg(D)) _ _ _ _ _ &m l) => //.
 proc; call (_:true); wp; while (_V=V') (Nsim-i).
  move=> *; wp; do 3! rnd predT; skip; smt(rnd_challenge_ll Pcommit_ll).
 seq 4: (#post).
 + while (_l=l /\ _V=V' /\ 0 <= i <= _l).
    by wp; do 3! rnd; skip => /> /#.
   by wp; skip => /#.
 + sp; while (_l=l /\ _V=V' /\ 0 <= i <= _l) (_l-i) _l 1%r; first 3 by move=> /> /#.
   + move=> hrec.
     seq 6: (_l = l /\ _V = V' /\ 0 <= i<=_l).
     + by wp; do 3! rnd; skip => /> /#.
     + by wp; do 3! rnd predT; skip => />; smt(Pcommit_ll scommit_ll rnd_challenge_ll).
     + case: (bad && i < _l); first by conseq hrec.
       by rcondf 1; skip => /#.
     + by hoare; wp; do 3! rnd; skip => /> /#.
     + done.
     wp; do 3! rnd predT; skip => />; smt(Pcommit_ll scommit_ll rnd_challenge_ll).
   + move=> /> *.
     wp; do 3! rnd predT; skip => />; smt(Pcommit_ll scommit_ll rnd_challenge_ll).
 + if => //.
   wp; call (_:true ==> true); first by proc; auto.
   by skip.
 + hoare.
   while (_l=l /\ _V=V' /\ 0 <= i <= _l).
    by wp; do 3! rnd; skip => /#.
   by wp; skip => /> /#.
 + by move=> * /#.
have ->: Pr[Distinguish(AdvComChg(D)).game(l, V', vaux, paux, w, x, false) @ &m : Hops.bad]
 = (mu1 (dbad_ideal V' vaux x) true)^l
   * (mu1 (dbad_real paux V' vaux w x) true)^(Nsim-l-1)
   * mu1 (dbad_ideal V' vaux x) true.
 byphoare (rOi_dbad_ph D paux V' vaux w x l false _ _ _) => //.
have ->: Pr[Distinguish(AdvComChg(D)).game(l, V', vaux, paux, w, x, true) @ &m : Hops.bad]
 = (mu1 (dbad_ideal V' vaux x) true)^l
   * (mu1 (dbad_real paux V' vaux w x) true)^(Nsim-l-1)
   * mu1 (dbad_real paux V' vaux w x) true.
 byphoare (rOi_dbad_ph D paux V' vaux w x l true _ _ _) => //.
rewrite -Domain.mulrBr normrM mulrC.
apply ler_pimulr; first smt().
rewrite ger0_norm; smt(mu_bounded exprn_ile1 expr_ge0).
qed.

import StdBigop.Bigreal.

lemma all_hybrids (D <: DRoI_t{IPS,Hops,ComChg,AdvComChg})
                  (p: bool -> bool -> bool) V' w x &m eps:
 (forall i, 0 <= i < Nsim =>
   `| Pr [ Hops(D).realn(i+1,V',w,x) @ &m : p Hops.bad res ]
      - Pr [ Hops(D).realn(i,V',w,x) @ &m : p Hops.bad res ] | <= eps) =>
 `| Pr [ Hops(D).realn(Nsim,V',w,x) @ &m : p Hops.bad res ]
    - Pr [ Hops(D).realn(0,V',w,x) @ &m : p Hops.bad res ] | <= Nsim%r * eps.
proof.
have Nsim_pos := Nsim_pos.
move=> Hstep.

pose X:= Real.(-) _ _.
have Xeq: X = BRA.big predT
               (fun i => Pr [ Hops(D).realn(i+1,V',w,x) @ &m : p Hops.bad res ]
                         - Pr [ Hops(D).realn(i,V',w,x) @ &m : p Hops.bad res ])
               (iota_ 0 Nsim).
 rewrite -BRA.sumrB (_:Nsim=Nsim-1+1) 1:/# {1}iota_add // 1:/# iota1.
 rewrite BRA.big_cat BRA.big_seq1 iotaS 1:/# BRA.big_cons {-1}/predT /=.
 by rewrite {-1}(_:1=1+0) 1:/# iota_addl /= BRA.big_map /(\o) /#.
have Xler: `|X| <= BRA.big predT
                    (fun i => `| Pr [ Hops(D).realn(i+1,V',w,x) @ &m : p Hops.bad res ]
                                - Pr [ Hops(D).realn(i,V',w,x) @ &m : p Hops.bad res ]|)
                    (iota_ 0 Nsim).
 by rewrite Xeq; apply big_normr.
have ->: Nsim%r * eps = BRA.big predT  (fun x => eps) (iota_ 0 Nsim).
 rewrite BRA.big_const count_predT_eq // size_iota /max Nsim_pos /=.
 rewrite -AddMonoid.iteropE -intmulpE /=; first by smt().
 by rewrite -mulr_intr mulrC ofintR.
apply (StdOrder.RealOrder.ler_trans _ _ _ Xler).
apply (ler_sum_seq) => i /mem_iota Hi _; apply Hstep; smt().
qed.

lemma realnL (D <: DRoI_t{IPS,ComChg,AdvComChg}) V' l:
  islossless D.rOi =>
  (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
  0 <= l < Nsim =>
  equiv [ Hops(D).realn ~ Distinguish(AdvComChg(D)).game
        : ={_l,_V,_w,_x,glob D}
          /\ (_l,_V,IPS.paux,IPS.vaux,true){1}=(l,V',_paux,_vaux,_lor){2} 
       ==> ={Hops.bad} /\ (!Hops.bad{1} => ={res})
        ].
proof.
move=> D_rOi_ll V_ll l_pos; proc; simplify.
inline AdvComChg(D,ComChg).lOr.
wp; call (_: ={glob D,_V,_vaux,_x,Hops.bad} /\ (!Hops.bad{2} => ={_t}) ==> ={Hops.bad} /\ (!Hops.bad{2} => ={res})).
 proc*; simplify.
 case: (Hops.bad{2}).
  call{1} D_rOi_ll.
  call{2} D_rOi_ll.
  by skip => /> *; progress.
 call (_:true).
 by skip => />.
unroll {1} 10.
swap {2} 1 10.
wp; while (={i,glob D} /\ (!bad{2} => ={t}) /\
       (_V,_w,_x,Hops.bad,IPS.paux,IPS.vaux,IPS.paux,IPS.vaux){1}=(_V0,_w0,_x0,bad,_paux,_vaux,_paux0,_vaux0){2} /\ (0 <= i <= Nsim){2}).
 by wp; do 3! rnd; skip => /#.
seq 9 10: (={i,glob D} /\ (!bad{2} => ={t}) /\
           (_V,_w,_x,_l,_l,IPS.paux,IPS.vaux,IPS.paux,IPS.vaux,_w,_x,_V,V',Hops.bad){1}
           =(_V0,_w0,_x0,_l0,l,_paux,_vaux,_paux0,_vaux0,_w,_x,_V,_V,bad){2} /\
           (0 <= i <= _l0 /\ _lor){2}).
 inline*.
 while (#post).
  by wp; do 3! rnd; skip => /> /#.
 by wp; skip => /#.
inline*; simplify.
rcondt {2} 7; first by move=>*; wp; skip; auto.
case: (Hops.bad{1}).
 rcondt {1} 1; first by move=> *; skip => /#.
 by wp; do 3! rnd; wp; skip => /> /#.
rcondf {1} 1; first by move=> *; skip => /#.
have ?:= Pcommit_ll.
by wp; do 3! rnd {2}; wp; skip => /> /#.
qed.

lemma realnR (D <: DRoI_t{IPS,ComChg,AdvComChg}) l V':
  islossless D.rOi =>
  (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
  0 <= l < Nsim =>
  equiv [ Hops(D).realn ~ Distinguish(AdvComChg(D)).game 
        : ={_V,_w,_x,glob D}
          /\ (_l,l,_V,IPS.paux,IPS.vaux,false){1}=(l+1,_l,V',_paux,_vaux,_lor){2} 
       ==> ={Hops.bad} /\ (!Hops.bad{1} => ={res})
        ].
proof.
move=> D_rOi_ll V_ll l_pos; proc.
inline AdvComChg(D, ComChg).lOr.
wp; call (_: ={glob D,Hops.bad,_V,_vaux,_x} /\ (!Hops.bad{2} => ={_t}) ==> ={Hops.bad} /\ (!Hops.bad{2} => ={res})).
 proc*; simplify.
 case: (Hops.bad{2}).
  call{1} D_rOi_ll.
  call{2} D_rOi_ll.
  by skip => /> *.
 call (_:true).
 by skip => /> *.
wp; while (={i,glob D} /\ (!bad{2} => ={t}) /\
           (_V,IPS.paux,IPS.vaux,_w,_x,Hops.bad){1}=(_V0,_paux0,_vaux0,_w0,_x0,bad){2} /\ (0 <= i <= Nsim){2}).
 by wp; do 3! rnd; skip => /> /#.
splitwhile {1} 9: (i<l); simplify.
swap {2} 1 10.
seq 9 10: (={i,_V,_w,_x,glob D} /\ (!bad{2} => ={t}) /\
           (IPS.paux,IPS.vaux,_V,V',IPS.paux,IPS.vaux,_w,_x,Hops.bad,_l,l){1}
           =(_paux,_vaux,_V0,_V0,_paux0,_vaux0,_w0,_x0,bad,l+1,_l0){2} /\
           (0 <= i{2} <= l /\ !_lor{2} /\ (!bad \/ i=l){2})).
 while (#[/:-1]post).
  by wp; do 3! rnd; skip => /#.
 by wp; skip => /> /#.
case: (Hops.bad{1}).
 rcondt {1} 1; first by move=> *; skip => /#.
 rcondf {1} 7; first by move=> &m'; wp; do 3! rnd; skip => /> /#.
 rcondt {2} 2.
  by move=> &m; inline*; wp; sp; if; wp; do 3! rnd; skip => /#.
 inline*.
 rcondf {2} 7; first by move=> *; wp; skip.
 by wp; do 3! rnd; wp; skip => /> /#.
rcondf {1} 1; first by move=> *; skip => /#.
rcondf {2} 2.
 by move=> *; inline*; sp; if; wp; do 3! rnd; skip => /> /#.
inline*; sp; if {2}; wp; do 3! rnd{2}; skip => />; smt(scommit_ll). 
qed.

lemma hybrid_bad (D <: DRoI_t{Hops,ComChg,AdvComChg,IPS})
                 V' w x &m i:
 islossless D.rOi =>
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 0 <= i < Nsim =>
 `| Pr [ Hops(D).realn(i+1,V',w,x) @ &m : Hops.bad ]
    - Pr [ Hops(D).realn(i,V',w,x) @ &m : Hops.bad ] | <= eps_sim.
proof.
move=> D_rOi_ll V_ll.
have Nsim_pos := Nsim_pos; move=> Irng.
have ->: Pr[ Hops(D).realn(i + 1, V', w, x) @ &m : Hops.bad]
  = Pr[ Distinguish(AdvComChg(D)).game(i,V',IPS.vaux{m},IPS.paux{m},w,x,false) @ &m: Hops.bad ]
 by byequiv (realnR D _ _ _ V_ll Irng).
have ->: Pr[Hops(D).realn(i, V', w, x) @ &m : Hops.bad]
 = Pr[ Distinguish(AdvComChg(D)).game(i,V',IPS.vaux{m},IPS.paux{m},w,x,true) @ &m: Hops.bad ]
 by byequiv (realnL D _ _ _ V_ll Irng).
by apply (rOi_bad_pr D).
qed.

lemma realn'_bad_pr (D <: DRoI_t{IPS,Hops,ComChg}) V' w x &m:
 islossless D.rOi =>
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 Pr [ Hops(D).realn(Nsim,V',w,x) @ &m : Hops.bad ]
 <= (1%r - guess_pr)^Nsim + Nsim%r * eps_sim.
proof.
move=> D_ll V_ll.
have dist_pr: `| Pr [ Hops(D).realn(Nsim,V',w,x) @ &m : Hops.bad ]
                 - Pr [ Hops(D).realn(0,V',w,x) @ &m : Hops.bad ] |
               <= Nsim%r * eps_sim.
 move: (all_hybrids D (fun x y=>x) V' w x &m eps_sim) => /= HH.
 apply HH => i Hi.
 have ->: Pr[ Hops(D).realn(i + 1, V', w, x) @ &m : Hops.bad]
   = Pr[ Distinguish(AdvComChg(D)).game(i,V',IPS.vaux{m},IPS.paux{m},w,x,false) @ &m: Hops.bad]
  by byequiv (realnR D _ V' _ _ Hi).
 have ->: Pr[Hops(D).realn(i, V', w, x) @ &m : Hops.bad]
   = Pr[ Distinguish(AdvComChg(D)).game(i,V',IPS.vaux{m},IPS.paux{m},w,x,true) @ &m: Hops.bad ]
  by byequiv (realnL D _ _ _ V_ll Hi).
 by apply (rOi_bad_pr D).
have bad_pr := realn_bad_pr D V' w x &m.
smt().
qed.

lemma hop2_Nbad (D <: DRoI_t{IPS,Hops,ComChg}) V' w x &m:
 islossless D.rOi =>
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 `| Pr [ Hops(D).realn(Nsim,V',w,x) @ &m : res /\ !Hops.bad ]
    - Pr [ Hops(D).realn(0,V',w,x) @ &m : res /\ !Hops.bad ] |
 <= Nsim%r * eps_sim.
proof.
move=> D_ll V_ll.
apply (all_hybrids D (fun x y=> y /\ !x) V' w x &m eps_sim) => i Hi /=.
have ->: Pr[ Hops(D).realn(i + 1, V', w, x) @ &m : res /\ !Hops.bad]
  = Pr[ Distinguish(AdvComChg(D)).game(i,V',IPS.vaux{m},IPS.paux{m},w,x,false) @ &m: res /\ !Hops.bad].
  by byequiv (realnR D _ V' _ _ Hi) => // /#.
have <-: Pr[ Distinguish(AdvComChg(D)).game(i,V',IPS.vaux{m},IPS.paux{m},w,x,false) @ &m: res ]
 = Pr[ Distinguish(AdvComChg(D)).game(i,V',IPS.vaux{m},IPS.paux{m},w,x,false) @ &m: res /\ !Hops.bad].
 byequiv => //.
 proc; inline AdvComChg(D, ComChg).lOr.
 wp; conseq (_: _ ==> ={b0, Hops.bad}) => //.
 by sim.
have ->: Pr[Hops(D).realn(i, V', w, x) @ &m : res /\ !Hops.bad]
   = Pr[ Distinguish(AdvComChg(D)).game(i,V',IPS.vaux{m},IPS.paux{m},w,x,true) @ &m: res /\ !Hops.bad]
  by byequiv (realnL D _ _ _ V_ll Hi) => // /#.
have <-: Pr[ Distinguish(AdvComChg(D)).game(i,V',IPS.vaux{m},IPS.paux{m},w,x,true) @ &m: res ]
 = Pr[ Distinguish(AdvComChg(D)).game(i,V',IPS.vaux{m},IPS.paux{m},w,x,true) @ &m: res /\ !Hops.bad].
 byequiv => //.
 proc; inline AdvComChg(D, ComChg).lOr.
 wp; conseq (_: _ ==> ={b0, Hops.bad}) => //.
 by sim.
by apply (replace_commitments (AdvComChg(D))).
qed.

lemma hop2 (D <: DRoI_t{IPS,Hops,ComChg}) V' w x &m:
 islossless D.rOi =>
 (forall (vaux : vauxdata_t) (x0 : statement_t) (com : commitment_t), is_lossless (V'.`challenge vaux x0 com)) =>
 `| Pr [ Hops(D).realn(0,V',w,x) @ &m : res ]
    - Pr [ Hops(D).realn(Nsim,V',w,x) @ &m : res ] |
 <= (1%r - guess_pr)^Nsim + Nsim%r * 2%r * eps_sim.
proof.
move=> D_ll V_ll.
rewrite Pr [mu_split Hops.bad] StdOrder.RealOrder.distrC Pr [mu_split Hops.bad].
have hop2_Nbad := hop2_Nbad D V' w x &m D_ll V_ll.
have X: 
  `| Pr [ Hops(D).realn(0,V',w,x) @ &m : res /\ Hops.bad ]
    - Pr [ Hops(D).realn(Nsim,V',w,x) @ &m : res /\ Hops.bad ] |
 <= (1%r - guess_pr)^Nsim + Nsim%r * eps_sim.
 have X1: Pr [ Hops(D).realn(0,V',w,x) @ &m : res /\ Hops.bad ]
          <= Pr [ Hops(D).realn(0,V',w,x) @ &m : Hops.bad ]
  by rewrite Pr [mu_sub].
 have X2: Pr [ Hops(D).realn(Nsim,V',w,x) @ &m : res /\ Hops.bad ]
          <= Pr [ Hops(D).realn(Nsim,V',w,x) @ &m : Hops.bad ]
  by rewrite Pr [mu_sub].
 have realn_bad_pr := realn_bad_pr D V' w x &m D_ll V_ll.
 have realn'_bad_pr := realn'_bad_pr D V' w x &m D_ll V_ll.
 smt.
smt().
qed.


(* Final ZK property *)

lemma realn_ideal_eq (D <: DRoI_t{IPS,Hops,ComChg}) V' w x &m:
 Pr [ Hops(D).realn(Nsim,V',w,x) @ &m : res ]
 = Pr [ ZK(D).game(V',w,x,false) @ &m : res ].
proof.
byequiv => //; simplify; proc; inline*.
rcondf {2} 2; first by move=> *; wp.
rcondf {1} 10.
 move=> *; while (_l=Nsim /\ 0 <= i <= Nsim); first by wp; do 3! rnd; skip => /> /#.
 by wp; skip => />; smt(Nsim_pos).
call (_: true); wp; simplify.
while (={i, glob D} /\ 0 <= i{2} <= Nsim /\
       (_l,Hops.bad,t,_x,_V,IPS.vaux){1} = (Nsim,bad,t0,_x1,_V1,_vaux){2} /\
       (bad{2} => t0{2}=(witness,witness,witness,witness))).
 by wp; do 3! rnd; skip => /> /#.
wp; skip => />; smt(Nsim_pos).
qed.

(* Final thm.: overal, we get the following bound
    | Pr[real] - Pr[ideal] | < eps_fail^N + N*(2*eps_com+eps_mpc) *)

lemma zk (D <: DRoI_t{IPS,Hops,ComChg}) V' w x &m:
 islossless D.rOi =>
 (forall vaux x com, is_lossless (V'.`challenge vaux x com)) =>
 R w x =>
 `| Pr [ ZK(D).game(V',w,x,true) @ &m : res ]
    - Pr [ ZK(D).game(V',w,x,false) @ &m : res ] |
 <= (1%r-guess_pr)^Nsim + Nsim%r*(2%r*eps_sim).
proof.
move=> D_ll V_ll inR.
have -> := hop1 D V' w x &m V_ll.
rewrite -(realn_ideal_eq D V' w x &m).
have ? := hop2 D V' w x &m D_ll V_ll.
smt().
qed.


(* end section ZK1.*)


end ZKprot.
