(**
  First optimization step: reducing extra circuit iterations (**LPZKFaster**). 

  Before extracting OCaml code from our EasyCrypt formalization, we perform a preliminary 
  optimization step that reduces extra circuit iterations made both by the verifier. Following 
  the definition depicted in the *LPZK.ec* file, one can observe that the verifier iterates over 
  the circuit to check that the commitment message is consistent with the circuit and then 
  performs another circuit iteration to generate [f]. Naturally, this party can condense the two 
  circuit iterations into a single one, where [gen_f] now checks the consistency of the 
  commitment while generating [f] at the same time.

  Technically, we will be re-using all types and operators from *LPZK.ec*, except for the [gen_f]
  operation, which we formalize to check the consistency of the commitment message at the same
  time it computes [f]. At the end, the new [gen_f] function will output two values: a boolean -
  indicating if the commitment message is valid - and the [f] data structure - which will only be
  well-formed if the commitment message is valid. We will then show that:
    - if the commitment message is valid, the boolean output of the new [gen_f] function will 
      always be true
    - if the commitment message is valid, both [gen_f] from *LPZK.ec* and the [gen_f] formalized
      here will produce the same [f] data structure
  Armed with these two results, we can prove that the [prove] function has the same observable
  behavior as the one of *LPZK.ec* and, therefore, that the two protocols are equivalent.

  Completeness, soundness and zero knowledge for this new version of LPZK were derived by proving
  that both the original and new versions have the same observable behavior. Informally, we prove
  that both the new prove operator will produce the same decision as the reference one on all 
  possible inputs. This allowed us to prove that: 
    i. the completeness game of the new LPZK version has the same probability of the completeness
       game of the reference LPZK version; 
    ii. the soundness game of the new LPZK version has the same probability of the soundness game
        of the reference LPZK version; and 
    iii. that the real zero knowledge game of the new LPZK version is indistinguishable from the 
         real game of the reference LPZK version and, therefore, the same simulator can be used 
         to prove zero knowledge.
*)
require import Int Real List Distr.

from DVNIZK require import ADVNIZKPProtocol.
from DVNIZK require import Completeness Soundness ZeroKnowledge.
from Zarith require import PrimeField.

from LPZK require import LPZK.

import LPZK.
import ArithmeticCircuit.
import Circuit.

theory LPZKFaster.

  (** The witness is the same as in **LPZK** *)
  type witness_t = LPZK.witness_t.
  (** The instance is the same as in **LPZK** *)
  type instance_t = LPZK.instance_t.
  (** The statement is the same as in **LPZK** *)
  type statement_t = LPZK.statement_t.

  (** The relation is the same as in **LPZK** *)
  op relation (w : witness_t) (x : statement_t) : bool = LPZK.relation w x.

  (** The prover input is the same as in **LPZK** *)
  type prover_input_t = LPZK.prover_input_t.
  (** The verifier input is the same as in **LPZK** *)
  type verifier_input_t = LPZK.verifier_input_t.
  (** Inputs are considered valid the same way as in **LPZK** *)
  op valid_inputs (x : prover_input_t * verifier_input_t) : bool = LPZK.valid_inputs x.

  (** The prover randomness is the same as in **LPZK** *)
  type prover_rand_t = LPZK.prover_rand_t.

  (** Prover randomness is considered valid the same way as in **LPZK** *)
  op valid_rand_prover (r : prover_rand_t) (x : prover_input_t) : bool = 
    LPZK.valid_rand_prover r x.

  (** The verifier randomness is the same as in **LPZK** *)
  type verifier_rand_t = verifier_rand_t.

  (** Verifier randomness is considered valid the same way as in **LPZK** *)
  op valid_rand_verifier (rp : prover_rand_t) (rv : verifier_rand_t) (x : verifier_input_t) : 
    bool = LPZK.valid_rand_verifier rp rv x.

  (** The prover output is the same as in **LPZK** *)
  type prover_output_t = LPZK.prover_output_t. 
  (** The verifier output is the same as in **LPZK** *)
  type verifier_output_t = LPZK.verifier_output_t. 

  (** The commitment is the same as in **LPZK** *)
  type commitment_t = LPZK.commitment_t.

  (** The prover commits to a statement and witness the same as in **LPZK** *)
  op commit (r : prover_rand_t) (x : prover_input_t) = LPZK.commit r x.

  (** The [f] data structure is the same as in **LPZK** *)
  type f_t = LPZK.f_t.

  (** We define a *bad* [f] value to cover the case where the message integrity check fails *)
  op bad : f_t = PInputF ({| e = fzero |}).

  (** Improved [gen_f] operator, that performs a single circuit iteration computing [f] and
      attesting the circuit integrity at the same time. It will output a pair [bool * f_t] where
      the first element determines if the commitment message is valid and the second element if
      the [f] structure constructed by the verifier from the commitment message.

      If the commitment message validity check fails, then [gen_f] will output the [bad] 
      [f] defined above. If the message is valid, it will output an [f] in accordance with
      the commitment message *)
  op gen_f (r : verifier_rand_t) (gg : gates_t) (z : z_t) =
    with z = PInputZ wid zi => 
      if is_pinput gg then
        if as_pinput gg = wid then
          let m = zi.`m in
          let v = (nth def_yi r.`y wid).`v in
          (true, PInputF {| e = fadd v m |})
        else (false, bad)
      else (false, bad)

    with z = SInputZ wid zi => 
      if is_sinput gg then
        if as_sinput gg = wid then
          let m = zi.`m in
          let v = (nth def_yi r.`y wid).`v in
          (true, SInputF {| e = fadd v m |})
        else (false, bad)
      else (false, bad)

    with z = ConstantZ gid zi =>
      if is_constant gg then
        if (as_constant gg).`1 = gid then
          let m = zi.`m in
          let v = (nth def_yi r.`y gid).`v in
          (true, ConstantF {| e = fadd v m |})
        else (false, bad)
      else (false, bad)

    with z = AdditionZ gid zi zl zr =>
      if is_addition gg then
        let (gid', wl, wr) = as_addition gg in

        if gid = gid' then
          let (bl, fl) = gen_f r wl zl in
          let (br, fr) = gen_f r wr zr in
          if (bl /\ br) then
            (true, AdditionF {| e = fadd (get_e fl) (get_e fr) |} fl fr)
          else (false, bad)
        else (false, bad)
      else (false, bad)

    with z = MultiplicationZ gid zi zl zr =>
      if is_multiplication gg then
        let (gid', wl, wr) = as_multiplication gg in

        if gid = gid' then
          let (bl, fl) = gen_f r wl zl in
          let (br, fr) = gen_f r wr zr in

          let m = zi.`m in

          let alpha = r.`alpha in
          let y = nth def_yi r.`y gid in
          let v = y.`v in

          let el = get_e fl in
          let er = get_e fr in
  
          let e = fadd v m in

          if (bl /\ br) then
            (true, MultiplicationF {| e = e |} fl fr)
          else (false, bad)
        else (false, bad)
      else (false, bad).

  (** New [prove] function, equal to the [prove] function specified in *LPZK.ec*, but invokes
      the newly defined [gen_f] operator *)
  op prove (r : verifier_rand_t) (x : verifier_input_t) (c : commitment_t) : bool =
    let (z, z') = c in
    let (circ, inst) = x in
    let topo = circ.`topo in
    let gg = circ.`gates in
    let (b, f) = gen_f r ((add_final_mul circ).`gates) z in
    let n = z' in
    if (n <> fzero /\ b) then 
        get_e f = fmul n r.`alpha
    else false.

  (** The trace is the same as in **LPZK** *)
  type trace_t = LPZK.trace_t.

  (** New [protocol] function, equal to the [protocol] function specified in *LPZK.ec*, but 
      invokes the newly defined [prove] operator *)
  op protocol (r : prover_rand_t * verifier_rand_t) 
              (x : prover_input_t * verifier_input_t) : 
              trace_t * (prover_output_t * verifier_output_t) = 
    let (r_p, r_v) = r in let (x_p, x_v) = x in
    let c = commit r_p x_p in
    let b = prove r_v x_v c in (c, ((),b)).

  (** Proves that the operator that checks the validity of the commitment message specified in
      *LPZK.ec* is equivalent to the boolean output of the [gen_f] operator *)
  lemma z_validity_equivalence (rp : prover_rand_t) (rv : verifier_rand_t) gg z :
    valid_z_gates z gg <=>
    (LPZKFaster.gen_f rv gg z).`1.
  proof. by elim: z gg => //= /#. qed.

  (** Proves that the [prove] operator of *LPZK.ec* is equivalent to the optimized [prove] 
      operator defined here *)
  lemma prove_equivalence (rp : prover_rand_t) (rv : verifier_rand_t) topo gg ys c inst :
    LPZK.prove rv (({| topo = topo ; gates = gg ; out_wires = ys |}, inst)) c = 
    prove rv ({| topo = topo ; gates = gg ; out_wires = ys |}, inst) c.
  proof.
    rewrite /prove; elim c => z n /=; rewrite /valid_z.
    case (valid_z_gates z ((add_final_mul {| topo = topo ; gates = gg ; out_wires = ys |}))%LPZK.`gates); last first; progress.
      have : (LPZKFaster.gen_f rv ((add_final_mul {| topo = topo ; gates = gg ; out_wires = ys |})).`gates z).`1 = false by smt(z_validity_equivalence).
      by smt().
    have : (LPZKFaster.gen_f rv ((add_final_mul {| topo = topo ; gates = gg ; out_wires = ys |})).`gates z).`1 by smt(z_validity_equivalence).
    progress.
    have : exists b f, (b,f) = gen_f rv (add_final_mul {| topo = topo ; gates = gg ; out_wires = ys |}).`gates z by exists (gen_f rv (add_final_mul {| topo = topo ; gates = gg ; out_wires = ys |}).`gates z).`1 (gen_f rv (add_final_mul {| topo = topo ; gates = gg ; out_wires = ys |}).`gates z).`2 => /#.
    progress.
    rewrite -H1 /=.
    have ->: b = (gen_f rv (add_final_mul {| topo = topo ; gates = gg ; out_wires = ys |}).`gates z).`1 by smt().
    have ->: f = (gen_f rv (add_final_mul {| topo = topo ; gates = gg ; out_wires = ys |}).`gates z).`2 by smt().
    progress.
    case (n <> fzero); progress.
    rewrite /get_e /= H0 /=; congr.
    clear H1; move : H H0.
    rewrite /add_final_mul /=; elim z => //=.
      move => gid zi zl zr /=; progress.
    have : exists (bl, fl), (bl, fl) = gen_f rv (Constant (topo.`npinputs + topo.`nsinputs + topo.`ngates) fone) zl
      by clear H4;
      exists (gen_f rv (Constant (topo.`npinputs + topo.`nsinputs + topo.`ngates) fone) zl).`1 (gen_f rv (Constant (topo.`npinputs + topo.`nsinputs + topo.`ngates) fone) zl).`2 => /#.
    progress.
    move : H4; rewrite -H5 /=; progress.
    have : exists (br, fr), (br, fr) = gen_f rv gg zr by clear H4; exists (gen_f rv gg zr).`1 (gen_f rv gg zr).`2 => /#.
    progress.
    move : H4; rewrite -H6 /=; progress; move : H4.
    have ->: bl = (gen_f rv (Constant (topo.`npinputs + topo.`nsinputs + topo.`ngates) fone) zl).`1 by smt().
    have ->: br = (gen_f rv gg zr).`1 by smt().
    case ((gen_f rv (Constant (topo.`npinputs + topo.`nsinputs + topo.`ngates) fone) zl).`1); last first; progress. 
    move : H7.
    by case ((gen_f rv gg zr).`1).
  qed.

  (** Proves that the LPZK formalization in file *LPZK.ec* is equivalent to the optimized
      formalization provided here *)
  lemma protocol_equivalence (rp : prover_rand_t) (rv : verifier_rand_t) topo gg ys w inst : 
    LPZK.protocol (rp, rv) ((w, ({| topo = topo ; gates = gg ; out_wires = ys |}, inst)), ({| topo = topo ; gates = gg ; out_wires = ys |}, inst)) = 
    protocol (rp, rv) ((w, ({| topo = topo ; gates = gg ; out_wires = ys |}, inst)), ({| topo = topo ; gates = gg ; out_wires = ys |}, inst)) by smt(prove_equivalence).

  (** Instantiation of the DVNIZK protocol syntax with the optimized LPZK types and operators *)
  clone import ADVNIZKPProtocol.DVNIZKPProtocol with
    type witness_t = witness_t,
    type statement_t = statement_t,
    type prover_input_t = prover_input_t,
    type verifier_input_t = verifier_input_t,
    type prover_rand_t = prover_rand_t,
    type commitment_t = commitment_t,
    type trace_t = trace_t,
    type verifier_rand_t = verifier_rand_t,
    type prover_output_t = prover_output_t,
    type verifier_output_t = verifier_output_t,
    op relation = relation,
    op valid_inputs = valid_inputs,
    op valid_rand_verifier = valid_rand_verifier,
    op valid_rand_prover = valid_rand_prover,
    op commit = commit,
    op prove = prove,
    op protocol = protocol
  proof *.
  (** Correctness lemma. Proves that the protocol securely evaluates the relation, i.e.:
        - if the witness and statement are not in the relation, then the protocol always outputs
          false; and
        - if the witness and statement are in the relation, then the protocol always outputs true

      Because the optimized LPZK version is equivalent to the LPZK version of *LPZK.ec*, we re-use
      the correcntess lemma already proved in *LPZK.ec*. *)
  realize correct.
    rewrite /valid_inputs /=.
    move => r x.
    elim r => rp rv /=.
    elim x => xp xv /=.
    elim xp => w stp /=.
    elim xv => c inst /=.
    elim c => topo gg ys /=.
    progress.
    rewrite /DVNIZKPProtocol.protocol -(protocol_equivalence rp rv topo gg ys w inst) 
            /DVNIZKPProtocol.relation /= /LPZKFaster.relation /=.
    by smt(LPZK.DVNIZKPProtocol.correct).
  qed.

  (** Completeness proof *)
  (** First, we import the completeness security definition instantiated with LPZKFaster *)
  clone import Completeness as LZPKCompleteness with
    theory DVNIZKPProtocol <- DVNIZKPProtocol.

  section Completeness.

    (** Randomness generator declaration *)
    declare module R <: Rand_t.
    (** Assumes that the randomness generator always terminates *)
    axiom r_gen_ll : islossless R.gen.

    (** Proves the desired completness lemma, according to the completeness game of the
        *CompletenessDVNIZKP.ec* file: we prove that, if the witness and the statement are in the
        relation, then the LPZK protocol will always produce true. The proof is done by using
        the correctness proof above. 

        Note that we could prove that the completeness game from *LPZK.ec* is equivalent to the
        one formalized here, but, although it would be an easy proof to do, it would be more 
        complex than the one we provide bellow *)
    lemma completeness &m w_ x_ : relation w_ x_ => 
                                  Pr[Completeness(R).main(w_,x_) @ &m : res] = 1%r.
    proof.
      move => H; byphoare (_ : w_ = w /\ x = x_ ==> res) => //.
      proc.
      seq 1 : #pre => //.
        by call r_gen_ll.
        by wp; skip; progress; move : (correct (r_p{hr}, r_v{hr}) ((w{hr}, x{hr}), x{hr})) => /#.
        by hoare; call (_ : true).
      qed.

  end section Completeness.

  (** Soundness proof *)
  (** First, we import the soundness security definition instantiated with LPZKFaster *)
  clone import Soundness as LPZKSoundness with
    theory DVNIZKPProtocol <- DVNIZKPProtocol.

  section Soundness.

    (** Malicious prover declaration *)
    declare module MP <: LPZK.LPZKSoundness.MProver_t.

    (** Establishes the equivalence between the soundness game of **LPZK** and the soundness
        game of **LPZKFaster**. If both games are equivalent, then they will have the same
        soundness error, which was already proved in *LPZK.ec*. 

        Note that we are also re-using the concrete randomness generator for the verifier define
        in *LPZK.ec* *)
    lemma soundness_eq :
      equiv [ Soundness(LPZK.RV, MP).main ~ LPZK.LPZKSoundness.Soundness(LPZK.RV, MP).main : 
        ={rp, x, glob RV, glob MP} ==> ={res} ].
    proof.
      proc.
      seq 1 1 : (#pre /\ ={c}); first by
        call (_ : true); skip; progress.
      seq 1 1 : (#pre /\ ={rv}); first by
        inline *; wp; rnd; wp; skip; progress.
      if => //=; last by wp.
        by smt().
      wp; skip; progress.
      case (language x{2}); progress; first by smt().
      have ->: ! (LPZK.DVNIZKPProtocol.language x{2}) by smt().
      by simplify; smt(prove_equivalence).
    qed.

    (** Since the two soundness games are equivalent, they will have the same soundness error *)
    lemma soundness &m (x_ : statement_t) rp_ :
                                 Pr [ Soundness(RV, MP).main(rp_, x_) @ &m : res ] <= 1%r / q%r.
    proof.
      have ->: Pr[Soundness(RV, MP).main(rp_, x_) @ &m : res] = 
               Pr[LPZK.LPZKSoundness.Soundness(RV, MP).main(rp_, x_) @ &m : res]
        by byequiv soundness_eq.
      by apply (LPZK.soundness MP &m x_ rp_).
    qed.

  end section Soundness.

  (** Zero-knowledge proof *)
  (** First, we import the zero-knowledge security definition instantiated with LPZKFaster *)
  clone import ZeroKnowledge as LPZKZeroKnowledge with
    theory DVNIZKPProtocol <- DVNIZKPProtocol.

  section ZeroKnowledge.

    (** Distinguisher declaration *)    
    declare module D <: LPZK.LPZKZeroKnowledge.Distinguisher_t.
    (** Malicious verifier declaration *)    
    declare module MV <: LPZK.LPZKZeroKnowledge.MVerifier_t{-D}.

    (** Establishes the equivalence between the *real* world game of **LPZK** and the *real*
        world game of **LPZKFaster**. If both games are equivalent, then the *real* world of
        **LPZKFaster** will also be equivalent to the *ideal* world game of **LPZK** and,
        consequently, **LPZKFaster** behavior could also be simulated by the simulator defined in
        *LPZK.ec*. *)    
    lemma game_real_equiv &m :
      equiv [ GameReal(D, LPZK.RP, MV).main ~ LPZK.LPZKZeroKnowledge.GameReal(D, RP, MV).main :
                ={glob RP, glob D, glob MV, w,x} ==> ={res} ].
    proof.
      proc; inline *.
      sp 5 5 => /=.
      seq 3 3 : (#pre /\ ={rp0}).
        case (topo{2}.`npinputs + topo{2}.`nsinputs + topo{2}.`ngates < 0).
          rcondf{1} 3. progress. wp; skip; progress. smt().
          rcondf{2} 3. progress. wp; skip; progress. smt().
          wp; skip; progress.
        while (#pre /\ ={i} /\ 0 <= i{2} <= topo{2}.`npinputs + topo{2}.`nsinputs + topo{2}.`ngates /\ ={rp0}).
          wp.
          do rnd.
          wp; skip; progress.
            smt().
            smt().
          wp; skip; progress.
            smt().
      seq 7 7 : (#pre /\ ={rp} /\ rp{2} = rp0{2}).
        wp. do rnd. wp. do rnd. skip; progress.
      (if; first by smt()); last first.
        by rnd.
      call (_ : true).
      wp.
      call (_ : true).
      by wp; skip; progress.
    qed.

    (** Zero-knowledge lemma for **LPZKFaster**, that uses the previous equivalence to prove 
        that the *real* world game is equivalent to the *ideal* world of **LPZK** *)  
    lemma zero_knowledge &m (w : witness_t) (x : statement_t) :
      valid_circuit x.`1 =>
      relation w x =>
      size w = x.`1.`topo.`nsinputs =>
      size x.`2 = x.`1.`topo.`npinputs =>
      Pr[ GameReal(D, RP, MV).main(w,x) @ &m : res ] = 
      Pr[ LPZK.LPZKZeroKnowledge.GameIdeal(D, RP, MV, LPZK.Simulator).main(w,x) @ &m : res ].
    proof.  
      progress.
      rewrite -(LPZK.zero_knowledge D MV) //=.
      by byequiv (game_real_equiv &m) => //=.
    qed.      

  end section ZeroKnowledge.

  (** Final printouts, printing a *readable* version of the completeness, soundness and 
      zero-knowledge lemmas *)
  print completeness.
  print soundness.
  print zero_knowledge.

end LPZKFaster.
