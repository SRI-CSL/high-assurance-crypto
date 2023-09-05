require import Int IntDiv List DList.

from General require import ListExt PrimeField Utils.
from SecretSharing require import ASecretSharingScheme SecretSharingSchemeSecurity.

theory Additive.

  const n : {int | 2 <= n} as n_pos.
  const t = n - 1.

  type pid_t = t.
  op pid_set : pid_t list.
  axiom pid_set_uniq : uniq pid_set.
  axiom pid_set_size : size pid_set = n.
  (*axiom pid_set_def : pid_set = map ofint (range 0 n).*)

  type secret_t = t.

  op valid_secret (x : secret_t) : bool = true.

  type share_t = t.
  type shares_t = (pid_t * share_t) list.

  type rand_t = t list.
  op valid_rand (r : rand_t) (s : secret_t) : bool = size r = n - 1.

  op public_encoding (x : secret_t) : (pid_t * share_t) list = witness.
    (*map (fun pid => (pid, if pid %% 2 = 0 then x else fsub fzero x)) pid_set.*)
  op pub_reconstruct (pid : pid_t) (sh : share_t) : secret_t = witness.
    (*if pid %% 2 = 0 then sh else fadd sh (fadd sh sh).*)

  op share (r : rand_t) (x : secret_t) : (pid_t * share_t) list = 
    let r = (fsub x (sumt r)) :: r in
    zip pid_set r.

  op reconstruct (xx : (pid_t * share_t) list) : secret_t = sumt (map snd xx).

  op get_party_share (pid : pid_t) (xs : shares_t) : share_t = oget (assoc xs pid).

  op reconstruct_rand (ss : shares_t) : rand_t = 
    let ss = behead ss in unzip2 ss.
  op consistent_shares (i j : pid_t) (shi shj : share_t) : bool = 
    exists r s, valid_rand r s /\ 
                let ss = share r s in 
                get_party_share i ss = shi /\
                get_party_share j ss = shj.

  clone import SecretSharingScheme with
    op n = n,
    op t = t,
    type pid_t = pid_t,
    op pid_set = pid_set,
    type secret_t = secret_t,
    op valid_secret = valid_secret,
    type share_t = share_t,
    type rand_t = rand_t,
    op valid_rand = valid_rand,
    op public_encoding = public_encoding,
    op pub_reconstruct = pub_reconstruct,
    op share = share,
    op reconstruct = reconstruct,
    op get_party_share = get_party_share,
    op consistent_shares = consistent_shares,
    op reconstruct_rand = reconstruct_rand
  proof n_pos, t_pos, pid_set_size, pid_set_uniq, correct, unzip1_share.
  realize n_pos by smt(n_pos).
  realize t_pos by rewrite /t /=; smt(n_pos).
  realize pid_set_size by apply pid_set_size.
  realize pid_set_uniq by apply pid_set_uniq.
  realize correct.
    rewrite /valid_rand /valid_secret /share /reconstruct => /> r s H.
rewrite unzip2_zip.
simplify.
rewrite H.
smt(pid_set_size).
rewrite /sumt /=.
by ringeq.
  qed.
  realize unzip1_share.
    rewrite /valid_rand /share => r s />; progress.
rewrite unzip1_zip.
smt(pid_set_size).
done.
  qed.

  clone import SecretSharingSchemeSecurity with 
    theory SS = SecretSharingScheme,
    type aux_t = secret_t.

  section Security.

    module R = {
      proc gen(aux : aux_t) : rand_t = {
        var ds;
        ds <$ dlist FDistr.dt (n-1);
        return ds;
      }
    }.

    module S = {
      proc simm(aux : aux_t, r : rand_t, cr : pid_t list) : shares_t = {
        var rhd, ss;
        rhd <$ FDistr.dt;
        r <- rhd :: r;
        ss <- zip pid_set r;
        return (map (fun pid => (pid, oget (assoc ss pid))) cr);
      }
    }.

    declare module D : Distinguisher_t.

    clone import Program with type t = t, op d = FDistr.dt.
  
    equiv real_ideal_eq :
      GameReal(D, R).main ~ GameIdeal(D,R,S).main :
        ={glob D, aux, s} ==> ={res}.
proof.
proc => //=.
seq 1 1 : (#pre /\ ={cr}).
call (_ : true).
skip; progress.
case (valid_corrupted_set cr{1}); last first.
inline*.
rcondf{1} 4.
progress.
wp; rnd; wp; skip; progress.
by rewrite H.
rcondf{2} 4.
progress.
wp; rnd; wp; skip; progress.
by rewrite H.
rnd; wp; rnd; wp; skip; progress.

rcondt{1} 2.
progress.
inline*.
wp; rnd; wp; skip; progress.
rewrite /valid_rand.
rewrite (supp_dlist_size FDistr.dt (Additive.n - 1)).
smt(n_pos).
done.
done.

rcondt{2} 2.
progress.
inline*.
wp; rnd; wp; skip; progress.
rewrite /valid_rand.
rewrite (supp_dlist_size FDistr.dt (Additive.n - 1)).
smt(n_pos).
done.
done.

inline*.
swap{2} 11 - 8.
swap{2} 6 - 1.
swap{2} 10 - 4.
swap{2} 12 - 5.

transitivity{2}
{
aux0 <- aux;
(*ds <$ dlist FDistr.dt (Addition.n - 1);
rhd <$ FDistr.dt;
r <- ds;
r0 <- r;
r1 <- r0;
r1 <- rhd :: r1;*)
r1 <@ SampleCons.sample(Additive.n);
aux1 <- aux;
s0 <- s;
cr0 <- cr;
aux2 <- aux1;
cr1 <- cr0;
ss0 <- zip Additive.pid_set r1;
ssc <- map (fun (pid : Additive.pid_t) => (pid, oget (assoc ss0 pid))) cr1;
ss <- ssc;
b' <@ D.guess(s, ss);
}
( (={glob D, aux, s} /\ ={cr}) /\ valid_corrupted_set cr{1} ==> ={b'} )
( (={glob D, aux, s} /\ ={cr}) /\ valid_corrupted_set cr{1} ==> ={b'} ).

progress.
exists (glob D){2} aux{2} cr{2} s{2}.
done.
smt().

(****)
transitivity{2}
{
aux0 <- aux;
(*ds <$ dlist FDistr.dt (Addition.n - 1);
rhd <$ FDistr.dt;
r <- ds;
r0 <- r;
r1 <- r0;
r1 <- rhd :: r1;*)
r1 <@ Sample.sample(Additive.n);
aux1 <- aux;
s0 <- s;
cr0 <- cr;
aux2 <- aux1;
cr1 <- cr0;
ss0 <- zip Additive.pid_set r1;
ssc <- map (fun (pid : Additive.pid_t) => (pid, oget (assoc ss0 pid))) cr1;
ss <- ssc;
b' <@ D.guess(s, ss);
}
( (={glob D, aux, s} /\ ={cr}) /\ valid_corrupted_set cr{1} ==> ={b'} )
( (={glob D, aux, s} /\ ={cr}) /\ valid_corrupted_set cr{1} ==> ={b'} ).

progress.
exists (glob D){2} aux{2} cr{2} s{2}.
done.
smt().

transitivity{2}
{
aux0 <- aux;
(*ds <$ dlist FDistr.dt (Addition.n - 1);
rhd <$ FDistr.dt;
r <- ds;
r0 <- r;
r1 <- r0;
r1 <- rhd :: r1;*)
r1 <@ RsumI.gen(Additive.n-1);
aux1 <- aux;
s0 <- s;
cr0 <- cr;
aux2 <- aux1;
cr1 <- cr0;
ss0 <- zip Additive.pid_set r1;
ssc <- map (fun (pid : Additive.pid_t) => (pid, oget (assoc ss0 pid))) cr1;
ss <- ssc;
b' <@ D.guess(s, ss);
}
( (={glob D, aux, s} /\ ={cr}) /\ valid_corrupted_set cr{1} ==> ={b'} )
( (={glob D, aux, s} /\ ={cr}) /\ valid_corrupted_set cr{1} ==> ={b'} ).

progress.
exists (glob D){2} aux{2} cr{2} s{2}.
done.
smt().

transitivity{1}
{
aux0 <- aux;
r0 <@ RsumR.gen(Additive.n-1, s);
ss0 <- zip pid_set r0;
ssc <- map (fun (pid : Additive.pid_t) => (pid, oget (assoc ss0 pid))) cr;
ss <- ssc;
b' <@ D.guess(s, ss);
}
( (={glob D, aux, s} /\ ={cr}) /\ valid_corrupted_set cr{1} ==> ={b'} )
( (={glob D, aux, s} /\ ={cr}) /\ valid_corrupted_set cr{1} ==> ={b'} ).

progress.
exists (glob D){2} aux{2} cr{2} s{2}.
done.
smt().

inline*.
call (_ : true).
wp.
rnd.
by wp; skip; progress.

call (_ : true).
wp.
call eq_rand_gen.
by wp; skip; progress.

call (_ : true).
wp.
inline *.
by wp; rnd; wp; skip; progress. 

(****)

call (_ : true).
wp.
call Sample_SampleCons_eq.
wp; skip; progress.
smt(n_pos).

call (_ : true).
wp.
inline*. 
wp.
rnd.
rnd.
wp; skip; progress.
qed.

    require import Real.

    lemma security &m aux s : 
      Pr [ GameReal(D,R).main(aux, s) @ &m : res ] - 
      Pr [ GameIdeal(D,R,S).main(aux, s) @ &m : res ] = 0%r.
    proof.
      have ->: Pr[GameReal(D, R).main(aux, s) @ &m : res] = 
               Pr[GameIdeal(D, R, S).main(aux, s) @ &m : res].
        by byequiv real_ideal_eq.
      by done.
    qed.

  end section Security.

end Additive.
