require import AllCore List Distr Dfilter.
require import RealFun RealSeq RealSeries.
require import Ring StdRing StdOrder StdBigop Discrete.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.

from General require import CyclicGroup PrimeField.

lemma existsN : forall (p : 'a -> bool), !(exists x, p x) <=> (forall x, !p x) by [].
lemma forallN : forall (p : 'a -> bool), !(forall x, p x) <=> (exists x, !p x) by [].

(* ==================================================================== *)
(** Party identifiers *)
type pid_zk_t = [ | Prover | Verifier ].
type pid_mpc_t = [ | P1 | P2 | P3 | P4 | P5 ].
op pid_mpc_set = [P1;P2;P3;P4;P5].

(*op pid_mpc_distr_f : pid_mpc_t -> real = fun pid => if pid \in pid_mpc_set then inv 5%r else 0%r.*)
op pid_mpc_distr_f : pid_mpc_t -> real = fun pid => inv 5%r.
op pid_mpc_distr : pid_mpc_t distr = mk pid_mpc_distr_f.

lemma uniq_mpc_size (s : pid_mpc_t list) : uniq s => size s <= 5.
proof.
  elim s => // x s.
  elim s => // x1 s.
  elim s => // x2 s.
  elim s => // x3 s.
  elim s => // x4 s.
  by smt().
qed.

lemma uniq_mpc_sizeN (s : pid_mpc_t list) x : !(x \in s) => uniq s => size s <= 4.
proof.
  elim s => // x1 s.
  elim s => // x2 s.
  elim s => // x3 s.
  elim s => // x4 s.
  elim s => // x5 s.
  by smt().
qed.

lemma isdistr_pid_mpc_distr_f : isdistr pid_mpc_distr_f.
proof.
  split => s; first by smt().
  elim s; first by smt().
  move => x s; elim s; first by rewrite /big /= /predT /= /#.
  move => x1 s; elim s; first by rewrite /big /= /predT /= /#.
  move => x2 s; elim s; first by rewrite /big /= /predT /= /#.
  move => x3 s; elim s; first by rewrite /big /= /predT /= /#.
  move => x4 s; elim s; first by rewrite /big /= /predT /= /#.
  by smt().
qed.

lemma pid_mpc_distr1E x :
  mu1 pid_mpc_distr x = inv 5%r.
proof. 
rewrite /pid_mpc_distr.
rewrite -massE.
rewrite muK //.
apply isdistr_pid_mpc_distr_f.
qed.

lemma supp_pid_mpc_distr x :
  x \in pid_mpc_distr <=> x \in pid_mpc_set.
proof.
rewrite supportP pid_mpc_distr1E. simplify.
by case x; rewrite /pid_mpc_set // => /#. 
qed.

lemma weight_pid_mpc_distr:
  weight pid_mpc_distr = 1%r.
proof. 
  rewrite muE (sumE_fin (mass pid_mpc_distr) pid_mpc_set).
    by rewrite /pid_mpc_set //.
    by smt().
    by rewrite /big /pid_mpc_set filter_predT foldr_map /= !massE !pid_mpc_distr1E. 
qed.

lemma pid_mpc_distr_ll : is_lossless pid_mpc_distr. 
proof. by rewrite /is_lossless weight_pid_mpc_distr. qed.

op pid_mpc_tuple_distr : (pid_mpc_t * pid_mpc_t) distr = pid_mpc_distr `*` pid_mpc_distr.
op challenge_distr : (pid_mpc_t * pid_mpc_t) distr.

axiom challenge_distr1E x :
  mu1 challenge_distr x = inv 10%r.

axiom pid_mpc_distr_tuple_ll : is_lossless pid_mpc_tuple_distr. 

op next_pid (pid : pid_mpc_t) : pid_mpc_t =
  with pid = P1 => P2
  with pid = P2 => P3
  with pid = P3 => P4
  with pid = P4 => P5
  with pid = P5 => P1.

op get_party_data (pid : pid_mpc_t) (x : 'a * 'a * 'a * 'a * 'a) : 'a =
  with pid = P1 => let (x1,x2,x3,x4,x5) = x in x1
  with pid = P2 => let (x1,x2,x3,x4,x5) = x in x2
  with pid = P3 => let (x1,x2,x3,x4,x5) = x in x3
  with pid = P4 => let (x1,x2,x3,x4,x5) = x in x4
  with pid = P5 => let (x1,x2,x3,x4,x5) = x in x5.

op get_other_pids (i j : pid_mpc_t) : pid_mpc_t * pid_mpc_t * pid_mpc_t =
  with i = P1, j = P1 => (P3,P4,P5) (*witness*)
  with i = P1, j = P2 => (P3,P4,P5)
  with i = P1, j = P3 => (P2,P4,P5)
  with i = P1, j = P4 => (P2,P3,P5)
  with i = P1, j = P5 => (P2,P3,P4)

  with i = P2, j = P1 => (P3,P4,P5)
  with i = P2, j = P2 => (P3,P4,P5) (*witness*)
  with i = P2, j = P3 => (P1,P4,P5)
  with i = P2, j = P4 => (P1,P3,P5)
  with i = P2, j = P5 => (P1,P3,P4)

  with i = P3, j = P1 => (P2,P4,P5)
  with i = P3, j = P2 => (P1,P4,P5)
  with i = P3, j = P3 => (P1,P4,P5) (*witness*)
  with i = P3, j = P4 => (P1,P2,P5)
  with i = P3, j = P5 => (P1,P2,P4)

  with i = P4, j = P1 => (P2,P3,P5)
  with i = P4, j = P2 => (P1,P3,P5)
  with i = P4, j = P3 => (P1,P2,P5)
  with i = P4, j = P4 => (P1,P2,P5) (*witness*)
  with i = P4, j = P5 => (P1,P2,P3)

  with i = P5, j = P1 => (P2,P3,P4)
  with i = P5, j = P2 => (P1,P3,P4)
  with i = P5, j = P3 => (P1,P2,P4)
  with i = P5, j = P4 => (P1,P2,P3)
  with i = P5, j = P5 => (P1,P2,P3) (*witness*).

op replace5_tuple (x : (pid_mpc_t * 'a) * (pid_mpc_t * 'a) * 
                       (pid_mpc_t * 'a) * (pid_mpc_t * 'a) * (pid_mpc_t * 'a)) 
                  (pid : pid_mpc_t) (xi : 'a) =
  with pid = P1 => let (x1,x2,x3,x4,x5) = x in ((pid,xi),x2,x3,x4,x5)
  with pid = P2 => let (x1,x2,x3,x4,x5) = x in (x1,(pid,xi),x3,x4,x5)
  with pid = P3 => let (x1,x2,x3,x4,x5) = x in (x1,x2,(pid,xi),x4,x5)
  with pid = P4 => let (x1,x2,x3,x4,x5) = x in (x1,x2,x3,(pid,xi),x5)
  with pid = P5 => let (x1,x2,x3,x4,x5) = x in (x1,x2,x3,x4,(pid,xi)).

op assemble (xa xb xc xd xe : (pid_mpc_t * 'a)) =
  let (a,xa) = xa in
  let (b,xb) = xb in
  let (c,xc) = xc in
  let (d,xd) = xd in
  let (e,xe) = xe in

  replace5_tuple (replace5_tuple (replace5_tuple (replace5_tuple (replace5_tuple (witness, witness, witness, witness, witness) a xa) b xb) c xc) d xd) e xe.

op tuple5_to_list (x : 'a * 'a * 'a * 'a * 'a) : 'a list =
  let (x1,x2,x3,x4,x5) = x in
  [x1;x2;x3;x4;x5].

lemma assocP1 (x y z w v : 'a) : 
assoc [(P1, x); (P2, y); (P3, z); (P4, w); (P5, v)] P1 = Some x.
proof.
smt().
qed.

lemma assocP2 (x y z w v : 'a) : 
assoc [(P1, x); (P2, y); (P3, z); (P4, w); (P5, v)] P2 = Some y.
proof.
smt().
qed.

lemma assocP3 (x y z w v : 'a) : 
assoc [(P1, x); (P2, y); (P3, z); (P4, w); (P5, v)] P3 = Some z.
proof.
smt().
qed.

lemma assocP4 (x y z w v : 'a) : 
assoc [(P1, x); (P2, y); (P3, z); (P4, w); (P5, v)] P4 = Some w.
proof.
smt().
qed.

lemma assocP5 (x y z w v : 'a) : 
assoc [(P1, x); (P2, y); (P3, z); (P4, w); (P5, v)] P5 = Some v.
proof.
smt().
qed.
