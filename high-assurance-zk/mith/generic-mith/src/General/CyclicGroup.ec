(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

from General require import PrimeField.

type group.

op g:group. (* the generator *)
op cgmul : group -> group -> group.   (* multiplication of group elements *)
op cginv : group -> group.             (* inverse of the multiplication *)
op cgdiv : group -> group -> group.   (* division *)
op cgexp : group -> t -> group.       (* exponentiation *)
op log  : group -> t.                (* discrete logarithm *)
op g1 = cgexp g fzero.

axiom gpow_log (a:group): cgexp g (log a) = a.
axiom log_gpow x : log (cgexp g x) = x.

axiom nosmt log_bij x y: x = y <=> log x = log y.
lemma nosmt pow_bij (x y: t): x = y <=> cgexp g x = cgexp g y by [].


axiom inv_def (a:group): cginv a = cgexp g (fumin (log a)).
axiom div_def (a b:group): cgexp g (fsub (log a) (log b)) = cgdiv a b.

axiom mul_pow g (x y:t): cgmul (cgexp g x) (cgexp g y) = cgexp g (fadd x y).

axiom pow_pow g (x y:t): cgexp (cgexp g x) y = cgexp g (fmul x y).

lemma nosmt log_pow (g1:group) x: log (cgexp g1 x) = fmul (log g1) x by [].

lemma nosmt log_mul (g1 g2:group): log (cgmul g1 g2) = fadd (log g1) (log g2) by [].

lemma nosmt pow_mul (g1 g2:group) x: cgmul (cgexp g1 x) (cgexp g2 x) = cgexp (cgmul g1 g2) x.
proof.
  rewrite -{1}(gpow_log g1) -{1}(gpow_log g2) !pow_pow mul_pow.
  by rewrite !(mulC _ x) mulfDl mulC -pow_pow -mul_pow !gpow_log.
qed.

lemma nosmt pow_opp (x:group) (p: t): cgexp x (fumin p) = cginv (cgexp x p).
proof.
  rewrite inv_def.
  have -> : fumin p = fmul (fumin fone) p by ringeq.
  have -> : fumin (log (cgexp x p)) = fmul (fumin fone) (log (cgexp x p)) by ringeq.
  by rewrite !(mulC (fumin fone)) -!pow_pow gpow_log.
qed.

lemma nosmt mulC (x y: group): cgmul x y = cgmul y x.
proof.
  by rewrite -(gpow_log x) -(gpow_log y) mul_pow;smt.
qed.

lemma nosmt mulA (x y z: group): cgmul x (cgmul y z) = cgmul (cgmul x y) z.
proof.
  by rewrite -(gpow_log x) -(gpow_log y) -(gpow_log z) !mul_pow;smt.
qed.

lemma nosmt mul1 x: cgmul g1 x = x.
proof.
  by rewrite /g1 -(gpow_log x) mul_pow;smt.
qed.

lemma nosmt divK (a:group): cgdiv a a = g1.
proof strict.
  by rewrite -div_def sub_def addfN.
qed.

axiom log_g : log g = fone.

lemma nosmt g_neq0 : g1 <> g.
proof.
  rewrite /g1 -{2}(gpow_log g) log_g -pow_bij;smt.
qed.

lemma mulN (x:group): cgmul x (cginv x) = g1.
proof.
  rewrite inv_def -{1}(gpow_log x) mul_pow;smt.
qed.

lemma inj_gpow_log (a:group): a = cgexp g (log a) by smt.

hint rewrite Ring.inj_algebra : inj_gpow_log.
hint rewrite Ring.rw_algebra : log_g log_pow log_mul log_bij.

