require import Int IntDiv.

(* the order of field is a prime q *)
op q: int.
axiom q_pos:  Int.(<) 0 q.
(* TODO: Add an axiom asserting primality of q. *)

(* Type of elements of the field *)
type t.
op fzero : t. (* zero *)
op fone  : t. (* one *)
op fmul : t -> t -> t.  (* multiplication modulo q *)
op fadd : t -> t -> t.  (* addition modulo q *)
op fumin : t -> t.       (* the additive inverse *)
op finv: t -> t.         (* the multiplicative inverse *)

op fsub : t -> t -> t.   (* subtraction modulo q *)
op fdiv : t -> t -> t.   (* division modulo q for y <> 0 *)
op fexp : t -> int -> t. (* exponentiation *)

axiom non_trivial: fzero <> fone.

(* Addition/Subtraction *)
axiom addC (x y:t): fadd x y = fadd y x.
axiom addA (x y z:t) : fadd x (fadd y z) = fadd (fadd x y) z.
axiom addf0 (x:t): fadd x fzero = x.
axiom addfN (x:t): fadd x (fumin x) = fzero.
axiom sub_def (x y:t) : fsub x y = fadd x (fumin y).

(* Multiplication *)
axiom mulC (x y:t): fmul x y = fmul y x.
axiom mulA (x y z:t): fmul x (fmul y z) = fmul (fmul x y) z.
axiom mulf1 (x:t): fmul x fone = x.
axiom mulfV (x:t): x <> fzero => (fmul x (finv x)) = fone.
axiom mulfDl (x y z:t): fadd (fmul x y) (fmul x z) = fmul x (fadd y z).
axiom div_def (x y:t): fdiv x y = fmul x (finv y).

axiom mulf_eq0:
  forall (x y : t), fmul x y = fzero <=> x = fzero \/ y = fzero.

(* Exponentiation *)
axiom pow0 (x:t): fexp x 0 = fone.
axiom powS (x:t) (n:int): Int.(<=) 0 n => fexp x (Int.(+) n 1) = fmul x (fexp x n).
lemma pow1 (x:t) : fexp x 1 = x.
proof.
  have ->: 1 = 0 + 1 by done.
  by rewrite powS // pow0 mulf1.
qed.  

axiom powN (x:t) (n:int): Int.(<=) 0 n => fexp x (Int.([-]) n) = finv (fexp x n).

(** conversion between int and gf_q *)
op ofint : int -> t.
op toint : t -> int.

axiom ofint0: ofint 0 = fzero.
axiom ofintS (n:int): Int.(<=) 0 n => ofint (Int.(+) n 1) = fadd (ofint n) fone.
axiom ofintN (n:int): ofint (Int.([-]) n) = fumin (ofint n).

axiom toint_bounded (x:t): 0 <= toint x < q.
axiom oftoint (x:t): ofint (toint x) = x.
axiom toofint_mod (x:int): toint (ofint x) = IntDiv.(%%) x q.

(* Declaring the ring and field structure *)
require AlgTactic.
require Ring.

instance ring with t
  op rzero = fzero
  op rone  = fone
  op add   = fadd
  op opp   = fumin
  op mul   = fmul
  op expr  = fexp
  op sub   = fsub
  op ofint = ofint

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof expr0     by smt
  proof exprS     by smt
  proof subrE     by smt
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt
  proof ofintN    by smt.

instance field with t
  op rzero = fzero
  op rone  = fone
  op add   = fadd
  op opp   = fumin
  op mul   = fmul
  op expr  = fexp
  op sub   = fsub
  op ofint = ofint
  op inv   = finv
  op div   = fdiv

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof mulrV     by smt
  proof expr0     by smt
  proof exprS     by smt
  proof exprN     by smt
  proof subrE     by smt
  proof divrE     by smt
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt
  proof ofintN    by smt.

(** Lemmas *)
lemma nosmt subff (x:t): (fsub x x) = fzero
by ringeq.

lemma nosmt add0f (x:t): fadd fzero x = x
by ringeq.

lemma nosmt mulf0 (x:t): fmul x fzero = fzero
by ringeq.

lemma nosmt mulNf (x y:t): fmul (fumin x) y = fumin (fmul x y)
by ringeq.

lemma nosmt mulfN (x y:t): fmul y (fumin x) = fumin(fmul y x)
by ringeq.

lemma nosmt oppK (x:t): fumin (fumin x) = x
by ringeq.

lemma nosmt mulfNl (x y z:t): fsub (fmul x y) (fmul x z) = fmul x (fsub y z)
by ringeq.

lemma nosmt mulN1f (x:t): fmul (fumin fone) x = fumin x
by ringeq.

lemma nosmt oppfD (x y:t): fadd (fumin x) (fumin y) = fumin (fadd x y)
by ringeq.

lemma nosmt toint_pos (x:t): 0 <= toint x
by [].

lemma nosmt toint_lt (x:t): toint x < q
by [].

lemma nosmt toint_le (x:t): toint x <= q - 1
by [].

lemma nosmt toofint (x:int): 0 <= x => x < q => toint (ofint x) = x.
proof. by move=> Hp Hlt; rewrite toofint_mod IntDiv.modz_small /#. qed.

lemma nosmt ofint1_: ofint 1 = fone
by [].

theory FDistr.

  require import Distr.
  require import Real.
  (* distrinution *)
  op dt: t distr.

  axiom dt_fu: is_full dt.

  axiom dt1E: forall (s:t), mu1 dt s = (1%r/q%r)%Real.

  axiom dt_ll: is_lossless dt.

  lemma dt_funi: is_funiform dt.
  proof. by move=> ??;rewrite !dt1E. qed.

  hint exact random : dt_fu dt_ll dt_funi.

end FDistr.

(* ==================================================================== *)
(** Field utils *)
lemma mulfDr : forall (x y z : t), fadd (fmul y x) (fmul z x) = fmul (fadd y z) x.
proof. by move => x y z; ringeq. qed.

(* -------------------------------------------------------------------- *)
lemma binom_mult (x y w z : t) :
  fmul (fadd x y) (fadd w z) = fadd (fadd (fadd (fmul x w) (fmul x z)) (fmul y w)) (fmul y z).
proof. by rewrite -mulfDr -!mulfDl addA. qed.

(* -------------------------------------------------------------------- *)
lemma powEA (x:t) (n:int) (n':int): Int.(<=) 0 n => Int.(<=) 0 n' => fexp x (Int.(+) n n') = fmul (fexp x n) (fexp x n').
proof.
  elim: n => /=.
    + by progress; rewrite pow0 mulC mulf1.
  progress; move : H1 H0; elim: n'; progress.
    + by rewrite pow0 mulf1.
  rewrite powS //.
  rewrite (_: fexp x (i + 1 + (i0 + 1)) = fexp x ((i + 1 + i0) + 1)). by rewrite addzA.
  rewrite powS; first by smt().
  by rewrite -mulA -H2 1:/# (addzC i0 1) addzA.
qed.

(* -------------------------------------------------------------------- *)
lemma same_divisor_add : forall (x y z : t), fadd (fdiv x z) (fdiv y z) = fdiv (fadd x y) z by [].

(* -------------------------------------------------------------------- *)
lemma same_divisor_sub : forall (x y z : t), z <> fzero => fsub (fdiv x z) (fdiv y z) = fdiv (fsub x y) z.
proof. by progress; rewrite !div_def (mulC x _) (mulC y _) mulfNl mulC. qed.

(* -------------------------------------------------------------------- *)
lemma diff_sub_zero : forall (x y : t), x <> y => fsub x y <> fzero.
proof.
  progress.
  + case (fsub x y = fzero) => ?.
    by have ?: x = y by ringeq; rewrite addC -sub_def ofint0.
  by done.
qed.

(* -------------------------------------------------------------------- *)
lemma zero_div x : fdiv fzero x = fzero.
proof. by rewrite div_def mulC mulf0. qed.

(* -------------------------------------------------------------------- *)
lemma divff (x : t) : x <> fzero => fdiv x x = fone.
proof. by move => ?; rewrite div_def mulfV. qed.

(* -------------------------------------------------------------------- *)
lemma zero_pow (x : int) : 0 < x => fexp fzero x = fzero.
proof.
  progress.
  have H0 : 0 <= x by smt().
  move : H.
  move : H0; elim x => /> *.
  by rewrite powS // mulC mulf0.
qed.

(* -------------------------------------------------------------------- *)
lemma div_mul_eq (x y w z a : t) : 
  fsub z w <> fzero =>
  (fdiv (fsub x y) (fsub z w) = a) = ((fsub x y) = fmul a (fsub z w)). 
proof. by move => *; smt. qed.
