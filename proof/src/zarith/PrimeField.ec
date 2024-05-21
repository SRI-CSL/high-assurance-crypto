(**
  Finite field formalization. This file defines elements of a finite field estalished by the
  prime order **q**, and defines all operations as done modulo **q**.
*)
require import Int IntDiv.

(** The order of field is a prime **q** *)
op q: int.
(** Establishes that the prime **q** is bigger than two *)
axiom q_pos:  Int.(<) 2 q.

(** Type of elements of the field *)
type t.
(** Zero element *)
op fzero : t.
(** One element *)
op fone  : t.
(** Multiplication modulo **q** *)
op fmul : t -> t -> t. 
(** Addition modulo **q** *)
op fadd : t -> t -> t.
(** Additive inverse modulo **q** *)
op fumin : t -> t.
(** Multiplicative inverse modulo **q** *)
op finv: t -> t.

(** Subtraction modulo **q** *)
op fsub : t -> t -> t.
(** Division modulo **q** for y <> 0 *)
op fdiv : t -> t -> t.
(** Exponentiation modulo **q** *)
op fexp : t -> int -> t.

(** Needed to establish that **fzero** is a different value than **fone** *)
axiom non_trivial: fzero <> fone.

(** Addition properties *)
(** Commutative addition property *)
axiom addC (x y:t): fadd x y = fadd y x.
(** Associative addition property *)
axiom addA (x y z:t) : fadd x (fadd y z) = fadd (fadd x y) z.
(** Zero as addition neutral element *)
axiom addf0 (x:t): fadd x fzero = x.
(** Addition by additive inverse yields zero *)
axiom addfN (x:t): fadd x (fumin x) = fzero.
(** Subtraction definition: subtracting two values is the same as adding the first value with the
    additive inverse of the second *)
axiom sub_def (x y:t) : fsub x y = fadd x (fumin y).

(** Auxiliar lemma, proving that adding two field yields the value of the first one, then
    the second one is zero *)
lemma add_fzero_imp (x : t) (y : t) : fadd x y = x => y = fzero.
proof.
  move => H. 
  have : y = fadd x (fumin x) by smt.
  move => H0.
  rewrite H0. 
  apply addfN. 
qed.

(** Auxiliar lemma, proving that adding a field element to another element that is different than
    zero will output a different field element *)
lemma non_zero_add (x : t) (y : t) :
  y <> fzero => fadd x y <> x.
proof.
  move => H; case (fadd x y = x) => H2 => //.
  by have : y = fzero by rewrite (add_fzero_imp x y).
qed.

(** Auxiliar lemma, proving that if [x + y = x + z] then [y = z] *)
lemma add_eq_termsL (x y z : t) : fadd x y = fadd x z <=> y = z.
proof. by progress; case (y <> z); smt(addC addA addf0 addfN). qed.

(** Auxiliar lemma, proving that if [y + x = z + x] then [y = z] *)
lemma add_eq_termsR (x y z : t) : fadd y x = fadd z x <=> y = z.
proof. by progress; case (y <> z); smt(addC addA addf0 addfN). qed.

(** Multiplication properties *)
(** Commutative multiplication property *)
axiom mulC (x y:t): fmul x y = fmul y x.
(** Associative multiplication property *)
axiom mulA (x y z:t): fmul x (fmul y z) = fmul (fmul x y) z.
(** Zero as multiplication neutral element *)
axiom mulf1 (x:t): fmul x fone = x.
(** Multiplication by multiplicative inverse yields one *)
axiom mulfV (x:t): x <> fzero => (fmul x (finv x)) = fone.
(** Commutative multiplication property over the addition *)
axiom mulfDl (x y z:t): fadd (fmul x y) (fmul x z) = fmul x (fadd y z).
(** Division definition: dividing two values is the same as multiplying the first value with the
    multiplicative inverse of the second *)
axiom div_def (x y:t): fdiv x y = fmul x (finv y).

(** Auxiliar lemma, proving that if the multiplication of field elements is zero, then one
    of them must by zero *)
lemma mulf_eq0:
  forall (x y : t), fmul x y = fzero <=> x = fzero \/ y = fzero.
proof.
  progress.
  by case (x = fzero); first 2 by smt.
  by case (x = fzero); progress; first 2 by smt.
qed.

(** Auxiliar lemma, provind that equation [(ax + m) = nx] can be transformed into 
    [m = nx - ax] *)
lemma test a x m n :
  a <> fzero => m <> fzero => n <> fzero =>
  (fadd (fmul a x) m = fmul n x) <=> (m = fsub (fmul n x) (fmul a x)).
proof. by smt. qed.

(** Auxiliar lemma, provind that equation [m = nx - ax] can be transformed into 
    [m = (n-a)x] *)
lemma test2 a x m n :
  a <> fzero => m <> fzero => n <> fzero =>
  (m = fsub (fmul n x) (fmul a x)) <=> (m = fmul (fsub n a) x).
proof. by rewrite !sub_def; smt. qed.

(** Auxiliar lemma, provind that equation [m = (n-a)x] can be transformed into 
    [m / (n-a) = x] *)
lemma test3 a x m n :
  a <> fzero => m <> fzero => n <> fzero => n <> a =>
  (m = fmul (fsub n a) x) <=> (fdiv m (fsub n a) = x).
proof. by rewrite !sub_def; smt. qed.

(** Auxiliar lemma, provind that equation [ax + x = nx] can be transformed into 
    [m / (n - a) = x] by following the path of the above lemmas *)
lemma test4 a x m n :
  a <> fzero => m <> fzero => n <> fzero => n <> a =>
  fadd (fmul a x) m = fmul n x <=> fdiv m (fsub n a) = x.
proof. by move => H H0 H1 H2; rewrite test // test2 // test3 //. qed.

(** Auxiliar lemma, provind that equation [ax + b + m = nx] can be transformed into 
    [b + m = nx - ax] *)
lemma test5 a x b m n :
  fadd (fadd (fmul a x) b) m = fmul n x <=> (fadd b m = fsub (fmul n x) (fmul a x)).
proof. by smt. qed.

(** Auxiliar lemma, provind that equation [b + m = nx - ax] can be transformed into 
    [b + m = (n - a)x] *)
lemma test6 a x b m n :
  (fadd b m = fsub (fmul n x) (fmul a x)) <=> (fadd b m = fmul (fsub n a) x).
proof. by smt. qed. 

(** Auxiliar lemma, provind that equation [b + m = (n - a)x] can be transformed into 
    [(b + m) / (n - a) = x] *)
lemma test7 a x b m n :
  n <> a =>
  (fadd b m = fmul (fsub n a) x) <=> (fdiv (fadd b m) (fsub n a) = x).
proof. by rewrite sub_def div_def; smt. qed.

(** Auxiliar lemma, provind that equation [ax + b + m = nx] can be transformed into 
    [(b + m) / (n - a) = x] by following the path of the above lemmas *)
lemma test8 a x b m n :
  n <> a =>
  fadd (fadd (fmul a x) b) m = fmul n x <=> fdiv (fadd b m) (fsub n a) = x.
proof. by move => H; rewrite test5 // test6 // test7 //. qed.

(** Exponentiation properties *)
(** Any field element raised to the 0 power is 1 *)
axiom pow0 (x:t): fexp x 0 = fone.
(** Inductive definition of exponentiation *)
axiom powS (x:t) (n:int): Int.(<=) 0 n => fexp x (Int.(+) n 1) = fmul x (fexp x n).
(** Base case of exponentiation: any field element raise to the 1 power yields the same field
    element as output *)
lemma pow1 (x:t) : fexp x 1 = x.
proof. by (have ->: 1 = 0 + 1 by done); by rewrite powS // pow0 mulf1. qed.  
(** Exponentiation with negative exponents *)
axiom powN (x:t) (n:int): Int.(<=) 0 n => fexp x (Int.([-]) n) = finv (fexp x n).

(** Conversion from integer to finite field element *)
op ofint : int -> t.
(** Conversion from finite field element to integer *)
op toint : t -> int.

(** Conversion between integer and finite field properties *)
(** Converting the integer 0 yields the finite field element **fzero** *)
axiom ofint0: ofint 0 = fzero.
(** Inductive definition of from integer conversion *)
axiom ofintS (n:int): Int.(<=) 0 n => ofint (Int.(+) n 1) = fadd (ofint n) fone.
(** Conversion of negative integers *)
axiom ofintN (n:int): ofint (Int.([-]) n) = fumin (ofint n).

(** Conversion of negative integers *)
axiom toint_bounded (x:t): 0 <= toint x < q.
(** Cancelation property: converting a field element to an integer and then back to a field
    element yields the original field element *)
axiom oftoint (x:t): ofint (toint x) = x.

require IntDiv.

(** Conversion modulo **q**. An integer is converted into a field element by obtaining its 
    remainder modulo **q** *)
axiom toofint_mod (x:int): toint (ofint x) = IntDiv.(%%) x q.

(** 
  Declaring the ring and field structure 

  The above types, operations, axioms and lemmas can be used to define a ring and a field 
  structure.
*)
require AlgTactic.
require Ring.

(** Declares a ring structure *)
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

(** Declares a field structure *)
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

(** Auxiliar lemma, proving that [x - x = 0] *)
lemma nosmt subff (x:t): (fsub x x) = fzero
by ringeq.

(** Auxiliar lemma, proving that [0 + x = x] *)
lemma nosmt add0f (x:t): fadd fzero x = x
by ringeq.

(** Auxiliar lemma, proving that [0x = 0] *)
lemma nosmt mulf0 (x:t): fmul x fzero = fzero
by ringeq.

lemma nosmt mul0f (x:t): fmul fzero x = fzero
by ringeq.

(** Auxiliar lemma, proving that [1x = x] *)
lemma nosmt mul1f (x:t): fmul fone x = x
by ringeq.

(** Auxiliar lemma, proving that [-xy = -(xy)] *)
lemma nosmt mulNf (x y:t): fmul (fumin x) y = fumin (fmul x y)
by ringeq.

(** Auxiliar lemma, proving that [y . -x = - (yx)] *)
lemma nosmt mulfN (x y:t): fmul y (fumin x) = fumin (fmul y x)
by ringeq.

(** Auxiliar lemma, proving that [-(-x) = x] *)
lemma nosmt oppK (x:t): fumin (fumin x) = x
by ringeq.

(** Auxiliar lemma, proving that [xy - xz = x (y - z)] *)
lemma nosmt mulfNl (x y z:t): fsub (fmul x y) (fmul x z) = fmul x (fsub y z)
by ringeq.

(** Auxiliar lemma, proving that [-1x = -x] *)
lemma nosmt mulN1f (x:t): fmul (fumin fone) x = fumin x
by ringeq.

(** Auxiliar lemma, proving that [-x + -y = - (x + y)] *)
lemma nosmt oppfD (x y:t): fadd (fumin x) (fumin y) = fumin (fadd x y)
by ringeq.

(** Auxiliar lemma, proving that all field elements are bigger than or equal to 0 *)
lemma nosmt toint_pos (x:t): 0 <= toint x
by smt.

(** Auxiliar lemma, proving that all field elements are smaller than **q** *)
lemma nosmt toint_lt (x:t): toint x < q
by smt.

(** Auxiliar lemma, proving that all field elements are smaller than or equal to **q - 1** *)
lemma nosmt toint_le (x:t): toint x <= q - 1
by smt.

(** Auxiliar lemma, proving that if an integer is between the range [0; q[, then converting
    it to a finite field and then back to an integer yields the original value *)
lemma nosmt toofint (x:int): 0 <= x => x < q => toint (ofint x) = x.
proof. by move=> Hp Hlt; rewrite toofint_mod IntDiv.modz_small /#. qed.

(** Converting the integer 1 yields the finite field element **fone** *)
lemma nosmt ofint1_: ofint 1 = fone by smt.

(** 
  Probability distribution over finite field elements 

  The **FDistr** theory defines a uniform distribution that samples elements of the field
  with probability **1/q** 
*)
theory FDistr.

  require Distr.

  require import Real.

  (** Probability distribution over elements of the field *)
  op dt: t distr.

  (** The field probability distribution is complete *)
  axiom dt_fu: Distr.is_full dt.

  (** Sampling probability of **1/q** *)
  axiom dt1E: forall (s:t), Distr.mu1 dt s = (1%r/q%r)%Real.

  axiom dt2E: forall (a b c :t), mu dt (fun x => fadd (fadd (fmul (fexp x 2) a) (fmul x b)) c = fzero) = (2%r/q%r)%Real.

  (** The field probability distribution is defined for all values of the field *)
  axiom dt_ll: Distr.is_lossless dt.

  (** The field probability distribution is finite and uniform *)
  lemma dt_funi: Distr.is_funiform dt.
  proof. by move=> ??;rewrite !dt1E. qed.

  hint exact random : dt_fu dt_ll dt_funi.

end FDistr.

(* ==================================================================== *)
(** Field utils *)
(** Auxiliar lemma, proving that [yx + zx = (y + z)x] *)
lemma mulfDr : forall (x y z : t), fadd (fmul y x) (fmul z x) = fmul (fadd y z) x.
proof. by move => x y z; ringeq. qed.

(* -------------------------------------------------------------------- *)
(** Auxiliar lemma, proving that [(x + y) * (w + z) = xw + xz + yw + yz] *)
lemma binom_mult (x y w z : t) :
  fmul (fadd x y) (fadd w z) = fadd (fadd (fadd (fmul x w) (fmul x z)) (fmul y w)) (fmul y z).
proof. by rewrite -mulfDr -!mulfDl addA. qed.

(* -------------------------------------------------------------------- *)
(** Auxiliar lemma, proving that [x ^ (n + n') = x^n * x^n'] *)
lemma powEA (x:t) (n:int) (n':int): 
  Int.(<=) 0 n => Int.(<=) 0 n' => 
  fexp x (Int.(+) n n') = fmul (fexp x n) (fexp x n').
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
(** Auxiliar lemma, proving that [x/z + y/z = (x + y)/z] *)
lemma same_divisor_add : forall (x y z : t), 
  fadd (fdiv x z) (fdiv y z) = fdiv (fadd x y) z by smt.

(* -------------------------------------------------------------------- *)
(** Auxiliar lemma, proving that [x/z - y/z = (x - y)/z] *)
lemma same_divisor_sub : forall (x y z : t), z <> fzero => 
  fsub (fdiv x z) (fdiv y z) = fdiv (fsub x y) z.
proof. by progress; rewrite !div_def (mulC x _) (mulC y _) mulfNl mulC. qed.

(* -------------------------------------------------------------------- *)
(** Auxiliar lemma, proving that the subtraction of two elements different than zero never yields
    zero as output *)
lemma diff_sub_zero : forall (x y : t), x <> y => fsub x y <> fzero.
proof.
  progress.
  + case (fsub x y = fzero) => ?.
    by have ?: x = y by ringeq; rewrite addC -sub_def ofint0.
  by done.
qed.

(* -------------------------------------------------------------------- *)
(** Auxiliar lemma, proving that zero divided by anything yields zero *)
lemma zero_div x : fdiv fzero x = fzero.
proof. by rewrite div_def mulC mulf0. qed.

(* -------------------------------------------------------------------- *)
(** Auxiliar lemma, proving that [x/x = 1] *)
lemma divff (x : t) : x <> fzero => fdiv x x = fone.
proof. by move => ?; rewrite div_def mulfV. qed.

(* -------------------------------------------------------------------- *)
(** Auxiliar lemma, proving that [0^x = 0] *)
lemma zero_pow (x : int) : 0 < x => fexp fzero x = fzero.
proof.
  progress.
  have H0 : 0 <= x by smt().
  move : H.
  move : H0; elim x => /> *.
  by rewrite powS // mulC mulf0.
qed.

(* -------------------------------------------------------------------- *)
(** Auxiliar lemma, proving that equation [y/x = z] can be transformed into [y = zx] *)
lemma div_mul_eq (x y w z a : t) : 
  x <> fzero =>
  (fdiv y x = z) = (y = fmul z x).
proof. by move => *; smt. qed.

(* -------------------------------------------------------------------- *)
(** Auxiliar lemma, proving that equation [(x - y) / (z - w) = a] can be transformed into 
    [x - y = a(z - w)] *)
lemma sub_div_mul_eq (x y w z a : t) : 
  fsub z w <> fzero =>
  (fdiv (fsub x y) (fsub z w) = a) = ((fsub x y) = fmul a (fsub z w)). 
proof. by move => *; smt. qed.
