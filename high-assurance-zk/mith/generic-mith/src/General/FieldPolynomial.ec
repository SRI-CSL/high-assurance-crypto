require import Int Distr List.

from General require import ListExt PrimeField Utils.

(* ==================================================================== *)
(** Type definition. Polynomials as list of monomials *)
type coeficient = t.
type exponent = int.

type monomial = {
  coef : coeficient;
  expo : exponent
}.

type polynomial = monomial list.

(* -------------------------------------------------------------------- *)
axiom expo_ge0 (m : monomial) : 0 <= m.`expo.

(* ==================================================================== *)
(* Non zeros *)
op non_zeros_polynomial (p : polynomial) : bool = forall x, x \in p => x.`expo <> 0 => x.`coef <> fzero.

(* ==================================================================== *)
(* Monomial evaluation *)
op meval (x:coeficient) (m : monomial) = fmul m.`coef (fexp x m.`expo).

(* -------------------------------------------------------------------- *)
lemma meval_zero x m : m.`coef = fzero => meval x m = fzero.
proof. by progress; rewrite /meval H; ringeq. qed.

(* ==================================================================== *)
(* Polynomial evaluation *)
op eval (x:coeficient) p =
  with p = [] => fzero
  with p = m :: p' => fadd (meval x m) (eval x p').

(* ==================================================================== *)
(* Polynomial evaluation *)
op get_coeficient (x:exponent) p z =
  with p = [] => z
  with p = m :: p' => 
    if m.`expo = x then m.`coef
    else get_coeficient x p' z.

(* -------------------------------------------------------------------- *)
lemma eval_zeroN p : count (fun x => x.`expo = 0) p = 0 => eval fzero p = fzero.
proof.
  rewrite -count_eq0 hasPn; progress.
  move : H; elim p => //.
  by progress; rewrite /meval; smt.
qed.

(* -------------------------------------------------------------------- *)
lemma eval_zeroE p : count (fun x => x.`expo = 0) p = 1 => eval fzero p = get_coeficient 0 p fzero.
proof.
  elim p => //.
  progress; move : H0; case (x.`expo = 0) => ?.
    rewrite /meval /b2i /=; progress.
    have ?: count (fun (x0 : monomial) => x0.`expo = 0) l = 0 by smt().
    by rewrite eval_zeroN //; smt. 
  by rewrite /b2i /=; progress; rewrite /meval /=; smt.
qed.

(* -------------------------------------------------------------------- *)
lemma eval_zero_mem p : 
  count (fun x => x.`expo = 0) p = 1 => 
  {| coef = eval fzero p ; expo = 0 |} \in p.
proof.
  elim p => //.
  progress; move : H0; case (x.`expo = 0) => H0.
    by rewrite /b2i /=; progress; smt.
  rewrite /b2i /=; progress.
  rewrite /meval /= zero_pow //=; first by smt(expo_ge0).
  by rewrite !mulf0 !add0f; right; rewrite H.  
qed.

(* ==================================================================== *)
(** Polynomial membership *)
op mem (pt : (coeficient * coeficient)) p = eval (fst pt) p = (snd pt).

(* ==================================================================== *)
(** Equality class *)
op (==) p1 p2 = forall x, eval x p1 = eval x p2.

(* -------------------------------------------------------------------- *)
lemma eq_class_implication p1 p2 :
  p1 = p2 => p1 == p2.
proof. by move => ->. qed.

(* -------------------------------------------------------------------- *)
lemma equal_sym p : p == p.
proof. by rewrite /(==) => *. qed.

(* -------------------------------------------------------------------- *)
lemma equal_comm p1 p2 : p1 == p2 => p2 == p1.
proof. by rewrite /(==); progress; rewrite H. qed.

(* -------------------------------------------------------------------- *)
lemma equal_assoc p1 p2 p3 : p1 == p2 => p2 == p3 => p1 == p3.
proof. by rewrite /(==); progress; rewrite H H0. qed.

(* ==================================================================== *)
(** Zero monomial *)
op mzero = {| coef = fzero; expo = 0 |}.

(* -------------------------------------------------------------------- *)
lemma meval_mzero x : meval x mzero = fzero.
proof. by rewrite /meval /mzero /= mulC mulf0. qed.

(* ==================================================================== *)
(** Zero polynomial *)
op pzero : polynomial = [].

(* -------------------------------------------------------------------- *)
lemma eval_zero x : eval x pzero = fzero.
proof. by rewrite /pzero. qed.

(* -------------------------------------------------------------------- *)
lemma zero_mzero_eq : pzero == [mzero].
proof. 
  rewrite /(==) /pzero /mzero /= /meval /= => *. 
  by rewrite pow0 mulf1 addf0.
qed.

(* ==================================================================== *)
(** One monomial *)
op mone = {| coef = fone; expo = 0 |}.

(* -------------------------------------------------------------------- *)
lemma meval_mone x : meval x mone = fone.
proof. by rewrite /meval /mone /= pow0 mulf1. qed.

(* ==================================================================== *)
(** One polynomial *)
op pone = [mone].

(* -------------------------------------------------------------------- *)
lemma eval_one x : eval x pone = fone.
proof. by rewrite /pone /mone /eval /= /meval /= pow0 mulf1 addf0. qed.

(* -------------------------------------------------------------------- *)
lemma eval_cons m p x : eval x (m :: p) = fadd (meval x m) (eval x p).
proof. by done. qed.

(* -------------------------------------------------------------------- *)
lemma eval_cat_comm p1 p2 x : eval x (p1 ++ p2) = eval x (p2 ++ p1).
proof.
  elim: p1 p2; first by progress; rewrite cats0.
  progress; elim p2; first by progress; rewrite cats0.
  simplify; progress.
  rewrite (H (x1 :: l0)) (eval_cons x1 ( l0 ++ l) x) -H0.
  rewrite addA addC (addC (meval x x0) (meval x x1)) addA addC addA.
  by rewrite H0 -H H0 addC.
qed.

(* -------------------------------------------------------------------- *)
lemma eval_cat (x : t) (p1 p2 : polynomial) : eval x (p1 ++ p2) = fadd (eval x p1) (eval x p2).
proof.
  elim p1 p2 => /=; first by move => ?; rewrite add0f.
  progress.
  elim p2 => /=; first by rewrite eval_cat_comm /=; ringeq.
  progress.
  by rewrite H /=; ringeq.
qed.

(* -------------------------------------------------------------------- *)
lemma eval_rev p x : eval x p = eval x (rev p).
proof.
elim p => //=.
move => m p; progress.
rewrite rev_cons.
have ->: rcons (rev p) m = rev p ++ [m] by smt(@List).
rewrite eval_cat.
rewrite -H.
simplify.
by ring.
qed.

(* -------------------------------------------------------------------- *)
lemma one_neq0 : pone <> pzero.
proof. by rewrite /pone /pzero. qed.

(* -------------------------------------------------------------------- *)
lemma expo_diff_count p :
  0 < size p =>
  (forall i, 0 <= i < size p => (nth mzero p i).`expo = size p - 1 - i) =>
  count (fun (x : monomial) => x.`expo = 0) p = 1.
proof.
  elim p => //.
  progress; case (l = []) => H2.
    move : H1; rewrite H2 /=; progress.
    by move : (H1 0) => /=; progress; rewrite H3 /= b2i1.
  case (x.`expo = 0) => H3.
    by rewrite /b2i /=; move : (H1 x.`expo); rewrite H3 H0 /=; progress; smt(@List).
  by rewrite /b2i H /= /#.
qed.

(* ==================================================================== *)
op update (p : polynomial) (e : int) (x : t) : polynomial = 
  map (fun m => if m.`expo = e then {| coef = x ; expo = e |} else m) p.

(* -------------------------------------------------------------------- *)
lemma update_id (p : polynomial) (e : int) (x : t) :
  update (update p e x) e x = (update p e x).
proof. 
  rewrite /update -map_comp /(\o) //=.
  rewrite -eq_in_map => m; progress.
  (case (m.`expo = e); first by done); progress.
  by rewrite H0 /=.
qed.

(* -------------------------------------------------------------------- *)
lemma updateK (p : polynomial) (e : int) (x : t) :
  count (fun (x : monomial) => x.`expo = e) p = 1 =>
  {| coef = x ; expo = e |} \in p =>
  update p e x = p.
proof. 
  move=> /> H H0; move : H H0; elim p => //.
  progress; case ({| coef = x; expo = e; |} = x0) => H2.
    rewrite /update /= /meval //=.
    move : H0; rewrite /b2i.
    have ->: x0.`expo = e by smt().
    progress.
    have ->: map (fun (m : monomial) => if m.`expo = e then {| coef = x; expo = e; |} else m) l = l.
      have ->: map (fun (m : monomial) => if m.`expo = e then {| coef = x; expo = e; |} else m) l = l <=> map (fun (m : monomial) => if m.`expo = e then {| coef = x; expo = e; |} else m) l = map (fun m => m) l by rewrite map_id.
      by rewrite -eq_in_map => m; progress; smt(@List).
    by smt().
  have H3: x0.`expo = e <=> false by smt(@List).
  rewrite /update /=.
  move : H0; rewrite /b2i.
  rewrite H3 /=; progress.
  have ->: map (fun (m : monomial) => if m.`expo = e then {| coef = x; expo = e; |} else m) l = update l e x by rewrite /update.
  by rewrite H => // /#.
qed.

(* -------------------------------------------------------------------- *)
lemma update_eval (p : polynomial) (e : int) (x : t) :
  count (fun (x : monomial) => x.`expo = e) p = 1 =>
  {| coef = x ; expo = e |} \in p =>
  update p e x == p.
proof. by progress; rewrite updateK //. qed.

(* -------------------------------------------------------------------- *)
lemma size_update (p : polynomial) (e : int) (x : t) :
  size (update p e x) = size p.
proof. by elim p; progress; case (x0.`expo = e) => ? //= /#. qed.

(* -------------------------------------------------------------------- *)
lemma update_exp (p : polynomial) (e : int) (x : t) :
  forall i, 0 <= i < size p => (nth mzero (update p e x) i).`expo = (nth mzero p i).`expo.
proof. by elim p; progress; case (x0.`expo = e) => ? //= /#. qed.

(* -------------------------------------------------------------------- *)
lemma eval_update0 (p : polynomial) (x : t) :
  count (fun (x : monomial) => x.`expo = 0) p = 1 =>
  eval fzero (update p 0 x) = x.
proof.
  elim p; progress; case (x0.`expo = 0) => H1 //=.
    rewrite /update.
    move : H0; rewrite /b2i H1 /=; progress.
    rewrite /meval H1 /= pow0 mulf1 /=.
    have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = x; expo = 0; |} else m) l = l.
      have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = x; expo = 0; |} else m) l = l <=> map (fun (m : monomial) => if m.`expo = 0 then {| coef = x; expo = 0; |} else m) l = map (fun m => m) l by rewrite map_id.
      by rewrite -eq_in_map => m; progress; smt(@List).
    by rewrite eval_zeroN 1:/# addf0.
  move : H0; rewrite /b2i.
  rewrite H1 /=; progress. 
  have ->: eval fzero (update (x0 :: l) 0 x) = eval fzero (update l 0 x).
    by rewrite /update /= /meval H1 /= zero_pow 1:smt mulf0 add0f.
  by rewrite H //.    
qed.

(* -------------------------------------------------------------------- *)
lemma eval_updateN p e x y :
  count (fun (x : monomial) => x.`expo = e) p = 0 =>
  eval y (update p e x) = eval y p.
proof.
elim p.
rewrite /update /=.
done.
move => m p; progress.
have ->: update (m :: p) e x = (if m.`expo = e then {| coef = x ; expo = e |} else m) :: update p e x.
by rewrite /update map_cons.
rewrite eval_cons.
smt.
qed.

(* -------------------------------------------------------------------- *)
op get_monomial (e : exponent) (p : polynomial) : monomial =
  with p = [] => mzero
  with p = m :: ms => 
    if m.`expo = e then m
    else get_monomial e ms.

lemma get_monomial_cat_r e p p' :
  count (fun (x : monomial) => x.`expo = e) p = 0 =>
  get_monomial e (p ++ p') = get_monomial e p'.
proof.
elim p.
simplify.
done.
move => m p; progress.
smt(@List).
qed.

lemma get_monomial_cat_l e p p' :
  count (fun (x : monomial) => x.`expo = e) p' = 0 =>
  get_monomial e (p ++ p') = get_monomial e p.
proof.
elim : p p'.
simplify.
progress.
move : H.
elim p'. done.
progress.
smt.
move => m p; progress.
smt.
qed.

lemma get_monomial_rev e p :
  count (fun (x : monomial) => x.`expo = e) p = 1 =>
  get_monomial e p = get_monomial e (rev p).
proof.
elim p.
simplify.
done.
move => m p; progress.
case (m.`expo = e); progress.
rewrite rev_cons.
have ->: rcons (rev p) m = rev p ++ [m] by smt(@List).
rewrite get_monomial_cat_r.
smt.
simplify.
done.
rewrite rev_cons.
have ->: rcons (rev p) m = rev p ++ [m] by smt(@List).
rewrite get_monomial_cat_l.
smt().
smt().
qed. 

lemma eval_update p e x y :
  count (fun (x : monomial) => x.`expo = e) p = 1 =>
  eval y (update p e x) = fadd (fsub (eval y p) (meval y (get_monomial e p))) (meval y ({| coef = x ; expo = e|})).
proof. 
elim p.
simplify.
done.
move => m p; progress.
have ->: update (m :: p) e x = (if m.`expo = e then {| coef = x ; expo = e |} else m) :: update p e x.
by rewrite /update map_cons.
case (m.`expo = e) => H1.
have ->: (eval y (update p e x)) = (eval y p).
rewrite eval_updateN.
smt().
done.
by ringeq.
rewrite H.
smt().
by ringeq.
qed.

(* -------------------------------------------------------------------- *)
lemma get_monomial0 p :
  count (fun (x : monomial) => x.`expo = 0) p = 1 =>
  get_monomial 0 p = {| coef = eval fzero p ; expo = 0 |}.
proof.
elim p.
smt.
move => m p.
progress.
smt.
qed.

(* ==================================================================== *)
(** Degree *)
(*op degree' p max =
  with p = [] => max
  with p = x :: xs => if max < x.`expo then degree' xs x.`expo
                      else degree' xs max.
op degree p = degree' p 0.*)
(*op degree p = (head mzero p).`expo.*)

op degree p = foldr (fun m acc => if acc <= m.`expo then m.`expo else acc) 0 p.

(* -------------------------------------------------------------------- *)
lemma degree_pzero : degree pzero = 0.
proof. by rewrite /pzero /degree /= /mzero /=. qed.

(* -------------------------------------------------------------------- *)
lemma degree_one : degree pone = 0.
proof. by rewrite /pone /mone /degree /=. qed.

(* -------------------------------------------------------------------- *)
lemma degree_ge0 p : 0 <= degree p.
proof.
  elim p; first by rewrite /degree /= /mzero /=.
  by progress; rewrite /degree /= /#.
qed.

(* -------------------------------------------------------------------- *)
lemma degree_upper_bound : 
  forall p y, 0 <= y => all (fun (m' : monomial) => m'.`expo <= y) p => degree p <= y.
proof.
  move => p y hy.
  elim p => /=; first by rewrite /degree /= /mzero /=.
  by move => /> /#.
qed.

(* -------------------------------------------------------------------- *)
lemma degree_update0 p x : degree (update p 0 x) = degree p.
proof. by elim p => /=; by rewrite /degree /= /mzero /= /#. qed.

(* -------------------------------------------------------------------- *)
lemma size_update0 p x : size (update p 0 x) = size p.
proof. by elim p => /=; by rewrite /mzero /= /#. qed.

(* -------------------------------------------------------------------- *)
lemma update_expo p x : 
  forall i, 0 <= i < size p => (nth mzero (update p 0 x) i).`expo = (nth mzero p i).`expo.
proof.
  move => i /> H; elim p => /=; first by rewrite /update /=.
  progress.
  case (i = 0); progress; first by rewrite /update /= /#. 
  rewrite /update (nth_map witness mzero) //=.
  by rewrite H2 /=; smt. 
qed.

(* -------------------------------------------------------------------- *)
lemma degree_max_expo (p : polynomial) :
  forall m, m \in p => m.`expo <= degree p. 
proof. by move => m; elim p => /> *; rewrite /degree /#. qed.

(* ==================================================================== *)
(** Monomial addition *)
op madd m1 m2 = {| coef = fadd m1.`coef m2.`coef; expo = m1.`expo |}.

(* -------------------------------------------------------------------- *)
lemma eval_madd x m1 m2 : 
  m1.`expo = m2.`expo => 
  meval x (madd m1 m2) = fadd (meval x m1) (meval x m2).
proof. 
  progress; rewrite /meval /madd /= !H.
  rewrite mulC -mulfDl. 
  rewrite (mulC (fexp x m2.`expo) (m1.`coef)); congr.
  by rewrite mulC.
qed.

(* -------------------------------------------------------------------- *)
lemma madd_comm x m1 m2 :
  m1.`expo = m2.`expo => 
  meval x (madd m1 m2) = meval x (madd m2 m1).
proof. by progress; rewrite eval_madd // addC -eval_madd // H. qed.

(* -------------------------------------------------------------------- *)
lemma madd_expo m1 m2 : (madd m1 m2).`expo = m1.`expo by rewrite /madd /=.

(* ==================================================================== *)
(** Monomial polynomial addition *)
op mpadd (m : monomial) p = 
  with p = [] => [m]
  with p = m' :: p' => 
    if m.`expo = m'.`expo then madd m m' :: p'
    else 
      if m'.`expo < m.`expo then m :: p
      else m' :: mpadd m p'.

(* -------------------------------------------------------------------- *)
lemma eval_mpadd x m p : 
  eval x (mpadd m p) = fadd (meval x m) (eval x p).
proof.
  rewrite /meval. 
  elim p => /=; first by rewrite /meval.
  progress.
    + case (m.`expo = x0.`expo) => H0.
      + by rewrite /madd /meval H0 addA /=; ringeq.
    + case (x0.`expo < m.`expo) => H1.
      + by rewrite /meval.
    + by rewrite H !addA; congr; rewrite addC.
qed.

(* -------------------------------------------------------------------- *)
lemma degree_mpadd m p : 
  degree (mpadd m p) = max (m.`expo) (degree p).
proof.
  rewrite /degree; elim p => /=.
    + rewrite /mzero /= /max.
      have aux : 0 <= m.`expo => !(m.`expo < 0) by smt().
      by (rewrite aux /=; first by rewrite expo_ge0); smt.
  progress.
    + case (m.`expo = x.`expo) => H0.
      + by rewrite /madd /= H0 /max /= /#.
    + case (x.`expo < m.`expo) => H1.
      + by rewrite /max /#. 
    + by rewrite /max /#.
qed.

(* ==================================================================== *)
(** Polynomial addition *)
op add (p1 p2 : polynomial) = 
  with p1 = [], p2 = [] => []
  with p1 = m1 :: p1', p2 = [] => p1
  with p1 = [], p2 = m2 :: p2' => p2
  with p1 = m1 :: p1', p2 = m2 :: p2' =>
    if m1.`expo = m2.`expo then madd m1 m2 :: add p1' p2'
    else
      if m1.`expo < m2.`expo then m2 :: add p1 p2'
      else m1 :: add p1' p2.

(* -------------------------------------------------------------------- *)
lemma size_add p1 p2 : 
  size p1 = size p2 =>
  (forall i, 0 <= i < size p1 => (nth mzero p1 i).`expo = (nth mzero p2 i).`expo) =>
  size (add p1 p2) = size p1.
proof.
  elim p1 p2; first by progress; have ->: p2 = [] by rewrite -size_eq0 => /#.
  progress; move : H1 H0; elim p2; first by smt().
  progress.
  have ->: x.`expo = x0.`expo by move : (H1 0) => /=; smt(size_ge0). 
  by simplify; rewrite H => /#. 
qed.

(* -------------------------------------------------------------------- *)
lemma add_expos p1 p2 : 
  size p1 = size p2 =>
  (forall i, 0 <= i < size p1 => (nth mzero p1 i).`expo = (nth mzero p2 i).`expo) =>
  (forall i, 0 <= i < size p1 => (nth mzero (add p1 p2) i).`expo = (nth mzero p1 i).`expo).
proof.
  elim p1 p2; first by progress; have ->: p2 = [] by rewrite -size_eq0 => /#.
  progress; move : H1 H0; elim p2; first by smt().
  progress.
  have ->: x.`expo = x0.`expo by move : (H1 0) => /=; smt(size_ge0). 
  simplify; case (i = 0) => ?; first by smt().
  by rewrite H => /#. 
qed.

(* -------------------------------------------------------------------- *)
lemma add_pzeror (x : polynomial): add pzero x = x.
proof. by case x => /=. qed.

(* -------------------------------------------------------------------- *)
lemma add_pzerol (x : polynomial): add x pzero = x.
proof. by case x => /=; rewrite /pzero /=. qed.

(* -------------------------------------------------------------------- *)
lemma eval_add x p p' : 
  eval x (add p p') = fadd (eval x p) (eval x p').
proof.
  elim: p p'; first by progress; rewrite add_pzeror add0f. 
  progress; elim p' => /=; first by rewrite addf0.
  progress.
    + case (x0.`expo = x1.`expo) => H1.
      + rewrite /madd /meval /= H1. rewrite -(mulfDr (fexp x x1.`expo) _ _).
        rewrite -(addA _ (eval x l) _) (addC (eval x l) _).
        rewrite -(addA _ (eval x l0) _) (addC (eval x l0) _).
        by rewrite !addA H addA.
    + case (x0.`expo < x1.`expo) => ?.
      + by rewrite H0 !addA; congr; rewrite -addA addC.
    + by rewrite H /= !addA.
qed.

(* -------------------------------------------------------------------- *)
lemma add_comm (x y : polynomial): (add x y) == (add y x).
proof. by rewrite /(==) /add => c; rewrite !eval_add addC. qed.

(* -------------------------------------------------------------------- *)
lemma add_assoc (x y z : polynomial): add x (add y z) == add (add x y) z.
proof. by rewrite /(==) /add => c; rewrite !eval_add addA. qed.

(* -------------------------------------------------------------------- *)
lemma equal_add p1 p2 p3 : p2 == p3 => add p1 p2 == add p1 p3.
proof. by rewrite /(==); progress; rewrite !eval_add H. qed. 

(* -------------------------------------------------------------------- *)
lemma degree_add (p1 p2 : polynomial) :
  degree (add p1 p2) = max (degree p1) (degree p2).
proof.
  elim: p1 p2.
    + progress; rewrite degree_pzero add_pzeror /max.
      + case (0 < degree p2) => ? //.
        have ?: 0 <= degree p2 by apply degree_ge0.
        by smt().
  progress; elim p2.
    + rewrite add_pzerol degree_pzero /max.
    + case (degree (x :: l) < 0) => H0 //.
      have H1: 0 <= degree (x :: l) by apply degree_ge0.
      by smt().
  progress; rewrite /degree /=.
    + case (x.`expo = x0.`expo) => H1.
      + by rewrite /madd /= H1 /max /= /#.
    + case (x.`expo < x0.`expo) => ?.
      + by rewrite /max /= /#.
    + by rewrite /max /#.
qed.

(* -------------------------------------------------------------------- *)
lemma add_same_expos (p p' : polynomial) e :
  (forall m, m \in p => m.`expo <> e) =>
  (forall m, m \in p' => m.`expo <> e) =>
  (forall m, m \in add p p' => m.`expo <> e).
proof.
elim p p'.
progress.
smt.
progress.
move : H1 H2. 
elim p'.
progress.
smt.
progress.
move : H3.
case (x.`expo = x0.`expo); progress.
case (m = madd x x0); progress.
rewrite madd_expo.
smt.
rewrite (H l0).
smt.
smt.
smt.
done.
move : H4.
case (x.`expo < x0.`expo); progress.
smt.
case (m = x); progress.
smt.
rewrite (H (x0 :: l0)).
smt.
smt.
smt.
done.
qed.

lemma update_add p p' x s s':
  (count (fun (x : monomial) => x.`expo = 0) p = 1) =>
  (count (fun (x : monomial) => x.`expo = 0) p' = 1) =>
  eval x (update (add p p') 0 (fadd (eval fzero (update p 0 s)) (eval fzero (update p' 0 s')))) =
  eval x (add (update p 0 s) (update p' 0 s')).
proof.
  progress; rewrite !eval_update0 // eval_add.
  move : H0 H; elim p p'; progress.
  move : H1 H0; elim p'; first by smt().
  progress; case (x0.`expo = x1.`expo); progress.
    case (x0.`expo = 0); progress. 
      move : H0 H1 H2; rewrite -H3 H4 /b2i /=; progress.
      rewrite /update /= madd_expo H4 /= /meval !pow0 !mulf1 /meval /=.
      have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = fadd s s'; expo = 0; |} else m) (add l l0)) = eval x (update (add l l0) 0 (fadd s s')) by rewrite /update.
      have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l) = eval x (update l 0 s) by rewrite /update.
      have ->: x1.`expo = 0 by smt().
      simplify; rewrite !pow0 !mulf1.
      have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0) = eval x (update l0 0 s') by rewrite /update.
      have ->: update l 0 s = l.

rewrite /update.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l = l <=> map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l = map (fun x => x) l.
progress.
rewrite -eq_in_map /(\o) /=; progress.
smt(@List).
smt(@List).
rewrite -eq_in_map; progress.
smt(@List).

      have ->: update l0 0 s' = l0.

rewrite /update.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = l0 <=> map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = map (fun x => x) l0.
progress.
rewrite -eq_in_map /(\o) /=; progress.
smt(@List).
smt(@List).
rewrite -eq_in_map; progress.
smt(@List).

have ->: update (add l l0) 0 (fadd s s') = add l l0.
rewrite /update.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = fadd s s'; expo = 0; |} else m) (add l l0) = add l l0 <=> map (fun (m : monomial) => if m.`expo = 0 then {| coef = fadd s s'; expo = 0; |} else m) (add l l0) = map (fun x => x) (add l l0).
by rewrite map_id.
rewrite -eq_in_map; progress.

move : (add_same_expos l l0 0).
have : (forall (m : monomial), m \in l => m.`expo <> 0).
have : count (fun (x : monomial) => x.`expo = 0) l = 0 by smt().
rewrite -count_eq0.
smt(@List).

have : (forall (m : monomial), m \in l0 => m.`expo <> 0).
have : count (fun (x : monomial) => x.`expo = 0) l0 = 0 by smt().
rewrite -count_eq0.
smt(@List).
smt().

rewrite eval_add.
ring.


      move : H0 H1 H2; rewrite -H3 H4 /b2i /=; progress.
rewrite /update /=.
rewrite /meval /madd.
have ->: {| x0 with  coef = fadd x0.`coef x1.`coef; |}.`expo = 0 <=> false by smt().
simplify.
rewrite H4 /=.
have ->: x1.`expo = 0 <=> false by smt().
simplify.
have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = fadd s s'; expo = 0; |} else m) (add l l0)) = eval x (update (add l l0) 0 (fadd s s')).
by rewrite /update.
have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l) = eval x (update l 0 s) by rewrite /update.
have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0) = eval x (update l0 0 s') by rewrite /update.
rewrite (H l0).
done.
done.
rewrite H3.
ring.

  case (x0.`expo < x1.`expo); progress.
    case (x0.`expo = 0); progress. 
      move : H0 H1 H2. rewrite H5 /=. 
      have ->: x1.`expo = 0 <=> false by smt().
      rewrite /b2i /=; progress.
      rewrite /update /=. 
      have ->: x1.`expo = 0 <=> false by smt(). 
      simplify. (*rewrite /meval. !pow0 !mulf1 /meval /=. *)
      have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = fadd s s'; expo = 0; |} else m) (add (x0 :: l) l0)) = eval x (update (add (x0 :: l) l0) 0 (fadd s s')) by rewrite /update.
      have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l) = eval x (update l 0 s) by rewrite /update.
      rewrite H5 /=.
      rewrite /meval /= !pow0 !mulf1.
      have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0) = eval x (update l0 0 s') by rewrite /update.
      have ->: update l 0 s = l.

rewrite /update.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l = l <=> map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l = map (fun x => x) l.
progress.
rewrite -eq_in_map /(\o) /=; progress.
smt(@List).
smt(@List).
rewrite -eq_in_map; progress.
smt(@List).

rewrite H0.
done.
done.

rewrite eval_update.
simplify; rewrite H5 /b2i /=. done.
rewrite eval_cons.
rewrite /meval /= !H5 /= !pow0 !mulf1.
by ring.

move : H0 H1 H2.
have ->: x0.`expo = 0 <=> false by smt().
have ->: x1.`expo = 0 <=> false by smt(expo_ge0).
rewrite /b2i /=; progress.
rewrite /update /=.
have ->: x0.`expo = 0 <=> false by smt().
have ->: x1.`expo = 0 <=> false by smt(expo_ge0).
simplify.
rewrite !H0.
done.
done.

have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l) = eval x (update l 0 s). by rewrite /update /=.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = update l0 0 s' by rewrite /update /=.

rewrite /update /=.
have ->: x0.`expo = 0 <=> false by smt().
simplify.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l = update l 0 s by rewrite /update /=.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = update l0 0 s' by rewrite /update /=.
by ring.


    case (x0.`expo = 0); progress. 
      move : H0 H1 H2. rewrite H5 /=. 
      have ->: x1.`expo = 0 <=> false by smt().
      rewrite /b2i /=; progress.
      rewrite /update /=. 
      have ->: x1.`expo = 0 <=> false by smt(). 
      rewrite !H5 /=.
      simplify. (*rewrite /meval. !pow0 !mulf1 /meval /=. *)
      have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = fadd s s'; expo = 0; |} else m) (add l (x1 :: l0))) = eval x (update (add l (x1 :: l0)) 0 (fadd s s')) by rewrite /update.
      have ->: eval x (map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l) = eval x (update l 0 s) by rewrite /update.
      have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = update l0 0 s' by rewrite /update.
      rewrite /meval /= !pow0 !mulf1.

      have ->: update l 0 s = l.

rewrite /update.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l = l <=> map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l = map (fun x => x) l.
progress.
rewrite -eq_in_map /(\o) /=; progress.
smt(@List).
smt(@List).
rewrite -eq_in_map; progress.
smt(@List).

smt.

case (x1.`expo = 0); progress.

move : H0 H1 H2.
have ->: x0.`expo = 0 <=> false by smt().
rewrite H6 /=.
rewrite /b2i /=; progress.
rewrite /update /=.
have ->: x0.`expo = 0 <=> false by smt().
have ->: x1.`expo = 0 by smt().
simplify.

have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l = update l 0 s by rewrite /update /=.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = update l0 0 s' by rewrite /update /=.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = fadd s s'; expo = 0; |} else m) (add l (x1 :: l0)) = update (add l (x1 :: l0)) 0 (fadd s s') by rewrite /update /=.
rewrite /meval /= !pow0 !mulf1.

have ->: update l0 0 s' = l0.
rewrite /update.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = l0 <=> map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = map (fun x => x) l0.
progress.
rewrite -eq_in_map /(\o) /=; progress.
smt(@List).
smt(@List).
rewrite -eq_in_map; progress.
smt(@List).

rewrite (H (x1 :: l0)).
simplify => /#.
done.
rewrite /update /=.
rewrite H6 /=.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l = update l 0 s by rewrite /update /=.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = update l0 0 s' by rewrite /update /=.
rewrite /meval /= !pow0 !mulf1.
have ->: update l0 0 s' = l0.
rewrite /update.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = l0 <=> map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = map (fun x => x) l0.
progress.
rewrite -eq_in_map /(\o) /=; progress.
smt(@List).
smt(@List).
rewrite -eq_in_map; progress.
smt(@List).
by ring.

rewrite /update /=.
move : H0 H1 H2.
have ->: x0.`expo = 0 <=> false by smt().
have ->: x1.`expo = 0 <=> false by smt(expo_ge0).
rewrite /b2i /=; progress.
simplify.

have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l = update l 0 s. by rewrite /update /=.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = update l0 0 s' by rewrite /update /=.


have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = fadd s s'; expo = 0; |} else m) (add l (x1 :: l0)) = update (add l (x1 :: l0)) 0 (fadd s s') by rewrite /update /=.

rewrite (H (x1 :: l0)).
smt.
done.

rewrite /update /=.
have ->: x1.`expo = 0 <=> false by smt(expo_ge0).
simplify.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s; expo = 0; |} else m) l = update l 0 s by rewrite /update /=.
have ->: map (fun (m : monomial) => if m.`expo = 0 then {| coef = s'; expo = 0; |} else m) l0 = update l0 0 s' by rewrite /update /=.
by ring.
qed.

(* -------------------------------------------------------------------- *)
lemma count_expo_add p p' :
  count (fun (x : monomial) => x.`expo = 0) (add p p') = 
  max (count (fun (x : monomial) => x.`expo = 0) p) (count (fun (x : monomial) => x.`expo = 0) p').
proof.
  elim: p p'; progress.
    rewrite add_pzeror /max. 
    by case (0 < count (fun (x : monomial) => x.`expo = 0) p') => //; smt(@List).
  elim p'; progress.
    rewrite /b2i.
    by case (x.`expo = 0); progress; smt(@List).
  case (x.`expo = x0.`expo); progress.
    rewrite /b2i madd_expo.
    by case (x.`expo = 0); progress; rewrite -H1 H2 /= /#.
  case (x.`expo < x0.`expo); progress.
    rewrite /b2i; case (x.`expo = 0); progress.
    have ->: x0.`expo = 0 <=> false by smt().
    by smt().
  case (x0.`expo = 0); progress; first by smt.
    by smt().
  rewrite /b2i; case (x.`expo = 0); progress.
  have ->: x0.`expo = 0 <=> false by smt().
    by smt.
  case (x0.`expo = 0); progress; first by smt.
  by smt().
qed.

(* -------------------------------------------------------------------- *)
axiom sumt_map_eval (s : 'a list) (ps : ('a * polynomial) list) (xs : ('a * ('b * t)) list) x :
  uniq s => unzip1 ps = s => unzip1 xs = s =>
  sumt (map (fun (pid : 'a) => eval x (update (oget (assoc ps pid)) 0 (oget (assoc xs pid)).`2)) s) = eval x (update (foldr (fun (p : 'a * polynomial) (st : polynomial) => add st p.`2) pzero ps) 0 (sumt (map snd (map (fun x => (x, oget (assoc xs x)).`2) s)))). 

(* -------------------------------------------------------------------- *)
axiom foldr_eval_add_update (s : 'a list) (ps : ('a * polynomial) list) x :
  uniq s => unzip1 ps = s =>
  foldr (fun (pid : 'a) (z : t) => 
    fadd (eval x (update (oget (assoc ps pid)) 0 fzero)) z) fzero s =
  eval x (update (foldr (fun (p : 'a * polynomial) (st : polynomial) => add st p.`2) pzero ps) 0 fzero).

(* -------------------------------------------------------------------- *)
axiom degree_foldr_add (ps : ('a * polynomial) list) d : 
  (forall x, x \in unzip1 ps => degree (oget (assoc ps x)) = d) =>
  degree (foldr (fun (p : 'a * polynomial) (st : polynomial) => add st p.`2) pzero ps) = d.

(* -------------------------------------------------------------------- *)
axiom size_foldr_add (ps : ('a * polynomial) list) d : 
  (forall x, x \in unzip1 ps => size (oget (assoc ps x)) = d) =>
  size (foldr (fun (p : 'a * polynomial) (st : polynomial) => add st p.`2) pzero ps) = d.

(* -------------------------------------------------------------------- *)
axiom count_expos_foldr_add (ps : ('a * polynomial) list) :
  (forall x, x \in unzip1 ps => count (fun m => m.`expo = 0) (oget (assoc ps x)) = 1) =>
  count (fun (x0 : monomial) => x0.`expo = 0) (foldr (fun (p : 'a * polynomial) (st : polynomial) => add st p.`2) pzero ps) = 1.

(* -------------------------------------------------------------------- *)
axiom count_expos_add_foldr p (ps : ('a * polynomial) list) :
  (forall x, x \in unzip1 ps => count (fun m => m.`expo = 0) (oget (assoc ps x)) = 1) =>
  count (fun m => m.`expo = 0) p = 1 =>
count (fun (x0 : monomial) => x0.`expo = 0)
  (add p (foldr (fun (p : 'a * polynomial) (st : polynomial) => add st p.`2) pzero ps)) = 1.

(* -------------------------------------------------------------------- *)
axiom expos_add_foldr (ps : ('a * polynomial) list) d :
  (forall x, x \in unzip1 ps => 
    forall (i : int),
        0 <= i && i < d + 1 =>
        (nth mzero ((oget (assoc ps x))) i).`expo = d - i) => 
  (forall (i : int),
  0 <= i && i < d + 1 =>
  (nth mzero
     (foldr (fun (p : 'a * polynomial) (st : polynomial) => add st p.`2) pzero
        ps) i).`expo =
  d - i).
  
(* ==================================================================== *)
(** Monomial multiplication *)
op mmul m1 m2 = {| coef = fmul m1.`coef m2.`coef; expo = Int.(+) m1.`expo m2.`expo |}.

(* -------------------------------------------------------------------- *)
lemma mmul_expo m m' : (mmul m m').`expo = m.`expo + m'.`expo by [].

(* -------------------------------------------------------------------- *)
lemma mmul_mzeror m x : meval x (mmul mzero m) = fzero.
proof. by rewrite /mmul /meval /mzero /= mulC (mulC fzero _) !mulf0. qed.

(* -------------------------------------------------------------------- *)
lemma mmul_mzerol m x : meval x (mmul m mzero) = fzero.
proof. by rewrite /mmul /meval /mzero /= mulf0 mulC mulf0. qed.

(* -------------------------------------------------------------------- *)
lemma eval_mmul x m m' :
  meval x (mmul m m') = fmul (meval x m) (meval x m').
proof.
  rewrite /meval /mmul /=.
  case (m = mzero \/ m' = mzero); progress. 
    + rewrite powEA; first 2 by apply expo_ge0.
      rewrite !mulA; congr.
      by rewrite -mulA (mulC (m'.`coef) _) mulA.
  rewrite powEA; first 2 by apply expo_ge0.
  rewrite !mulA; congr.
  by rewrite -mulA (mulC (m'.`coef) _) mulA.
qed.

(* -------------------------------------------------------------------- *)
lemma mmulC m m' : mmul m m' = mmul m' m.
proof. by rewrite /mmul mulC addzC /=. qed.

(* ==================================================================== *)
(** Monomial polynomial multiplication *)
op mpmul m p =
  with p = [] => []
  with p = m' :: p' => mpadd (mmul m m') (mpmul m p').

(* -------------------------------------------------------------------- *)
lemma mpmul_pzero m : mpmul m pzero = pzero by done.

(* -------------------------------------------------------------------- *)
lemma mpmul_pone m : mpmul m pone = [m].
proof. by rewrite /pone /= /mmul /mone /= mulf1 /#. qed.

(* -------------------------------------------------------------------- *)
lemma eval_mpmul m p x : eval x (mpmul m p) = fmul (meval x m) (eval x p). 
proof.
  elim p => /=; first by rewrite mulf0.
  progress.
    rewrite eval_mpadd H -mulfDl; congr.
    rewrite /mmul /= /meval /= powEA; first 2 by apply expo_ge0.
    rewrite !mulA; congr.
    by rewrite -mulA (mulC (x0.`coef) _) mulA.
qed.

(* -------------------------------------------------------------------- *)
lemma mpmul_mzero p : mpmul mzero p == pzero.
proof.
  rewrite /mzero /=; elim p; progress; rewrite /(==); progress.
    + rewrite eval_mpadd /meval /= /mmul /= eval_mpmul /= /meval /= pow0 eval_zero.
      by ringeq.
qed.

(* -------------------------------------------------------------------- *)
lemma equal_mpmul p1 p2 x : p1 == p2 => mpmul x p1 == mpmul x p2.
proof.
  rewrite /(==); elim: p1 p2.
    by progress; rewrite !eval_mpmul; smt.
  by progress; rewrite !eval_mpmul; smt.
qed.

(* ==================================================================== *)
(** Polynomial multiplication *)
op mul p1 p2 =
  with p1 = [] => []
  with p1 = m :: p1' => add (mpmul m p2) (mul p1' p2).

(* -------------------------------------------------------------------- *)
lemma mul0r (x : polynomial): mul pzero x = pzero.
proof. by rewrite /pzero /=. qed.

(* -------------------------------------------------------------------- *)
lemma mul0l (x : polynomial): mul x pzero = pzero.
proof.
  rewrite /pzero; elim x => //=.
  by progress; rewrite H /=.
qed.

(* -------------------------------------------------------------------- *)
lemma mul1r (x : polynomial): mul pone x == x.
proof. 
  rewrite /pone; elim x => /=; first by rewrite equal_sym.
  progress.
    + rewrite /(==); progress. 
      rewrite add_pzerol eval_mpadd eval_mpmul /meval /mmul /mone /=. 
      have aux : forall (x : t), fmul fone x = x by progress; rewrite mulC mulf1.
      by rewrite pow0 !aux /meval.
qed.

(* -------------------------------------------------------------------- *)
lemma mul_eval_zeror p1 p2 x : eval x p2 = fzero => eval x (mul p1 p2) = fzero.
proof.
  rewrite /(==); elim: p1 p2; first by progress; rewrite mul0r eval_zero.
  by progress; rewrite eval_add H // eval_mpmul H0 mulf0 addf0.
qed.

(* -------------------------------------------------------------------- *)
lemma equal_mul p1 p2 p3 : p2 == p3 => mul p1 p2 == mul p1 p3.
proof.
  rewrite /(==); elim p1; first by progress; rewrite !mul0r eval_zero.
  by progress; rewrite !eval_add H // !eval_mpmul H0.
qed.

(* -------------------------------------------------------------------- *)
lemma eval_mul (p1 p2 : polynomial): 
  forall x, eval x (mul p1 p2) = fmul (eval x p1) (eval x p2).
proof.
  progress; elim: p1 p2; first by progress; ringeq.
  progress.
    + by rewrite eval_add H eval_mpmul mulfDr.
qed.

(* -------------------------------------------------------------------- *)
lemma mulC (x y : polynomial): mul x y == mul y x.
proof. by rewrite /(==) => x0; rewrite !eval_mul mulC. qed.

(* -------------------------------------------------------------------- *)
lemma mulA (x y z : polynomial): mul x (mul y z) == mul (mul x y) z.
proof. by rewrite /(==) => *; rewrite !eval_mul mulA. qed.

(* -------------------------------------------------------------------- *)
lemma mulDl (x y z : polynomial): mul (add x y) z == add (mul x z) (mul y z).
proof. by rewrite /(==) => *; rewrite !eval_mul !eval_add !eval_mul mulfDr. qed.

(* -------------------------------------------------------------------- *)
lemma degree_mul_pzeror (p : polynomial) : degree (mul p pzero) = 0.
proof.
  elim: p => /=; first by rewrite degree_pzero.
  by progress; rewrite degree_add H mpmul_pzero degree_pzero /max.
qed.

(* -------------------------------------------------------------------- *)
lemma degree_mul_pzerol (p : polynomial) : degree (mul pzero p) = 0.
proof. by elim: p => />. qed.

(* -------------------------------------------------------------------- *)
axiom degree_mul (p p' : polynomial) : degree (mul p p') = degree p + degree p'.

(* ==================================================================== *)
(** Scalar multiplication *)
op smul x p = map (fun m => {| coef = fmul x m.`coef ; expo = m.`expo |} ) p.

(* -------------------------------------------------------------------- *)
lemma size_smul c p : size (smul c p) = size p.
proof. by rewrite /smul size_map. qed.

(* -------------------------------------------------------------------- *)
lemma eval_smul x c p : eval x (smul c p) = fmul c (eval x p).
proof.
  rewrite /smul; elim p => /=; first by ringeq.
  by move => m p /> *; rewrite /meval /=; smt.
qed.

(* -------------------------------------------------------------------- *)
lemma degree_smul c p : degree (smul c p) = degree p.
proof. by rewrite /degree /= foldr_map /=. qed. 

(* -------------------------------------------------------------------- *)
lemma smul_expo c p :   
  forall i, 0 <= i < size p => (nth mzero (smul c p) i).`expo = (nth mzero p i).`expo.
proof. by progress; rewrite /smul; rewrite (nth_map mzero _ _). qed.

(* -------------------------------------------------------------------- *)
lemma update_smul p x s:
  count (fun (x : monomial) => x.`expo = 0) p = 1 =>
  update (smul x p) 0 (fmul x s) = smul x (update p 0 s).
proof.
  elim p => //; progress.
  case (x0.`expo = 0); progress.
  rewrite /smul /=.
  rewrite /update /= !H1 /= -!map_comp /(\o) /=.
  rewrite -eq_in_map => m; progress.
  by case (m.`expo = 0). 
  simplify.  
  rewrite /smul /= /update /= !H1 /= -!map_comp /(\o) /=.
  rewrite -eq_in_map => m; progress.
  by case (m.`expo = 0). 
qed.

(* ==================================================================== *)
(** Monomial unary minus *)
op mumin m = {| coef = fumin m.`coef; expo = m.`expo |}.

(* ==================================================================== *)
(* Polynomial unary minus *)
op umin p =
  with p = [] => []
  with p = m :: p' => mumin m :: umin p'.

(* -------------------------------------------------------------------- *)
lemma eval_umin p x : eval x (umin p) = fumin (eval x p).
proof.
  elim p => /=; first by ringeq.
  progress.
    + by rewrite /meval /mumin H /= -oppfD; congr; rewrite mulNf.
qed.

(* -------------------------------------------------------------------- *)
lemma uminff p : add p (umin p) == pzero.
proof. by rewrite /(==) => *; rewrite /pzero eval_add eval_umin eval_zero -sub_def subff. qed.

(* ==================================================================== *)
(** Lagrange basis *)
op basis_loop (xi : t) (xj : t) (xm : t list) : t list =
  with xm = [] => []
  with xm = y :: ys => 
    if xj <> y then (fdiv (fsub xi y) (fsub xj y)) :: basis_loop xi xj ys
    else basis_loop xi xj ys.

op basis (xi xj : t) (xm : t list) = 
  foldr (fun (x y : t) => fmul x y) fone (basis_loop xi xj xm).

(* -------------------------------------------------------------------- *)
lemma basis_empty x y : basis x y [] = fone.
proof. by rewrite /basis /=. qed.

(* -------------------------------------------------------------------- *)
lemma basis_cons_same x xm : basis x x (x :: xm) = basis x x xm. 
proof. by rewrite /basis. qed.

(* -------------------------------------------------------------------- *)
lemma basis_cons x y z xm : 
  basis x y (z :: xm) = fmul (basis x y [z]) (basis x y xm).
proof.
  rewrite /basis => /=.
  case (y = z); progress.
    + by rewrite mulC mulf1.
    + by congr; rewrite mulf1.
qed.

(* -------------------------------------------------------------------- *)
lemma basis_cons_diff x y xm :
  y <> x =>
  basis x y (x :: xm) = fzero. 
proof. by move; progress; rewrite /basis /= H /= subff zero_div mulC mulf0. qed.

(* -------------------------------------------------------------------- *)
lemma basis_cons_diff_coef x y xm :
  basis x y (y :: xm) = basis x y xm by done.

(* -------------------------------------------------------------------- *)
lemma basis_eq x xm :
  basis x x xm = fone.
proof.
  rewrite /basis; elim xm => //=.
  progress.
    + case (x = x0); progress.
      rewrite H divff; first by rewrite diff_sub_zero /#.
      by rewrite mulf1.
qed.

(* -------------------------------------------------------------------- *)
lemma basis_neq (x y : t) (xm : t list) :
  y <> x => x \in xm =>
  basis x y xm = fzero.
proof.
  move; progress. move : H0; elim xm. progress.
  progress; case (x = x0); progress.
    + by rewrite basis_cons_diff /#.
    + by rewrite basis_cons H0 1:/# mulf0.
qed.

(* ==================================================================== *)
(** Lagrange polynomial interpolation *)
op interpolate_loop (x : t) (xm : t list) (pm : (t * t) list) =
  map (fun xy => fmul (basis x (fst xy) xm) (snd xy)) pm.

(* -------------------------------------------------------------------- *)
lemma interpolate_loop_cons x pm :
  pm <> [] => !(x \in unzip1 pm) =>
  fzero \in interpolate_loop x (x :: unzip1 pm) pm.
proof.
  elim pm => //; progress.
  by move : H; rewrite /interpolate_loop; progress; smt. 
qed.

(* -------------------------------------------------------------------- *)
op interpolate (x : t) (pm : (t * t) list) = 
  sumt (interpolate_loop x (map fst pm) pm).

(* -------------------------------------------------------------------- *)
axiom interpolate_constant (pm : t list) (c : t) (x : t) : 
  uniq pm =>
  interpolate x (map (fun y => (y, c)) pm) = c.

(* -------------------------------------------------------------------- *)
axiom interpolate_mem (pm : (t * t) list) (x : t) : 
  uniq (unzip1 pm) => x \in unzip1 pm =>
  interpolate x pm = oget (assoc pm x).

(* -------------------------------------------------------------------- *)
axiom interpolate_eval (pm : t list) (p : polynomial) (x : t) : 
  uniq pm =>
  degree p < size pm =>
  interpolate x (map (fun y => (y, eval y p)) pm) = eval x p.

(* -------------------------------------------------------------------- *)
axiom interpolate_eval_update (pm : t list) (p : polynomial) (x : t) : 
  count (fun (x : monomial) => x.`expo = 0) p = 1 =>
  uniq pm =>
  degree p < size pm =>
  interpolate fzero (map (fun y => (y, eval y (update p 0 x))) pm) = x.

(* ==================================================================== *)
(** Lagrande polynomial interpolation with reconstructed polynomial *)
op basis_poly (x : t) (xs: t list) : polynomial =
  with xs = [] => pone
  with xs = y :: ys =>
    if x = y then basis_poly x ys
    else mul ([ {| coef = fdiv fone (fsub x y) ; expo = 1 |} ; 
                {| coef = fdiv (fumin y) (fsub x y) ; expo = 0 |} ]) (basis_poly x ys).

op interpolate_poly_loop (xs: t list) (pm: (t * t) list) : polynomial =
  with xs = [] => []
  with xs = y :: ys =>
    add (mpmul {| coef = (odflt fzero (assoc pm y)) ; expo = 0 |} (basis_poly y xs)) 
    (interpolate_poly_loop ys pm).

op interpolate_poly (pm: (t * t) list) : polynomial =
  interpolate_poly_loop (map fst pm) pm.

axiom interpolate_polyE (pm : t list) (p : polynomial) : 
  uniq pm =>
  interpolate_poly (map (fun y => (y, eval y p)) pm) = p.

axiom interpolate_poly_eval (pm : (t * t) list) (x : t) : 
  uniq (unzip1 pm) =>
  interpolate x pm = 
  eval x (interpolate_poly pm).

axiom degree_interpolate_poly0 (xs : t list) (rs : (t * polynomial) list) (d : int) :
  uniq xs => unzip1 rs = xs =>
  (forall x, x \in xs => degree (oget (assoc rs x)) = d) => 
  degree (interpolate_poly (map (fun x => (x, eval fzero (oget (assoc rs x)))) xs)) = d.

axiom degree_interpolate_polyX (xs : t list) (rs : (t * polynomial) list)
                               y (d : int) :
  uniq xs => unzip1 rs = xs =>
  (forall x, x \in xs => degree (oget (assoc rs x)) = d) => 
  degree (interpolate_poly (map (fun x => (x, eval y (oget (assoc rs x)))) xs)) = d.

axiom size_interpolate_polyX (xs : t list) (rs : (t * polynomial) list)
                               y (d : int) :
  uniq xs => unzip1 rs = xs =>
  (forall x, x \in xs => size (oget (assoc rs x)) = d) => 
  size (interpolate_poly (map (fun x => (x, eval y (oget (assoc rs x)))) xs)) = d.

axiom expos_interpolate_polyX (xs : t list) (rs : (t * polynomial) list) y ( d : int) :
  uniq xs => unzip1 rs = xs =>
  (forall x, x \in xs => size (oget (assoc rs x)) = d) => 
  (forall x, x \in xs => 
    forall (i : int), 0 <= i && i < d => (nth mzero (oget (assoc rs x)) i).`expo = d - 1 - i) => 
  (forall (i : int), 0 <= i && i < d => (nth mzero (interpolate_poly (map (fun x => (x, eval y (oget (assoc rs x)))) xs)) i).`expo = d - 1 - i).

(* ==================================================================== *)
(** Polynomial distribution *)
op dpolynomial : int -> polynomial distr.

(* -------------------------------------------------------------------- *)
axiom dpolynomial_ll x : 0 <= x => is_lossless (dpolynomial x).

(* -------------------------------------------------------------------- *)
axiom dpolynomial_size p x : 0 <= x => p \in dpolynomial x => size p = x + 1.

(* -------------------------------------------------------------------- *)
axiom dpolynomial_non_zeros p x : 0 <= x => p \in dpolynomial x => non_zeros_polynomial p.

(* -------------------------------------------------------------------- *)
axiom dpolynomial_exp p x i : 
  0 <= x => p \in dpolynomial x => (nth mzero p i).`expo = x - i.

(* -------------------------------------------------------------------- *)
axiom dpolynomial_degree p x : 0 <= x => p \in dpolynomial x => degree p = x.

(* ==================================================================== *)
(** Polynomial random generation module *)
module PolynomialRand = {
  proc gen(n : int) = {
    var p;
    p <$ dpolynomial n;
    return p;
  }
}.

(* -------------------------------------------------------------------- *)
axiom polynomial_rand_equiv n_: equiv [ PolynomialRand.gen ~ PolynomialRand.gen : 
          ={n} /\ n{1} = n_ ==> 
          res{1} \in dpolynomial n_ /\
          res{2} \in dpolynomial n_ /\
          forall x c c', x <> fzero => eval x (update res{1} 0 c) = eval x (update res{2} 0 c') ].

axiom ind_sumt_poly (x v v' : t) (ps ps' : (t * polynomial) list) : 
  unzip1 ps = unzip1 ps' => x \in unzip1 ps =>
  (forall (x' c c' : t),
          x' <> fzero =>
          eval x' (update (oget (assoc ps x)) 0 c) =
          eval x' (update (oget (assoc ps' x)) 0 c')) =>
  fadd v (eval x (update (foldr (fun (p : t * polynomial) (st : polynomial) => add st p.`2) pzero ps) 0 fzero)) = fadd v' (eval x (update (foldr (fun (p : t * polynomial) (st : polynomial) => add st p.`2) pzero ps') 0 fzero)).
