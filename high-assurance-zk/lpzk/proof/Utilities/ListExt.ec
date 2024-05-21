(**
  This file contains a series of additional lemmas and operations thatn extend the default
  EasyCrypt list library
*)
require import AllCore List.

(** Proves that the head of the list is a member of that list *)
lemma headP (s : 'a list) (z0 : 'a) :
  0 < size s => head z0 s \in s.
proof. by elim s => //. qed.

(** Proves that if two lists are equal up to permutation, than the same predicate applied to
    both of them yields the same result *)
lemma perm_eq_all (s s' : 'a list) (P : 'a -> bool) : 
  perm_eq s s' => all P s = all P s'.
proof. by smt(@List). qed.

(** Proves that [(map f xs).[x] = f xs.[x]], for an association list [xs] and key [x] *)
lemma map_assoc (f : 'a -> 'b) (x : 'a) (s : 'a list) :
  x \in s => assoc (map (fun x => (x, f x)) s) x = Some (f x).
proof. 
  elim s => //= x' l hind h.
  case (x = x') => hx.
    by rewrite hx assoc_cons /=.
  by rewrite assoc_cons hx /= hind /#.
qed.

(** Conditional application of the **map_assoc** lemma. Proves that the **map_assoc** lemma
    holds except for one of the association list keys *)
lemma map_assoc_if (f : 'a -> 'b) (x : 'a) (s : 'a list) (a : 'a) (b : 'b) :
  x \in s => 
  assoc (map (fun k => if k = a then (a,b) else (k, f k)) s) x = 
  Some (if x = a then b else f x).
proof. 
  elim s => //= x' l hind h.
  case (x' = a); progress.
    rewrite assoc_cons /=.
    by case (x = a) => hx => //=; first by smt().
  rewrite assoc_cons /=.
  case (x = x') => H0.
    have ->: x = a <=> false by smt().
    by smt().
  by smt().
qed.

(** Proves that [(map f xs).[x] = None], if the key [x] is not a member of [xs] *)
lemma map_assocN (f : 'a -> 'b) (x : 'a) (s : 'a list) :
  !(x \in s) => assoc (map (fun x => (x, f x)) s) x = None.
proof. 
  elim s => //= x' l hind h.
  by rewrite assoc_cons hind => /#. 
qed.

(** [assoc_rem x l] removes the element with key [x] from list [l] *)
op assoc_rem (x : 'a) (l : ('a * 'b) list) : ('a * 'b) list =
  if x \in unzip1 l then rem (x, oget (assoc l x)) l else l.

(** Proves that all keys that are different from [x] in [assoc_rem x l] remain in the domain
    of l after [assoc_rem x l] *)
lemma mem_assoc_rem (x : 'a) (l : ('a * 'b) list) (y : 'a) :
  x <> y =>
  x \in unzip1 l =>
  x \in unzip1 (assoc_rem y l).
proof.
  move => H.
  elim l => //=.
  move => x' l; progress.
  case (x = x'.`1); progress.
    case (y = x'.`1); progress; first 2 by smt().
  move : H1; rewrite H2 /=; progress.
  case (y = x'.`1); progress; first by smt().
  have : x \in unzip1 (assoc_rem y l) by smt().
  rewrite /assoc_rem. 
rewrite !mapP.
progress.
exists x0.
progress.
smt(@List).
qed.

(** Proves that [l.[x]] = [(assoc_rem y l).[x]] if **x <> l**, for an association list [l] *)
lemma assoc_rem (x : 'a) (l : ('a * 'b) list) (y : 'a) :
  x <> y =>
  assoc l x = assoc (assoc_rem y l) x.
proof.
  move => H.
  elim l => //=.
  move => x' l; progress.
  case (x = x'.`1); progress.
    case (y = x'.`1); progress; first 2 by smt().
  have ->: x' = (x'.`1, x'.`2) by smt().
  rewrite assoc_cons /= H1 /=.
  rewrite H0 /=.
rewrite /assoc_rem /=.
case (y \in unzip1 l); progress.
case (x'.`1 = y); progress.
have <-: x'.`2 = oget (assoc ((x'.`1, x'.`2) :: l) x'.`1).
smt().
simplify.
rewrite H0.
rewrite /assoc_rem.
rewrite H2.
simplify.
done.

smt.

case (y = x'.`1); progress.
rewrite assoc_cons /=.
rewrite H1 /=.
done.
qed.

(** Proves that [(x,y) :: (assoc_rem x l).[k] = y] if [k = x] or [l.[x]] otherwise *)
lemma assoc_rem_cons (x : 'a) (y : 'b) (l : ('a * 'b) list) (k : 'a) :
  x \in unzip1 l =>
  assoc ((x,y) :: (assoc_rem x l)) k = if k = x then Some y else assoc l k.
proof.
  progress.
  rewrite assoc_cons /=.
  case (k = x); progress.
  rewrite -(assoc_rem k _ x) //.
qed.

(** Proves that [(x,y) :: (assoc_rem x l).[k] = y] if [k = x] or [l.[x]] otherwise *)
lemma assoc_mem_unzip2 (s : ('a * 'b) list) x :
x \in unzip1 s => oget (assoc s x) \in unzip2 s.
proof.
elim s => //= x' s.
progress.
smt().
qed.

(** Proves that if there are no repeated elements in the domain of an association list, then
    removing an element from that list means that the element removed is no longer on the domain
    of the resulting association list *)
lemma unzip1_assoc_rem_memN x (s : ('a * 'b) list) : 
  uniq (unzip1 s) => !(x \in unzip1 (assoc_rem x s)).
proof.
  rewrite /assoc_rem /=.
  rewrite mapP.

elim s; progress.
case (x = x0.`1); progress.
have <-: x0 = (x0.`1, oget (assoc (x0 :: l) x0.`1)).
smt().
simplify.
smt.
smt.
qed.

(** Proves that if there are no repeated elements in the domain of an association list, then
    there are no repeated elements in the domain of the list after removing a pair from it *)
lemma uniq_unzip1_assoc_rem (x : 'a) (s : ('a * 'b) list) : 
  uniq (unzip1 s) => uniq (unzip1 (assoc_rem x s)).
proof.
smt.
qed.

(** Proves that the domain of an association list after removing an element from it is the same
    as removing just they key from the domain *)
lemma unzip1_map_rem_assoc (s : ('a * 'b) list) x : 
  unzip1 (rem (x, oget (assoc s x)) s) = rem x (unzip1 s).
proof.
elim s => //=.
move => x' s; progress.
have ->: x' = (fst x', snd x') by smt().
rewrite (assoc_cons).
simplify.
case (x'.`1 = x); progress.
have ->: x = x'.`1 <=> false by smt().
simplify.
by rewrite H.
qed.

(** Proves the domain of an association list is equal up to permutation to the domain of an
    association list where a *(key, value)* pair is first removed and then added back to it *)
lemma unzip1_assoc_rem_cons (x : 'a) (y : 'b) (s : ('a * 'b) list) :
  x \in unzip1 s =>
  perm_eq (unzip1 s) (unzip1 ((x, y) :: assoc_rem x s)).
proof.
progress.
rewrite /assoc_rem /=.
rewrite H /=.
rewrite unzip1_map_rem_assoc.
rewrite perm_to_rem.
done.
qed.

(** Proves that if a key in a member of the domain of association list, then the corresponding
    *(key, value)* pair is a member of the association list *)
lemma assoc_unzip1_mem k (s : ('a * 'b) list) : 
  k \in unzip1 s => (k, oget (assoc s k)) \in s.
proof.
smt.
qed.

(** Proves that if there are no repeated elements in the domain of an association list, then
    there are no repeated elements in the domain of an association list after one removes a
    *(key, value)* pair from it and add it back again *)
lemma uniq_unzip1_cons_assoc_rem (s : ('a * 'b) list) x y : 
  uniq (unzip1 s) => uniq (unzip1 ((x,y) :: assoc_rem x s)).
proof.
simplify.
progress.
rewrite /assoc_rem.
case (x \in unzip1 s); progress.
have ->: unzip1 (rem (x, oget (assoc s x)) s) = rem x (unzip1 s).
clear H H0.
elim s.
progress.
progress.
have ->: x0 = (fst x0, snd x0) by smt().
rewrite (assoc_cons).
simplify.
case (x0.`1 = x); progress.
have ->: x = x0.`1 <=> false by smt().
simplify.
by rewrite H.
smt(@List).
rewrite uniq_unzip1_assoc_rem.
done.
qed.

(** Proves that [(assoc_rem x s).[k] = s.[k]] if [x <> k] *)
lemma assoc_assoc_rem (s : ('a * 'b) list) k x : 
  x <> k => assoc (assoc_rem x s) k = assoc s k.
proof.
rewrite /assoc_rem.
progress.
case (x \in unzip1 s); progress.
clear H0.
elim s.
progress.
progress.
have ->: x0 = (fst x0, snd x0) by smt().
rewrite (assoc_cons).
simplify.
case (x0.`1 = x); progress.
smt(@List).
have ->: x = x0.`1 <=> false by smt().
simplify.
smt(@List).
qed.

(** Proves that, for an association list [s], the [i]th element of that list is a pair consisting
    on the [i]th element of the domain and of the [i]th element of range *)
lemma nth_assoc (x : 'a) (y : 'b) (s : ('a * 'b) list) i :
  0 <= i < size s =>
  nth (x,y) s i = (nth x (unzip1 s) i, nth y (unzip2 s) i).
proof.
progress.
rewrite !(nth_map witness) => //=.
smt(@List).
qed.

(** Gives another definition of an association list [s], as 
    [map (fun x => (x, s.[x])) (domain s)] *)
lemma eq_assoc_map (s : ('a * 'b) list) :
  uniq (unzip1 s) =>
  s = map (fun x => (x, oget (assoc s x))) (unzip1 s).
proof.
  elim s => //.
  progress; first by smt().
  move : H0; elim x => x1 x2 /=.
  have ->: (fun (x : 'a) => (x, oget (assoc ((x1, x2) :: l) x))) = 
           (fun (x : 'a) => (x, oget (if x1 = x then Some x2 else assoc l x))).
    rewrite fun_ext /(==); progress.
    by rewrite assoc_cons => /#.
  by progress; rewrite H //; smt.
qed.

(** Proves that if the domain of an association list has no repeated elements, then the list 
    itself will also not have any repeated elements *)
lemma uniq_assoc (s : ('a * 'b) list) :
  uniq (unzip1 s) =>
  uniq s.
proof.
  elim s => //; progress; first by smt.
  by rewrite H.
qed.

(** Proves that if the domains of the association lists are equal up to permutation, and if the
    the keys of both lists have the same value, then the two association lists will also be
    equal up to permutation *)
lemma assoc_is_perm_eq (s1 s2 : ('a * 'b) list) :
  uniq (unzip1 s1) => 
  perm_eq (unzip1 s1) (unzip1 s2) =>
  (forall x, x \in unzip1 s1 => assoc s1 x = assoc s2 x) =>
  perm_eq s1 s2.
proof.
progress.
rewrite /perm_eq allP.
progress.
rewrite !count_uniq_mem.
smt.
smt.
rewrite /b2i.
case (x \in s1); progress.
have ->: x \in s2.
have H4 : x.`1 \in unzip1 s2.
have : x.`1 \in unzip1 s1.
smt.
smt.
have H5 : assoc s2 x.`1 = Some x.`2.
rewrite -H1.
smt.
rewrite -mem_assoc_uniq.
done.
smt().
smt.
done.

have ->: x \in s2 <=> false.
case (! (x.`1 \in unzip1 s2)); progress.
smt.

have : assoc s1 x.`1 <> Some x.`2.
smt.
progress.
have : assoc s2 x.`1 <> Some x.`2.
smt.
progress.
move : (assocP s2 x.`1).
rewrite H4 /=.
progress.
move : (mem_assoc_uniq s2 x.`1 x.`2).

smt.
done.
qed.
