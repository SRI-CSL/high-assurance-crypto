require import AllCore Int List FSet SmtMap Distr.
require import Aux AuxList Int.

(* Sets *)

lemma in_eq x (xs ys : 'a fset) :
  x \in ys /\ xs= ys => x \in xs.
  progress. qed.  

op iset (n:int) : int fset = oflist (iseq n).
op iset' (n m:int) : int fset = oflist (iota_ n m).

lemma iset_ge (i n m:int) :
  n <= m => i \in iset n => i \in iset m.
  rewrite /iset !mem_oflist /iseq !mem_iota. progress. smt(). qed.

lemma iset_in_def i n :
  i \in iset n = (0 <= i /\ i < n).
  rewrite mem_oflist mem_iota => />*. qed.

lemma iset_in_def' i n m :
  i \in iset' n m = (n <= i /\ i < n+m).
  rewrite mem_oflist mem_iota => />*. qed.

lemma iset_succ n :
  0 <= n => iset (n+1) = iset n `|` fset1 n.
  rewrite fsetP => />*. rewrite in_fsetU in_fset1 !iset_in_def => />*. smt(). qed.

lemma iset_succ' (n m:int) :
  0 <= n => 0 <= m => iset' n (m+1) = iset' n m `|` fset1 (n+m).
  rewrite fsetP => />*. rewrite in_fsetU in_fset1 !iset_in_def' => />*. progress.
  smt(). smt(). smt(). qed.

lemma iset_fset0 n :
  n <= 0 => iset n = fset0.
  rewrite /iset => />*. rewrite iseq_nil. progress. rewrite fsetP => />*. rewrite !mem_oflist => />*. rewrite in_fset0 => />*. qed.

lemma iset_fset0' s n :
  n <= 0 => iset' s n = fset0.
  rewrite /iset' => />*. rewrite iota0 => />*. progress. rewrite fsetP => />*. rewrite !mem_oflist => />*. rewrite in_fset0 => />*. qed.

lemma card_iset n :
  0 <= n => card (iset n) = n. 
  elim n => />*. rewrite iset_fset0 => />*. rewrite fcards0 => />*. 
  rewrite iset_succ => />*. rewrite fcardUI_indep => />*. rewrite fsetP => />*. rewrite !in_fsetI !in_fset0 !in_fset1 => />*.
  rewrite iset_in_def => />. smt(). rewrite fcard1 => />*. smt(). qed.

lemma notin_iset i n :
  i < 0 || n <= i => !(i \in iset n).
  rewrite iset_in_def => />*. smt(). qed.

lemma in_iset i n : 
  0 <= i /\ i < n => i \in iset n.
  rewrite iset_in_def => />*. qed.

lemma in_iset_succ' x (n m1 m2:int) :
  m1 <= m2 => x \in iset' n m1 => x \in iset' n m2.
  rewrite !iset_in_def' => />*. smt(). qed.

lemma le_subset_iset (n1 n2:int) :
  (n1 <= n2) => iset n1 \subset iset n2.
  rewrite /iset subsetP => /> H. 
move : (mem_oflist (iseq n1))=> H1.
move : (mem_oflist (iseq n2))=> H2.
rewrite /(<=) => a. rewrite H1 H2. rewrite !in_iseq => />. smt(@List).
qed.

lemma subset_in (s1 s2:'a fset) :
  s1 \subset s2 = (forall x, x \in s1 => x \in s2).
  rewrite subsetP /(<=). progress. qed.

lemma in_subset s1 s2 (x:'a) :
  s1 \subset s2 /\ x \in s1 => x \in s2.
  rewrite subset_in => />. smt(). 
qed.

lemma subset_trans (x y z:'a fset) :
  x \subset y => y \subset z => x \subset z.
  rewrite !subsetP /(<=) => />H1 H2 a Ha. rewrite H2 H1 => />. qed.

lemma subset_id (x:'a fset) :
  x \subset x.
  rewrite subsetP /(<=) => />. qed.

op fsetall (p:'a->bool) (xs:'a fset) : bool =
  forall i, i \in xs => p i
  axiomatized by fsetallP.

lemma fset_filter_fset0 (p:'a->bool) (xs:'a fset) :
  fsetall (fun i => !p i) xs => filter p xs = fset0.
  rewrite fsetallP. progress. 
  rewrite fsetP => />*. rewrite in_fset0 =>/>*. rewrite in_filter => />*. 
  smt(). qed.

lemma fset_filter_id (p:'a->bool) (xs:'a fset) :
  fsetall (fun i => p i) xs => filter p xs = xs.
  rewrite fsetallP => />. rewrite fsetP => /> H x. rewrite !in_filter => /> H0. smt(). qed.


lemma isetI n1 n2 :
  iset n1 `&` iset n2 = iset (min n1 n2).
  rewrite fsetP => />*. rewrite in_fsetI !iset_in_def. smt(). qed.

op interset (x y:'a fset) = x `&` y.

op disjU (x y : 'a fset) = (x `|` y) `\` (x `&` y).

lemma in_oflist x (s:'a list) :
  x \in oflist s = x \in s.
  smt(mem_oflist). qed.

lemma nth_elems_in d (s:'a fset) i :
  0 <= i < card(s) => nth d (elems s) i \in s.
  progress. rewrite (_:nth d (elems s) i \in s = nth d (elems s) i \in elems s).
  rewrite- in_oflist elemsK => />*. rewrite cardE in H0.
  move :H H0. elim (elems s) i => /> i. smt(). move => l H j H1 H2.
  case (j=0) => /> H3.
smt(size_ge0). qed.

lemma oflist_nil :
  oflist [<:'a>] = fset0.
  smt(@FSet). qed.

lemma perm_eq2 (x y z w:'a) :
  perm_eq [x;y] [z;w] <=> ((x = z /\ y = w) \/ (x = w /\ y = z)).
  rewrite /perm_eq => />*. rewrite /b2i /pred1 => />*. smt().
qed.

lemma perm_eq2' x y (zs: 'a list) :
  perm_eq [x;y] zs <=> (size zs = 2 /\ ((x = nth witness zs 0 /\ y = nth witness zs 1) \/ (x = nth witness zs 1 /\ y = nth witness zs 0))).
  split. move => pp. have : size [x;y] = size zs. apply perm_eq_size => />H. 
  move => H. rewrite -H => />. rewrite (size2E zs). rewrite -H => />. rewrite !nth_cons => />. 
  case (x = nth witness zs 0 /\ y = nth witness zs 1). smt().
  move => H1. simplify. move : pp. rewrite (size2E zs) => />. rewrite -H => />. 
  rewrite /pred1 => />. smt(@List).
smt(perm_eq2  size2E @List).
qed.

axiom elems_fset1U (x y: 'a) :
  x <> y => elems (fset1 x `|` fset1 y) = [x;y] \/ elems (fset1 x `|` fset1 y) = [y;x].

lemma card2E (xs:'a fset) :
  card xs = 2 => 
  xs = oflist [nth witness (elems xs) 0;nth witness (elems xs) 1].
  rewrite cardE => />H. rewrite (_:xs=oflist (elems xs)). rewrite elemsK => />*.
  rewrite (size2E (elems xs)) => />*. rewrite !oflist_cons !oflist_nil !fsetU0 => />*.
  have : elems (fset1 (nth witness (elems xs) 0) `|` fset1 (nth witness (elems xs) 1)) = [nth witness (elems xs) 0;nth witness (elems xs) 1] \/ elems (fset1 (nth witness (elems xs) 0) `|` fset1 (nth witness (elems xs) 1)) = [nth witness (elems xs) 1;nth witness (elems xs) 0]. rewrite elems_fset1U => />*. have : uniq (elems xs). rewrite uniq_elems => />*. rewrite (size2E (elems xs)) => />*.
  move => H1. elim H1 => /> H1.
  rewrite H1 => />. rewrite H1 => />. rewrite fsetUC => />. qed.

lemma elems_fset2_ind x y (p : 'a list -> bool) :
  x <> y =>
  p [x;y] =>
  p [y;x] =>
  forall l, l = elems (fset1 x `|` fset1 y) => p l.
  case (x=y) => />*. 
  have : elems (fset1 x `|` fset1 y) = [x;y] \/ elems (fset1 x `|` fset1 y) = [y;x]. rewrite elems_fset1U => />*. smt(). qed.

lemma fold2 (f : 'a -> 'b -> 'b) (z : 'b) (x y : 'a) : 
  x<>y => f x (f y z) = f y (f x z) =>
  fold f z (fset1 x `|` fset1 y) = f x (f y z). 
  rewrite foldE. move => diff.
  rewrite (_: ( f x (f y z) = f y (f x z) => foldr f z (elems (fset1 x `|` fset1 y)) = f x (f y z)) = (fun s => f x (f y z) = f y (f x z) => foldr f z s = f x (f y z)) (elems (fset1 x `|` fset1 y)) ). smt().   
  apply/(elems_fset2_ind x y) => />*. smt().  qed.

lemma subset_l (x y z:'a fset) :
  x \subset y => x \subset y `|` z.
  rewrite !subsetP => />*. rewrite in_fsetU => />*. smt(). qed.

lemma subset_r (x y z:'a fset) :
  x \subset z => x \subset y `|` z.
  rewrite !subsetP => />*. rewrite in_fsetU => />*. smt(). qed.

lemma subset_from_l (x y z:'a fset) : 
  (x `|` y) \subset z => x \subset z.
  rewrite !subsetP => />.  rewrite /(<=) => /> H H0 H1. apply H. smt(@FSet). qed. 

lemma subset_from_r (x y z:'a fset) : 
  (x `|` y) \subset z => y \subset z.
  rewrite !subsetP => /> H. rewrite /(<=) => /> aa HH. move : H.
  rewrite /(<=) => H. rewrite H. rewrite in_fsetU => />. smt(). qed. 

lemma l_subset (x y z:'a fset) :
  x \subset y => x `|` z \subset y `|` z.
  rewrite !subsetP => /> H H0. rewrite !in_fsetU => />*. smt(). qed.

lemma r_subset (x y z:'a fset) :
  x \subset y => z `|` x \subset z `|` y.
  rewrite !subsetP => /> H H0.  rewrite !in_fsetU => />*. smt(). qed.

lemma in_subset_l x (y z y1 : 'a fset) :
  x \in y `|` z => y \subset y1 => x \in y1 `|` z.
  move => H1 H2. rewrite (in_subset (y `|`z)) => />. rewrite subsetP /(<=) => a.
  rewrite !in_fsetU => />. smt(). qed.

lemma subset_l0 (x1 x2 y:'a fset) :
  x1 \subset x2 => x2 `&` y = fset0 => x1 `&` y = fset0.
  rewrite !fsetP => />H1 H2 x. split.
  rewrite !in_fsetI. rewrite -H2 in_fsetI. smt(@FSet).
  rewrite in_fset0 => />*. qed.

lemma oflist_rcons (xs:'a list) x :
  oflist (rcons xs x) = oflist xs `|` fset1 x.
  rewrite fsetP => />*. rewrite !mem_oflist => />*. rewrite !mem_rcons => />*. progress.
  rewrite in_fsetU mem_oflist in_fset1 => />*. smt().
  rewrite in_fsetU mem_oflist in_fset1 in H => />*. smt(). qed.

lemma filter_subset (p:'a->bool) (xs:'a fset) :
  filter p xs \subset xs.  
  rewrite subsetP => />. rewrite /(<=) => a. rewrite in_filter => />. qed.

lemma nth_in_oflist (xs:'a list) i :
    0 <= i < size xs =>
    nth witness xs i \in oflist xs.
    rewrite mem_oflist => />*. rewrite nth_in => />*. qed.

lemma oflist_cons_ne0 x (xs:'a list) :
  oflist (x::xs) <> fset0.
  rewrite oflist_cons => />*. smt(@FSet). qed.

lemma pick_subset (A B : 'a fset) :
  A <> fset0 => A \subset B => pick A \in B.
  rewrite subsetP /(<=) => /> H a. smt(@FSet).  qed.
  
lemma pick1 (x:'a) :
  pick (fset1 x) = x.
  rewrite pickE => />*. rewrite elems_fset1 => />*. qed.
