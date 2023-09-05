require import AllCore Int List FSet SmtMap CoreMap.
require import Aux AuxList AuxFSet.

(* Maps *)

lemma fdom_empty :
  fdom empty<:'a,'b> = fset0<:'a>.
  rewrite fsetP => />*. rewrite in_fset0 mem_fdom. smt(mem_empty). qed.

lemma fmap_eqIn (m1 m2 : ('a,'b) fmap) : 
  ((fdom m1 = fdom m2) /\ (forall i, i \in fdom m1 => m1.[i] = m2.[i])) = (m1 = m2).
  rewrite -fmap_eqP. rewrite eq_logical => />. 
split. move => H H0 x. case (x \in fdom m1) => />H1. rewrite H0 => />. rewrite !get_none => />. rewrite mem_fdom in H1 => />. move :H1. rewrite H mem_fdom => />.
  move => H. rewrite fsetP => />. split.
  move => x. smt(@SmtMap).
  move => i H1. rewrite H => />.
qed.

lemma get_map (f:'a->'b->'c) (m:('a,'b) fmap) (a:'a) :
  (map f m).[a] = omap (f a) m.[a].
  rewrite mapE => />*. qed.

lemma map_some (f:'a->'b->'c) (m:('a,'b) fmap) (a:'a) :
  a \in m => (map f m).[a] = Some (f a (oget m.[a])).
  rewrite get_map => />*. rewrite omap_some => />*. qed.

op fmap (f:'b->'c) (m:('a,'b) fmap) : ('a,'c) fmap =
  map (fun x => f) m.

abbrev filter_idx (p:'a->bool) (xs:('a,'b)fmap) = filter (fun i x => p i) xs.

lemma fmap_empty (f:'b->'c) (m:('a,'b) fmap) :
  (m = empty) = (fmap f m = empty).
  rewrite -!fmap_eqP => />. rewrite eq_logical => />. split.
  move => H x. rewrite get_map H => />. rewrite !emptyE => />.
  move => H x. have : (fmap f m).[x] = empty.[x]. rewrite H => />. rewrite get_map !emptyE => />. case (m.[x]) => />*. 
qed.

lemma fmap_comp (g:'c->'d) (f:'b->'c) (m:('a,'b) fmap) :
  fmap g (fmap f m) = fmap (g \o f) m.
  rewrite -fmap_eqIn => />*. rewrite !fdom_map => />*. rewrite !get_map omap_comp /(\o) => />*.
  qed.

op fzip (m1 : ('a,'b1) fmap) (m2 : ('a,'b2) fmap) : ('a,'b1*'b2) fmap =
  ofmap (Map.offun (fun x => ozip m1.[x] m2.[x] )).

lemma mem_fzip x (m1 : ('a,'b1) fmap) (m2 : ('a,'b2) fmap) : 
  x \in fzip m1 m2 <=> (x \in m1 /\ x \in m2).
  rewrite domE /fzip getE ofmapK. 
  apply/Finite.finiteP => /=. exists (elems (fdom m1 `&` fdom m2)) => /> x0.
rewrite Map.getE Map.offunK => />*. rewrite setIE. 
rewrite -mem_oflist elemsK mem_oflist mem_filter.
rewrite -mem_oflist elemsK. 
have : m1.[x0] <> None /\ m2.[x0] <> None. 
rewrite some_ozip => />*. rewrite !fdomP => />*.
rewrite Map.getE Map.offunK => />. split. move => H. have : (m1.[x] <> None /\ m2.[x] <> None). apply some_ozip => />. progress. move => H1 H2. rewrite ozip_some => />.
qed.

lemma fdom_fzip (xs:('a,'b) fmap) (ys:('a,'c) fmap) : 
  fdom (fzip xs ys) = (fdom xs) `&` (fdom ys).
  rewrite fsetP => />*. rewrite in_fsetI. rewrite !mem_fdom !mem_fzip => />*. qed.

lemma get_fzip (xs:('a,'b) fmap) (ys: ('a,'c) fmap) (i:'a) : 
  (fzip xs ys).[i] = (ozip xs.[i] ys.[i]).
  case (i \in xs) => />*. case (i \in ys) => />*. 
  rewrite ozip_some. rewrite -fdomP mem_fdom => />*. rewrite -fdomP mem_fdom => />*. 
  rewrite /fzip getE ofmapK. apply/Finite.finiteP => /=. exists (elems (fdom xs `&` fdom ys)) => /> x.
rewrite Map.getE Map.offunK => /> H.
rewrite setIE. rewrite -mem_oflist elemsK mem_oflist mem_filter. 
rewrite -mem_oflist elemsK. 
have : xs.[x] <> None /\ ys.[x] <> None. 
rewrite some_ozip => />*. rewrite !fdomP => />*. 
rewrite Map.getE Map.offunK => />*. 
rewrite ozip_some. 
rewrite -fdomP mem_fdom => />*. 
rewrite -fdomP mem_fdom => /> /#. 
smt().
rewrite ozip_none. 
smt().
rewrite (_: ((fzip xs ys).[i] = None) = !((fzip xs ys).[i] <> None)).
smt().
rewrite -fdomP fdom_fzip in_fsetI => />*. 
smt(@SmtMap).
rewrite ozip_none. 
smt().
smt(mem_fzip).
qed.

lemma fzip_some (xs:('a,'b) fmap) (ys: ('a,'c) fmap) (i:'a) : 
  i \in fdom xs `&` fdom ys => (fzip xs ys).[i] = Some (oget xs.[i],oget ys.[i]).
  rewrite get_fzip => />. 
rewrite in_fsetI => />*. rewrite ozip_some => />*. rewrite -fdomP => />*. rewrite -fdomP => />*. qed.

lemma fzip_id (tr:('a,'b*'d) fmap) :
  fzip (fmap fst tr) (fmap snd tr) = tr.
  rewrite -fmap_eqIn => />*. rewrite !fdom_fzip !fdom_map fsetIid => />*. rewrite !get_fzip !get_map => />*. rewrite !omap_some => />*. rewrite -fdomP => />*. rewrite -fdomP => />*. rewrite ozip_some => />*. rewrite -prod_id => />. 
 smt(@SmtMap). qed.

abbrev fzip3 (m1 : ('a,'b1) fmap) (m2 : ('a,'b2) fmap) (m3 : ('a,'b3) fmap) = (fzip m1 (fzip m2 m3)).

op fmerge (f:'b1 -> 'b2 -> 'b3) (m1 : ('a,'b1) fmap) (m2 : ('a,'b2) fmap) : ('a,'b3) fmap =
  fmap (uncurry f) (fzip m1 m2).

lemma fdom_fmerge (f: 'b -> 'c -> 'd) (m1 : ('a,'b) fmap) (m2 : ('a,'c) fmap)  :
  fdom (fmerge f m1 m2) = fdom m1 `&` fdom m2.
  rewrite /fmerge. rewrite fdom_map /uncurry => />*. rewrite fdom_fzip => />*. qed.

lemma get_fmerge (f:'b->'c->'d) (m1:('a,'b) fmap) (m2:('a,'c) fmap) (a:'a) :
  (fmerge f m1 m2).[a] = omap (uncurry f) (ozip m1.[a] m2.[a]).
  rewrite /fmerge /uncurry get_map !get_fzip => />*. qed.

lemma fmerge_some (f:'b->'c->'d) (m1:('a,'b) fmap) (m2:('a,'c) fmap) (a:'a) :
  a \in fdom m1 `&` fdom m2 => (fmerge f m1 m2).[a] = Some (f (oget m1.[a]) (oget m2.[a])).
  rewrite in_fsetI => />*. rewrite get_fmerge /uncurry => />*. rewrite ozip_some => />*. 
  rewrite -fdomP => />*. rewrite -fdomP => />*. qed.

lemma get_filter (f:'a->'b->bool) (m:('a,'b) fmap) i :
  (filter f m).[i] = odflt None (omap (fun x => f i x ? Some x : None) m.[i]).
  rewrite filterE => />*. 
case (i \in m) => />H. rewrite omap_some => />. smt(). smt().
qed.

lemma filter_empty (p:'a->'b->bool) (xs:('a,'b) fmap) :
  (forall i, i \in xs => !p i (oget xs.[i])) => filter p xs = empty.
  rewrite -fmap_eqP => /> H x. rewrite filterE. 
  case (x \in xs) => />H1. have : !p x (oget xs.[x]). rewrite H => />*. auto => />. have : !oapp (p x) false xs.[x]. rewrite oapp_some => />. rewrite H => />.
  move => H2 H3. rewrite H2 => />. rewrite emptyE => />.
  rewrite emptyE => />. have : !(oapp (p x) false xs.[x]). smt(@SmtMap). move => H2. rewrite H2 => />. 
 qed.

op fall (f:'a -> 'b -> bool) (m:('a,'b) fmap) : bool =
  forall a, a \in fdom m => f a (oget m.[a])
  axiomatized by fallP.

lemma filter_id (p:'a->'b->bool) (xs:('a,'b) fmap) :
  fall p xs => filter p xs = xs.
  rewrite fallP -fmap_eqP => /> H x. rewrite filterE. 
  case (x \in xs) => />H1. have : p x (oget xs.[x]). rewrite H => />*. rewrite mem_fdom => />*. have : oapp (p x) false xs.[x]. rewrite oapp_some => />. rewrite H => />. smt(@SmtMap).
smt(@SmtMap). 
smt(@SmtMap). 
qed.

lemma filter_comp (p1 p2:'a->'b->bool) (xs:('a,'b) fmap) :
  filter p1 (filter p2 xs) = filter (fun a b => p1 a b /\ p2 a b) xs.
  rewrite -fmap_eqP => /> x. rewrite !filterE => />*.
  case (xs.[x]) => />x0. case (p2 x x0) => />*. qed.

lemma fdom_filter_subset (p:'a->'b->bool) (xs:('a,'b) fmap) :
  fdom (filter p xs) \subset fdom xs.
  rewrite subsetP => />. rewrite /(<=) => a. rewrite !mem_fdom !domE => />.
  rewrite getE ofmapK. apply/Finite.finiteP => /=. exists (elems (fdom xs)) => /> x.
  smt(@SmtMap). 
  rewrite Map.getE Map.offunK => /> H. smt().
qed.

lemma fdom_filter_idx (p1:'a->'b->bool) (p2:'a->bool) (xs:('a,'b) fmap) :
  fall (fun i x => p1 i x = p2 i) xs => fdom (filter p1 xs) = filter p2 (fdom xs).
  rewrite fallP. rewrite fsetP => /> H x. rewrite !mem_fdom !in_filter. rewrite -mem_fdom fdomP filterE.
  case (x \in xs) => /> H1. have : p1 x (oget xs.[x]) = p2 x. rewrite H => />*. rewrite mem_fdom => />H2 H3. move => H2. case (oapp (p1 x) false xs.[x]) => />H3 H4. rewrite -H2 mem_fdom => />. move :H3. rewrite oapp_some => />. rewrite mem_fdom => />. move :H3. rewrite oapp_some => />. rewrite H2. smt(). 
smt(@SmtMap).  
qed.

lemma map_filter_idx (f:'a -> 'b->'c) (p:'a->bool) (xs:('a,'b) fmap) :
  map f (filter (fun i x => p i) xs) = filter (fun i x => p i) (map f xs).
  rewrite -fmap_eqIn => />. rewrite !fdom_map !(fdom_filter_idx _ p) => />*. rewrite fallP => />*. rewrite fallP => />*. rewrite fdom_map => /> x H. rewrite in_filter in H => />*.  
  rewrite !get_map !get_filter => />*. rewrite !omap_some => />*. rewrite -fdomP. 
smt(). 
smt(). 
smt(@SmtMap).
smt(@SmtMap). 
move :H. progress. rewrite H => />. rewrite get_map omap_some => />. rewrite -fdomP => />. 
qed.

lemma fzip_filter_idx (p:'a->bool) (xs:('a,'b) fmap) (ys:('a,'c) fmap) :
  fzip (filter_idx p xs) (filter_idx p ys) = filter_idx p (fzip xs ys).
  rewrite -fmap_eqIn => />*. rewrite fdom_fzip => />*. rewrite !(fdom_filter_idx _ p) => />*. rewrite fallP => />*. rewrite fallP => />*. rewrite fallP => />*. rewrite fdom_fzip => />*. rewrite filterI => /> i. 
  rewrite !in_fsetI => />. rewrite !in_filter => />.
  rewrite !get_fzip !get_filter get_fzip => />*.  
  rewrite omap_some => />*. rewrite -fdomP => />*. rewrite omap_some => />*. rewrite -fdomP => />*. rewrite omap_some => />*. rewrite ozip_some => />*. rewrite -fdomP => />*. rewrite -fdomP => />*. 
  case (p i) => />*. 
  rewrite !ozip_some => />*. rewrite -fdomP => />*. rewrite -fdomP => />*. qed.

lemma fzip_filter_idx' (p1 p2:'a->bool) (xs:('a,'b) fmap) (ys:('a,'c) fmap) :
  fzip (filter_idx p1 xs) (filter_idx p2 ys) = filter_idx (fun a => p1 a /\ p2 a) (fzip xs ys).
  rewrite -fmap_eqIn => />*. rewrite fdom_fzip => />*. rewrite !(fdom_filter_idx (fun i x => p1 i) p1) => />*. rewrite fallP => />*. rewrite !(fdom_filter_idx (fun i x => p2 i) p2) => />. rewrite fallP => />. rewrite (_: (fun (i : 'a) (_ : 'b * 'c) => p1 i /\ p2 i) = (fun i x => (fun i => p1 i /\ p2 i) i) ). auto => />. rewrite (fdom_filter_idx _ (fun i => p1 i /\ p2 i)) => />. rewrite fallP => />. rewrite fdom_fzip => />. rewrite filterI => />. split.
  rewrite fsetP => />. auto => /> x.  rewrite !in_fsetI => />.
 by rewrite !in_filter => />. 
   move => i.
 rewrite !in_fsetI => />.  rewrite !in_filter => />.
  rewrite !get_fzip !get_filter get_fzip => />*. 
  rewrite omap_some => />*. rewrite -fdomP => />*. rewrite omap_some => />*. rewrite -fdomP => />*. rewrite omap_some => />*. rewrite ozip_some => />*. rewrite -fdomP => />*. rewrite -fdomP => />*. 
  case (p1 i) => />*. case (p2 i) => />*. 
  rewrite !ozip_some => />*. rewrite -fdomP => />*. rewrite -fdomP => />*. qed.

(*lemma fzip3_filter_idx (p:'a->bool) (xs:('a,'b) fmap) (ys:('a,'c) fmap) (zs:('a,'d) fmap) :
  fzip3 (filter_idx p xs) (filter_idx p ys) (filter_idx p zs) = filter_idx p (fzip3 xs ys zs).
  rewrite /fzip3 => />*. rewrite !fzip_filter_idx => />*. rewrite -map_filter_idx => />*. qed.*)
 
lemma filter_false (m:('a,'b) fmap) :
  filter (fun i x => false) m = empty.
  rewrite -fmap_eqIn => />*. rewrite !(fdom_filter_idx _ (fun i => false)) => />*. rewrite fallP => />*. rewrite fdom_empty => />*. auto => />. rewrite fsetP => />. 
do split. 
move => x. 
by rewrite in_fset0 in_filter => />*. 
move => i.
rewrite get_filter emptyE. rewrite odflt_def => />*. case (m.[i]) => />H. qed.

lemma filter_set_left (p:'a->'b->bool) (m:('a,'b) fmap) (i:'a) (b:'b) :
  i \notin m /\ !(p i b) => filter p m.[i <- b] = filter p m.
  rewrite filter_set. auto => />. move => H H0. rewrite rem_id => />.
smt(@SmtMap). qed.

lemma filter_eq (p:'a->'b->bool) (m:('a,'b) fmap) :
  fall p m => filter p m = m.
  rewrite fallP -fmap_eqP => /> H x. rewrite get_filter. 
case (x \in m) => /> ?. 
have : p x (oget m.[x]). rewrite H => />*. rewrite mem_fdom => />*. rewrite omap_some. rewrite -fdomP mem_fdom => />*. auto => />. smt(). 
  rewrite omap_none => />*. rewrite (_:(None = m.[x]) = !(m.[x] <> None)). auto => />. case m.[x] => />*. rewrite -fdomP mem_fdom => />*. qed.

op fsingl (x:'a) (y:'b) : ('a,'b) fmap = empty.[x<-y].

op ofset (f:'a->'b) (xs:'a fset) : ('a,'b) fmap =
  ofmap (Map.offun (fun a => if a \in xs then Some (f a) else None )).

lemma fdom_ofset (f:'a->'b) (xs:'a fset) :
  fdom (ofset f xs) = xs.
  rewrite /ofset fsetP => /> x. auto => />. rewrite mem_fdom.
do split.
move => H.
  have : (ofmap ((Map.offun (fun (a : 'a) => if a \in xs then Some (f a) else None)))).[x] = 
           Some (oget (ofmap ((Map.offun (fun (a : 'a) => if a \in xs then Some (f a) else None)))).[x]).
  rewrite get_some => />. rewrite getE ofmapK.
  apply/Finite.finiteP => /=. exists (elems xs) => />x0. rewrite Map.offunE => />. 
  move :H. smt(@SmtMap). rewrite Map.getE => />. rewrite Map.offunK => />. smt(@SmtMap).
  move => H.
  have : (ofmap ((Map.offun (fun (a : 'a) => if a \in xs then Some (f a) else None)))).[x] = 
           Some (oget (ofmap ((Map.offun (fun (a : 'a) => if a \in xs then Some (f a) else None)))).[x]).
rewrite getE ofmapK => />.
  apply/Finite.finiteP => /=. exists (elems xs) => />. smt(@SmtMap). rewrite !Map.getE. rewrite !Map.offunK => />. rewrite !H => />.
  pose m := (ofmap ((Map.offun (fun (a : 'a) => if a \in xs then Some (f a) else None)))).
  rewrite -mem_fdom fdomP.
  case (m.[x]) => />.
 qed.

lemma ofset_some (f:'a->'b) (s:'a fset) (i:'a) :
  i \in s => (ofset f s).[i] = Some (f i).
  rewrite /ofset => />*. rewrite get_some. rewrite -mem_fdom fdomP. rewrite getE ofmapK.
  apply/Finite.finiteP => /=. exists (elems s) => /> x. rewrite Map.getE Map.offunK => />*. rewrite -memE. smt(). 
  rewrite Map.getE Map.offunK. smt(). congr. rewrite getE ofmapK. 
  apply/Finite.finiteP => /=. exists (elems s) => /> x. rewrite Map.getE Map.offunK => />*. rewrite -memE. smt(). 
  rewrite Map.getE Map.offunK. smt(). qed.

lemma ofset_none (f:'a->'b) (s:'a fset) (i:'a) :
  !(i \in s) => (ofset f s).[i] = None.
  rewrite /ofset => />*. rewrite get_none. rewrite -mem_fdom fdomP. rewrite getE ofmapK.
  apply/Finite.finiteP => /=. exists (elems s) => /> x. rewrite Map.getE Map.offunK => />*. rewrite -memE. smt(). 
  rewrite Map.getE Map.offunK. smt(). auto => />. qed. 

lemma get_ofset (f:'a->'b) (s:'a fset) (i:'a) :
  (ofset f s).[i] = if i \in s then Some (f i) else None.
  case (i \in s) => />*. rewrite ofset_some => />*. rewrite ofset_none => />*. qed.

op fjoin (f: 'b -> 'b -> 'b) (m1 : ('a,'b) fmap) (m2 : ('a,'b) fmap) : ('a,'b) fmap =
  ofmap (Map.offun (fun x => ojoin f m1.[x] m2.[x] )).

lemma mem_fjoin x (f:'b->'b->'b) (m1 : ('a,'b) fmap) (m2 : ('a,'b) fmap) : 
  x \in fjoin f m1 m2 <=> (x \in m1 || x \in m2).
  rewrite domE /fjoin getE ofmapK. 
  apply/Finite.finiteP => /=. 
  exists (elems (fdom m1 `|` fdom m2)) => /> x0. 
  rewrite Map.getE Map.offunK => />. 
  rewrite setUE. 
  rewrite -mem_oflist elemsK mem_oflist mem_cat. 
  rewrite -mem_oflist -mem_oflist !elemsK. 
  move => H. rewrite !fdomP. smt(@SmtMap). 
  rewrite Map.getE Map.offunK. rewrite !domE => />*. case m1.[x] => />*. case m2.[x] => />*. qed.

lemma fdom_fjoin f (m1 m2 : ('a,'b) fmap) :
  fdom (fjoin f m1 m2) = fdom m1 `|` fdom m2.
  rewrite fsetP => />*. rewrite in_fsetU. rewrite !mem_fdom !mem_fjoin => />*. smt(). qed.

lemma get_fjoin (f:'b->'b->'b) xs ys (i:'a) :
  (fjoin f xs ys).[i] = (ojoin f xs.[i] ys.[i]).
  case (i \in xs) => /> H. case (i \in ys) => /> H0. 
  rewrite ojoin_some_lr. rewrite -fdomP mem_fdom => />. 
  rewrite /fjoin getE ofmapK. apply/Finite.finiteP => /=. 
  exists (elems (fdom xs `|` fdom ys)) => /> x.
  rewrite Map.getE Map.offunK => />. rewrite setUE. rewrite -mem_oflist elemsK mem_oflist mem_cat. rewrite -mem_oflist -mem_oflist !elemsK.
  rewrite !fdomP => />. case xs.[x] => />. 
  rewrite Map.getE Map.offunK => />. move :H H0. rewrite -!mem_fdom !fdomP. case (xs.[i]) => />H. case (ys.[i]) => />H0.
  rewrite /fjoin getE ofmapK. apply/Finite.finiteP => /=. 
   exists (elems (fdom xs `|` fdom ys)) => />x . rewrite Map.getE Map.offunK => />. 
  rewrite setUE. rewrite -mem_oflist elemsK mem_oflist mem_cat. rewrite -mem_oflist -mem_oflist !elemsK.
  rewrite !fdomP => />. case xs.[x] => />.
  rewrite Map.offunE => />.
  rewrite /fjoin getE ofmapK. apply/Finite.finiteP => /=. exists (elems (fdom xs `|` fdom ys)) => />x.  rewrite Map.getE Map.offunK => />. rewrite -memE in_fsetU !fdomP => />. move => H2. apply (some_ojoin f) => />.
  rewrite !Map.getE !Map.offunK => />. qed.

op toassoc ['a 'b] (m:('a,'b) fmap) : ('a * 'b) list =
  fold (fun (a:'a) (xs:('a * 'b) list) => oapp (fun (b:'b) => (a,b) :: xs) xs m.[a]) [] (fdom m).

op ffoldl (f:'c -> 'a -> 'b -> 'c) (z:'c) (m:('a,'b) fmap) : 'c =
  foldl (fun c a => f c a (oget m.[a])) z (elems (fdom m)).

lemma fall_seq (p1:'a->'b->bool) (p2:'a->'b->bool) (xs:('a,'b)fmap) :
    fall p1 xs /\ fall (fun i x => p1 i x => p2 i x) xs => fall p2 xs.
    rewrite !fallP => />. smt(). qed.

lemma fall_seq' (p1:'a->'b->bool) (p2:'a->'b->bool) (xs:('a,'b)fmap) :
    fall p1 xs /\ (forall i x, p1 i x => p2 i x) => fall p2 xs.
    rewrite !fallP => />*. smt().  qed.

lemma fall_fmap p (f:'b->'c) (xs:('a,'b)fmap) :
    fall p (fmap f xs) = fall (fun i => p i \o f) xs.
    rewrite !fallP => />*. rewrite eq_logical /(\o) => />.
do split. 
move => H a; move : (H a) => H0.
move => H1.
have : p a (oget (fmap f xs).[a]).  rewrite H => />. rewrite fdom_map => />. rewrite get_map omap_some => />. rewrite -fdomP => />.
move => H a H1. rewrite get_map omap_some => />. rewrite -fdomP => />. rewrite fdom_map in H1 => />. rewrite H => />. rewrite fdom_map in H1 => />.
qed.

lemma fmerge_fmap (f:'b1->'c2->'d) (f1:'b->'b1) (f2:'c->'c2) (xs:('a,'b)fmap) (ys:('a,'c)fmap) :
  fmerge f (fmap f1 xs) (fmap f2 ys) = fmerge (fun b c => f (f1 b) (f2 c)) xs ys.
  rewrite /fmerge /uncurry => />. rewrite -fmap_eqIn => />. rewrite !fdom_map => />. rewrite !fdom_fzip => />. rewrite !fdom_map => />. 
move => i.
rewrite in_fsetI => />*. rewrite !map_some => />*. rewrite mem_fzip !mem_map => />*. rewrite -!mem_fdom => />*. rewrite mem_fzip => />*. rewrite -!mem_fdom => />*. 
  rewrite !fzip_some => />*. rewrite !fdom_map in_fsetI => />*. rewrite in_fsetI => />*.
  rewrite !map_some => />*. rewrite -mem_fdom => />*. rewrite -mem_fdom => />*. qed.  

lemma fall_fzip' (p1:'a->'b->bool) (p2:'a->'c->bool) (p:'a->'b*'c->bool) (xs:('a,'b)fmap) (ys:('a,'c)fmap) :
  fall p1 xs /\ fall p2 ys /\ (forall a x y, p1 a x /\ p2 a y => p a (x,y)) => fall p (fzip xs ys).
  rewrite !fallP => /> H H0 H1 a. rewrite get_fzip => />. rewrite fdom_fzip. move => H2. rewrite ozip_some => />. rewrite -fdomP. move :H2. rewrite in_fsetI => />*. rewrite -fdomP. move :H2. rewrite in_fsetI => />*. rewrite H1. rewrite H => />*. rewrite in_fsetI in H2 => />*. move :H2. auto => />. rewrite H0 => />*. move :H2. rewrite in_fsetI => />*. qed.

lemma fall_and (p1 p2:'a->'b->bool) (xs:('a,'b)fmap) :
  (fall p1 xs /\ fall p2 xs) = fall (fun i x => p1 i x /\ p2 i x) xs.
  rewrite !fallP => />. rewrite eq_logical => />. auto => />. smt(@SmtMap). qed.

lemma fmap_fst_fzip (f:'b*'c->'b) (xs:('a,'b) fmap) (ys:('a,'c) fmap) :
  fdom xs = fdom ys => f = fst => fmap f (fzip xs ys) = xs.
  rewrite -fmap_eqIn => />H. rewrite !fdom_map fdom_fzip => />*. rewrite H fsetIid => />*. 
  rewrite map_some => />*. rewrite mem_fzip => />*. rewrite -!mem_fdom => />*. rewrite H => />*. 
  rewrite fzip_some => />*. rewrite H fsetIid => />*. 
  rewrite some_oget => />*. rewrite -fdomP => />*. rewrite H => />*. qed.

lemma fmap_fst_fzip' (f:'b*'c->'d) (g:'b->'d) (xs:('a,'b) fmap) (ys:('a,'c) fmap) :
  fdom xs = fdom ys => f = g \o fst => fmap f (fzip xs ys) = fmap g xs.
  auto => /> *.  rewrite -fmap_comp. congr. rewrite fmap_fst_fzip => />*. qed.

lemma fmap_snd_fzip (f:'b*'c->'c) (xs:('a,'b) fmap) (ys:('a,'c) fmap) :
  fdom xs = fdom ys => f = snd => fmap f (fzip xs ys) = ys.
  rewrite -fmap_eqIn => />H. rewrite !fdom_map fdom_fzip => />*. rewrite H fsetIid => />*. 
  rewrite map_some => />*. rewrite mem_fzip => />*. rewrite -!mem_fdom => />*. rewrite H => />*. 
  rewrite fzip_some => />*. rewrite H fsetIid => />*. 
  rewrite some_oget => />*. rewrite -fdomP => />*. qed.
  
lemma fmap_snd_fzip' (f:'b*'c->'d) (g:'c ->'d) (xs:('a,'b) fmap) (ys:('a,'c) fmap) :
  fdom xs = fdom ys => f = g \o snd => fmap f (fzip xs ys) = fmap g ys.
  auto => />*.  rewrite -fmap_comp. congr. rewrite fmap_snd_fzip => />*. qed.

lemma fzip_map_fst (f:'a->'b->'d) (xs:('a,'b) fmap) (ys:('a,'c) fmap) :
  fzip (map f xs) ys = map (fun a (bc:_*_) => (f a bc.`1,bc.`2)) (fzip xs ys).
  rewrite -fmap_eqIn => />. rewrite !fdom_fzip !fdom_map !fdom_fzip => /> i. rewrite in_fsetI => />*.
  rewrite !get_map !get_fzip => />*. rewrite !get_map => />*. rewrite omap_some => />*. rewrite -fdomP => />*. rewrite !ozip_some => />*. rewrite -fdomP => />*. rewrite -fdomP => />*. rewrite -fdomP => />*. qed.

lemma fzip_map_snd (f:'a->'c->'d) (xs:('a,'b) fmap) (ys:('a,'c) fmap) :
  fzip xs (map f ys) = map (fun a (bc:_*_) => (bc.`1,f a bc.`2)) (fzip xs ys).
  rewrite -fmap_eqIn => />*. rewrite !fdom_fzip !fdom_map !fdom_fzip => />i. rewrite in_fsetI => />*.
  rewrite !get_map !get_fzip => />*. rewrite !get_map => />*. rewrite omap_some => />*. rewrite -fdomP => />*. rewrite !ozip_some => />*. rewrite -fdomP => />*. rewrite -fdomP => />*. rewrite -fdomP => />*. qed.

lemma ofset_eq (f g:'a->'b) (iss jss:'a fset) :
  iss = jss /\ fsetall (fun x => f x = g x) iss => ofset f iss = ofset g jss.
  auto => />. rewrite -fmap_eqIn => />. rewrite !fdom_ofset => /> H i H0. 
  rewrite !ofset_some => />. move :H. rewrite fsetallP => /> ->. done. done. qed.

lemma fmap_ofset (f:'b->'c) (g:'a->'b) iss :
  fmap f (ofset g iss) = ofset (f \o g) iss.
  rewrite -fmap_eqIn => />*. rewrite fdom_map !fdom_ofset => />*. rewrite !get_map => />*. rewrite !get_ofset => />. smt(). qed.

op fredom (iss:'a fset) (xs:('a,'b) fmap) : ('a,'b) fmap =
  ofset (fun i => oget xs.[i]) iss.

lemma fdom_fredom (iss:'a fset) (xs:('a,'b) fmap) :
  fdom (fredom iss xs) = iss.
  rewrite /fredom fdom_ofset => />*. qed.

lemma ofassoc_ofset (f:'a->'b) (xs:'a fset) :
  ofassoc (map (fun x => (x,f x)) (elems xs)) = ofset f xs.
  rewrite -fmap_eqIn => />*. rewrite fdom_ofassoc fdom_ofset => />*. rewrite -map_comp /(\o) map_id => />*. rewrite elemsK => />*. rewrite ofset_some => />*. rewrite ofassoc_get => />*. rewrite assoc_map_r => />. smt(). qed.
