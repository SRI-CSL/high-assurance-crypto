require import Core Int List FSet SmtMap Distr.

op constfun (b:'b) (a:'a) : 'b = b.

(* Logic *)

lemma sym_eq (x y:'a) :
(x=y) <=> (y=x).
progress. qed.

lemma neg2 (b:bool) :
  !(!b) = b.
  smt(). qed.

lemma eq_logical (p1:bool) (p2:bool) :
  (p1 = p2) = (p1 <=> p2).
  smt(). qed.

lemma equivE p1 p2 :
    (p1 <=> p2) <=> ((p1 => p2) /\ (p2 => p1)).
    progress. qed.

lemma implies_and (p1 p2 p3:bool) :
  (p1 => p2) /\ (p1 => p2 => p3) => (p1 => p2 /\ p3).
  smt(). qed.

lemma if_then b (x y:'a) :
  b => (if b then x else y) = x.
   progress. rewrite H => />*. qed.

lemma if_else b (x y:'a) :
  !b => (if b then x else y) = y.
   progress. rewrite H => />*. qed.

(* Pairs *)

abbrev fst3 (x:'a*('b*'c)) = x.`1.
abbrev snd3 (x:'a*('b*'c)) = x.`2.`1.
abbrev thr3 (x:'a*('b*'c)) = x.`2.`2.

(*abbrev fst3' (x:'a*'b*'c) = x.`1.
abbrev snd3' (x:'a*'b*'c) = x.`2.
abbrev thr3' (x:'a*'b*'c) = x.`3.*)

type 'a array1 = 'a.
type 'a array2 = ('a * 'a).
type 'a array3 = 'a * ('a * 'a).
type 'a array4 = 'a * ('a * ('a * 'a)).
type 'a array5 = 'a * ('a * ('a * ('a * 'a))).
type 'a array6 = 'a * ('a * ('a * ('a * ('a * 'a)))).

abbrev nth0_3 (x:'a array3) : 'a = x.`1.
abbrev nth1_3 (x:'a array3) : 'a = x.`2.`1.
abbrev nth2_3 (x:'a array3) : 'a = x.`2.`2.

abbrev nth0_4 (x:'a array4) : 'a = x.`1.
abbrev nth1_4 (x:'a array4) : 'a = x.`2.`1.
abbrev nth2_4 (x:'a array4) : 'a = x.`2.`2.`1.
abbrev nth3_4 (x:'a array4) : 'a = x.`2.`2.`2.

abbrev nth0_5 (x:'a array5) : 'a = x.`1.
abbrev nth1_5 (x:'a array5) : 'a = x.`2.`1.
abbrev nth2_5 (x:'a array5) : 'a = x.`2.`2.`1.
abbrev nth3_5 (x:'a array5) : 'a = x.`2.`2.`2.`1.
abbrev nth4_5 (x:'a array5) : 'a = x.`2.`2.`2.`2.

abbrev nth0_6 (x:'a array6) : 'a = x.`1.
abbrev nth1_6 (x:'a array6) : 'a = x.`2.`1.
abbrev nth2_6 (x:'a array6) : 'a = x.`2.`2.`1.
abbrev nth3_6 (x:'a array6) : 'a = x.`2.`2.`2.`1.
abbrev nth4_6 (x:'a array6) : 'a = x.`2.`2.`2.`2.`1.
abbrev nth5_6 (x:'a array6) : 'a = x.`2.`2.`2.`2.`2.

op array1 (x1 : 'a) : 'a array1 =
 (x1).

op array2 (x1 x2 : 'a) : 'a array2 =
 (x1,(x2)).

op array3 (x1 x2 x3 : 'a) : 'a array3 =
 (x1,(x2,x3)).

op array4 (x1 x2 x3 x4 : 'a) : 'a array4 =
 (x1,(x2,(x3,x4))).

op array5 (x1 x2 x3 x4 x5 : 'a) : 'a array5 =
 (x1,(x2,(x3,(x4,x5)))).

op array6 (x1 x2 x3 x4 x5 x6 : 'a) : 'a array6 =
 (x1,(x2,(x3,(x4,(x5,x6))))).

op init_array5 (f:int -> 'a) : 'a array5 =
  array5 (f 0) (f 1) (f 2) (f 3) (f 4).

op set_array2 (xs:'a array2) (i:int) (x:'a) : 'a array2 =
  if i = 0 then (x,xs.`2)
  else if i = 1 then (xs.`1,x)
  else xs.

op set_array3 (xs:'a array3) (i:int) (x:'a) : 'a array3 =
  if i = 0 then (x,xs.`2)
  else (xs.`1,set_array2 xs.`2 (i-1) x).

op set_array4 (xs:'a array4) (i:int) (x:'a) : 'a array4 =
  if i = 0 then (x,xs.`2)
  else (xs.`1,set_array3 xs.`2 (i-1) x).

op set_array5 (xs:'a array5) (i:int) (x:'a) : 'a array5 =
  if i = 0 then (x,xs.`2)
  else (xs.`1,set_array4 xs.`2 (i-1) x).

op list_to_array1 (xs:'a list) : 'a array1 =
  array1 (nth witness xs 0).

op list_to_array2 (xs:'a list) : 'a array2 =
  array2 (nth witness xs 0) (nth witness xs 1).

op list_to_array3 (xs:'a list) : 'a array3 =
  array3 (nth witness xs 0) (nth witness xs 1) (nth witness xs 2).

op list_to_array4 (xs:'a list) : 'a array4 =
  array4 (nth witness xs 0) (nth witness xs 1) (nth witness xs 2) (nth witness xs 3).

op list_to_array5 (xs:'a list) : 'a array5 =
  array5 (nth witness xs 0) (nth witness xs 1) (nth witness xs 2) (nth witness xs 3) (nth witness xs 4).

op list_to_array6 (xs:'a list) : 'a array6 =
  array6 (nth witness xs 0) (nth witness xs 1) (nth witness xs 2) (nth witness xs 3) (nth witness xs 4) (nth witness xs 5).

lemma list_to_array2_cons x (xs:'a list) :
  list_to_array2 (x::xs) = (x,list_to_array1 xs).
  rewrite /list_to_array2 => />. qed.

lemma list_to_array3_cons x (xs:'a list) :
  list_to_array3 (x::xs) = (x,list_to_array2 xs).
  rewrite /list_to_array3 => />. qed.

lemma list_to_array4_cons x (xs:'a list) :
  list_to_array4 (x::xs) = (x,list_to_array3 xs).
  rewrite /list_to_array4 => />. qed.

lemma list_to_array5_cons x (xs:'a list) :
  list_to_array5 (x::xs) = (x,list_to_array4 xs).
  rewrite /list_to_array5 => />. qed.

lemma list_to_array6_cons x (xs:'a list) :
  list_to_array6 (x::xs) = (x,list_to_array5 xs).
  rewrite /list_to_array6 => />. qed.

op nth_array1 (x:'a array1) (i:int) : 'a =
  if i=0 then x
  else witness.

op nth_array2 (x:'a array2) (i:int) : 'a =
  if i=0 then fst x
  else if i=1 then snd x
  else witness.

op nth_array3 (x:'a array3) (i:int) : 'a =
  if i=0 then nth0_3 x
  else if i=1 then nth1_3 x
  else if i=2 then nth2_3 x
  else witness.

op nth_array4 (x:'a array4) (i:int) : 'a =
  if i=0 then nth0_4 x
  else if i=1 then nth1_4 x
  else if i=2 then nth2_4 x
  else if i=3 then nth3_4 x
  else witness.

op nth_array5 (x:'a array5) (i:int) : 'a =
  if i=0 then nth0_5 x
  else if i=1 then nth1_5 x
  else if i=2 then nth2_5 x
  else if i=3 then nth3_5 x
  else if i=4 then nth4_5 x
  else witness.

op nth_array6 (x:'a array6) (i:int) : 'a =
  if i=0 then nth0_6 x
  else if i=1 then nth1_6 x
  else if i=2 then nth2_6 x
  else if i=3 then nth3_6 x
  else if i=4 then nth4_6 x
  else if i=5 then nth5_6 x
  else witness.

lemma nth_array2_cons (x:'a) xs i :
  nth_array2 (x,xs) i = if i=0 then x else nth_array1 xs (i-1).
  rewrite /nth_array2 => />. case (i=0) => />H0. case (i=1) => />H1. smt(). qed.

lemma nth_array3_cons (x:'a) xs i :
  nth_array3 (x,xs) i = if i=0 then x else nth_array2 xs (i-1).
  rewrite /nth_array3 => />. case (i=0) => />H0. case (i=1) => />H1. case (i=2)=>/>H2. smt(). qed.

lemma nth_array4_cons (x:'a) xs i :
  nth_array4 (x,xs) i = if i=0 then x else nth_array3 xs (i-1).
  rewrite /nth_array4 => />. case (i=0) => />H0. case (i=1) => />H1. case (i=2)=>/>H2. case (i=3)=>/>H3. smt(). qed.

lemma nth_array5_cons (x:'a) xs i :
  nth_array5 (x,xs) i = if i=0 then x else nth_array4 xs (i-1).
  rewrite /nth_array5 => />. case (i=0) => />H0. case (i=1) => />H1. case (i=2)=>/>H2. case (i=3)=>/>H3. case (i=4)=>/>H4. smt(). qed.

lemma nth_array6_cons (x:'a) xs i :
  nth_array6 (x,xs) i = if i=0 then x else nth_array5 xs (i-1).
  rewrite /nth_array6 => />. case (i=0) => />H0. case (i=1) => />H1. case (i=2)=>/>H2. case (i=3)=>/>H3. case (i=4)=>/>H4. case (i=5) =>/>H5. smt(). qed.

lemma nth_list_to_array1 (xs:'a list) i :
  i=0 =>
  nth_array1 (list_to_array1 xs) i = nth witness xs i.
  rewrite /nth_array1 /list_to_array1 => />. qed.

lemma nth_list_to_array2 (xs:'a list) i :
  0 <= i <= 1 =>
  nth_array2 (list_to_array2 xs) i = nth witness xs i.
  move => H. case xs => />x l. rewrite list_to_array2_cons => />. rewrite nth_array2_cons => />. case (i=0) => />H0. case (i=1) => />H1. rewrite nth_list_to_array1 => />. smt(). qed.

lemma nth_list_to_array3 (xs:'a list) i :
  0 <= i <= 2 =>
  nth_array3 (list_to_array3 xs) i = nth witness xs i.
  move => H. case xs => />x l. rewrite list_to_array3_cons => />. rewrite nth_array3_cons => />. case (i=0) => />H0. rewrite nth_list_to_array2 => />. smt(). qed.

lemma nth_list_to_array4 (xs:'a list) i :
  0 <= i <= 3 =>
  nth_array4 (list_to_array4 xs) i = nth witness xs i.
  move => H. case xs => />x l. rewrite list_to_array4_cons => />. rewrite nth_array4_cons => />. case (i=0) => />H0. rewrite nth_list_to_array3 => />. smt(). qed.

lemma nth_list_to_array5 (xs:'a list) i :
  0 <= i <= 4 =>
  nth_array5 (list_to_array5 xs) i = nth witness xs i.
  move => H. case xs => />x l. rewrite list_to_array5_cons => />. rewrite nth_array5_cons => />. case (i=0) => />H0. rewrite nth_list_to_array4 => />. smt(). qed.

lemma nth_list_to_array6 (xs:'a list) i :
  0 <= i <= 5 =>
  nth_array6 (list_to_array6 xs) i = nth witness xs i.
  move => H. case xs => />x l. rewrite list_to_array6_cons => />. rewrite nth_array6_cons => />. case (i=0) => />H0. rewrite nth_list_to_array5 => />. smt(). qed.

op prod (f: 'a -> 'c) (g: 'b -> 'd) (ab:'a*'b) : ('c*'d) =
  (f ab.`1,g ab.`2).

lemma prod_id (xy:'a*'b) :
  xy = (xy.`1,xy.`2).
  elim xy => />*.  qed.

lemma prod3_id (x:'a*('b*'c)) :
  x = (x.`1,(x.`2.`1,x.`2.`2)).
  elim x => /> x2.  elim x2 => />*. qed.

lemma prod3_id' (x:'a*'b*'c) :
  x = (x.`1,x.`2,x.`3).
  elim x => />x2. qed.
  
lemma eq2 (x y:'a*'b) :
    (x = y) = ((x.`1 = y.`1) /\ (x.`2 = y.`2)).
    case x => />*. case y => />*. qed.

lemma eq3 (x y:'a*('b*'c)) :
  (x = y) = ((x.`1 = y.`1) /\ (x.`2.`1 = y.`2.`1) /\ (x.`2.`2 = y.`2.`2)).
  case x => />*. case y => />*. rewrite !eq2 => />*. qed.

(* Option *)  

lemma oapp_some (f:'a->'b) (z:'b) (o:'a option) :
  o <> None => oapp f z o = f (oget o).
  case o => />*. qed.

lemma odflt_eq d (o1 o2:'a option) :
  (o1 <> Some d /\ o2 <> Some d /\ (odflt d o1 = odflt d o2)) => o1 = o2.
  case o1. case o2 => />*. smt(). case o2 => />*. smt(). qed.

lemma odflt_nodef d (o:'a option) :
  o <> None /\ o <> Some d => odflt d o <> d.
  case o => />*. qed.

lemma odflt_def d (o:'a option) :
  o = None || o = Some d => odflt d o = d.
  case o => />*. qed.

lemma odflt_some_eq d1 d2 (o1 o2:'a option) :
  o1 <> None /\ o2 <> None => (odflt d1 o1 = odflt d2 o2) => o1 = o2.
  case o1. progress. case o2 => />*. qed. 

lemma option_eq (x y : 'a option) :
  (((x = None) = (y = None)) /\ ((x <> None) => (y <> None) /\ oget x = oget y)) = (x = y).
  rewrite eq_logical => />.
  case x => />. case y => />. case y => />.
  qed.

lemma some_eq (x y : 'a) :
  Some x = Some y => x = y.
  by[]. qed.

lemma oget_eq (x y : 'a option) :
  oget x <> witness => (oget x = oget y) => (x = y).
  case x => /> /#. qed.

lemma some_oget_eq (x y:'a option) :
  x <> None => y <> None => (oget x = oget y) => (x = y).
  case x => /> /#. qed.

lemma some_oget (x:'a option) :
  x <> None => Some (oget x) = x.
  case x => />*. qed.

op osame (p:'a->'b->bool) (x:'a option) (y:'b option) =
  with x = None => is_none y
  with x = Some a => oapp (p a) false y.

lemma osame_eq (ox oy: 'a option) :
  osame (fun x y => x=y) ox oy = (ox = oy).
  case ox => />*. case oy => />*. case oy => />*. qed.

lemma osame_none (p:'a->'b->bool) o1 o2 :
  o1 = None /\ o2 = None => osame p o1 o2.
  case o1 => />*. qed.

lemma osame_none_l (p:'a->'b->bool) o2 :
  osame p None o2 = (o2 = None).
  case o2 => />*. qed.

lemma osame_none_r (p:'a->'b->bool) o1 :
  osame p o1 None = (o1 = None).
  case o1 => />*. qed.

lemma osame_some (p:'a->'b->bool) o1 o2 : 
  o1 <> None /\ o2 <> None => osame p o1 o2 = p (oget o1) (oget o2).
  case o1 => /> />x. case o2 => />. qed.

lemma omap_comp (f:'b->'c) (g:'a->'b) x :
  omap f (omap g x) = omap (f \o g) x.
  case x => />*. qed.

lemma omap_some (f:'a->'b) (x:'a option) :
  x <> None => omap f x = Some (f (oget x)).
  case x => />*. qed.

lemma omap_none (f:'a->'b) (x:'a option) :
  (x = None) => omap f x = None.
  case x => />*. qed.

op ojoin (f:'a->'a->'a) (x:'a option) (y:'a option) : 'a option =
  with x = None => y
  with x = Some a => oapp (fun b => Some (f a b)) (Some a) y.

lemma ojoin_some f (x y:'a option) :
  x <> None || y <> None => ojoin f x y <> None.
  case x => />. case y => />. qed.

lemma ojoin_some_l f (x y:'a option) :
  x <> None => ojoin f x y = Some (oapp (f (oget x)) (oget x) y).
  case x => />*. case y => />*. qed.

lemma ojoin_some_r f (x y:'a option) :
  y <> None => ojoin f x y = Some (oapp (transpose f (oget y)) (oget y) x).
  case y => />*. case x => />*. qed.

lemma ojoin_some_lr f (x y:'a option) :
  x <> None /\ y <> None => ojoin f x y = Some (f (oget x) (oget y)).
  case x => /> /#. qed.

lemma some_ojoin f (x y:'a option) :
  ojoin f x y <> None => (x <> None \/ y <> None).
  case x => /> /#. qed.

lemma ojoin_none f (x y:'a option) :
  x = None /\ y = None => ojoin f x y = None.
  case x => />*. qed.

op omerge (f:'a->'b->'c) (x:'a option) (y:'b option) : 'c option =
  with x = None => None
  with x = Some a => oapp (fun b => Some (f a b)) None y.

lemma omerge_some (f:'a->'b->'c) (x:'a option) (y:'b option) :
  x <> None => y <> None => omerge f x y = Some (f (oget x) (oget y)).
  case x => />. case y => />. qed.

op ozip (x:'a option) (y:'b option) : ('a*'b) option =
  oapp (fun a => oapp (fun b => Some (a,b)) None y) None x.

lemma ozip_some (x:'a option) (y:'b option) :
  x <> None => y <> None => ozip x y = Some (oget x,oget y).
  case x => />. case y => />. qed.

lemma some_ozip (x:'a option) (y:'b option) :
  ozip x y <> None => (x <> None /\ y <> None).
  case x => />. case y => />. qed.

lemma ozip_none (x:'a option) (y:'b option) :
  x = None || y = None => ozip x y = None.
  case x => />. qed.

op ozip3 (x:'a option) (y:'b option) (z:'c option) : ('a*('b*'c)) option =
  (ozip x (ozip y z)).

lemma ozip3_some (x:'a option) (y:'b option) (z:'c option) :
  x <> None => y <> None => z <> None => ozip3 x y z = Some (oget x,(oget y,oget z)).
  rewrite /ozip3 => />*. rewrite !ozip_some => />*. qed.

lemma ozip3_none (o1: 'a option) (o2: 'b option) (o3: 'c option) :
  o1 = None || o2 = None || o3 = None => ozip3 o1 o2 o3 = None.
  case o1 => />. case o2 => />. qed.

lemma ozip_omap_fst (f:'a->'c) (o1:'a option) (o2:'b option) :
  ozip (omap f o1) o2 = omap (fun (xy:_*_) => (f xy.`1,xy.`2)) (ozip o1 o2).
  case o1 => />. case o2 => />. qed.

lemma ozip_omap_snd (f:'b->'c) (o1:'a option) (o2:'b option) :
  ozip o1 (omap f o2) = omap (fun (xy:_*_) => (xy.`1,f xy.`2)) (ozip o1 o2).
  case o1 => />. case o2 => />. qed.

lemma is_some_if (p:bool) (x:'a) :
  is_some (if p then Some x else None) = p.
  smt(). qed.

lemma nenone_some_if (p:bool) (x:'a) :
  ((if p then Some x else None) <> None) = p.
  smt(). qed.

lemma some_if_eq (p:bool) (x y:'a) :
  (Some x = if p then Some y else None) = (p /\ x = y).
  case p => />*. qed.

lemma none_if_eq (p:bool) (y:'a) :
  (None = if p then Some y else None) = (!p ).
  case p => />*. qed.

(* Sums *)

type ('a,'b) either = [ L of 'a | R of 'b ].

op either (f:'a->'c) (g:'b->'c) (e:('a,'b) either) : 'c =
  with e = L a => f a
  with e = R b => g b.

op unL (e:('a,'b) either) : 'a =
  with e = L a => a
  with e = R b => witness.

op unR (e:('a,'b) either) : 'b =
  with e = L a => witness
  with e = R b => b.

op isL (e:('a,'b) either) : bool =
  with e = L a => true
  with e = R b => false.

op isR (e:('a,'b) either) : bool =
  with e = L a => false
  with e = R b => true.

lemma isL_id (x:('a,'b) either) :
  isL x => L (unL x) = x.
  case x => />*. qed.

lemma isR_id (x:('a,'b) either) :
  isR x => R (unR x) = x.
  case x => />*. qed.

op eq_either (f:'a->'a->bool) (g:'b->'b->bool) (e1 e2:('a,'b) either) =
  with e1 = L x => either (f x) (constfun false) e2
  with e1 = R x => either (constfun false) (g x) e2.

lemma not_isR (x:('a,'b) either) :
  isL x = ! isR x. case x => />. qed.

lemma not_isL (x:('a,'b) either) :
  isR x = ! isL x. case x => />. qed.

(* Distribution *)

(*NB: cannot use congr on sample *)
op sample : 'a distr -> 'a.

axiom sampleE (d:'a distr) :
  sample d \in d.

lemma ll_dmap (xs:'a distr) (f:'a->'b) :
  is_lossless (dmap xs f) = is_lossless xs.
  rewrite /is_lossless => />*. rewrite weight_dmap /#. qed.

lemma rnd_funi' ['a] (d : 'a distr) x y:
  is_funiform d => mu1 d x = mu1 d y.
  smt(rnd_funi). qed.

lemma dmap_dprod' ['a1 'a2 'b1 'b2] (d1 : 'a1 distr ) (d2 : 'a2 distr ) (f1 : 'a1 -> 'b1) (f2 : 'a2 -> 'b2) :
  dmap d1 f1 `*` dmap d2 f2 = dmap (d1 `*` d2) (prod f1 f2).
  rewrite /prod. rewrite dmap_dprod => />*.
  qed.

lemma dmap_supp' ['a 'b] (d : _ distr) f x y :
  y = f x => x \in d => y \in dmap<:'a, 'b> d f.
  move => H H0. rewrite H dmap_supp => |>. qed.

lemma dapply1E (f : 'a -> 'b) (d : 'a distr) (b : 'b):
  mu1 (dapply f d) b = mu d ((pred1 b) \o f).
  rewrite /dapply => />*. rewrite dmap1E => />*. qed.

lemma dapplyE (f : 'a -> 'b) (d : 'a distr) (P : 'b -> bool):
  mu (dapply f d) P = mu d (P \o f).
  rewrite /dapply => />*. rewrite dmapE => />*. qed.

(* Higher-order *)

op uncurry (f : 'a -> 'b -> 'c) (xy:'a*'b) : 'c =
  f xy.`1 xy.`2.
op uncurry3 (f : 'a -> 'b -> 'c ->'d) (xyz:'a*('b*'c)) : 'd =
  f xyz.`1 xyz.`2.`1 xyz.`2.`2.

(* Order *)

lemma succ_ge_id (x:int) :
  x <= x + 1.
  smt(). qed.

lemma succ_ge (x y : int) :
  (x+1 <= y) => (x <= y).
  smt(). qed.

lemma succ_ge_gt (x y : int) :
  (x+1 <= y) => (x < y).
  smt(). qed.

lemma gt_ge_succ (x y:int) :
    x < y + 1 = x <= y.
    smt(). qed.

lemma gt_ge_neq (x y : int) :
    (x <= y /\ x <> y) = x < y.
    smt(). qed.

lemma gt_succ (x:int) :
  x < x + 1.
  smt(). qed.

lemma gt_trans (a b c:int) :
  a < b => b < c => a < c.
  smt(). qed.

lemma min_gt (x y z:int) :
  x < y => x < z => x < min y z.
  smt(). qed.

lemma min_eq (x:int) :
  min x x = x.
  smt(). qed.

lemma max_eq (x:int) :
  max x x = x.
  smt(). qed.

lemma gt0_max (x y:int):
  x < y => 0 <= y => max 0 y = y.
  smt(). qed.

lemma ge0_gt_max0 (x y:int) :
  0 <= x => x < y => max 0 (y-x) = y-x.
  smt(). qed.

lemma succ_le (n y:int) :
  n + 1 <= y => n <= y.
  smt(). qed.

lemma succ_lt (n y:int) :
  n + 1 <= y => n < y.
  smt(). qed.

lemma gt0_succ (x:int) :
  0 < x => 0 < x + 1.
  smt(). qed.

lemma ge1_gt0 (x:int) :
  1 <= x = 0 < x.
  smt().
  qed.

lemma max_ge0 (x y:int) :
   0 <= x /\ 0 <= y => (1 + x = y) => (x = max 0 (y-1)).
   smt().
   qed.

lemma ge0_succ (x:int) :
  0 <= x => 1 <= 1 + x.
  smt(). qed.

lemma ge0_gt0_succ (x:int) :
  0 <= x => 0 < 1 + x.
  smt().
  qed.

lemma ge0_max (x:int) :
  0 <= x => max 0 x = x.
  smt().
  qed.

lemma succ_ge0 (x y:int) :
  0 <= x => 0 <= y => 0 <= x + y.
  smt(). qed.

lemma ge_min (n1 n2:int) :
  n1 <= n2 => min n1 n2 = n1.
  smt(). qed.

lemma le_succ (x y: int):
  x <= y => x <= 1 + y.
  smt(). qed.

lemma max_r (x y:int) :
  x <= y => max x y = y.
  smt(). qed.

lemma max_l (x y:int) :
  y <= x => max x y = x.
  smt(). qed.

lemma succ_gt0 (x y:int) :
  0 <= x => 1 + x <= y => 0 < y.
  smt(). qed.

lemma min_assoc (x y z:int) :
  min x (min y z) = min (min x y) z. smt(). qed.
