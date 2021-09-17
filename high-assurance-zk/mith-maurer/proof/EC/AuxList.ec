require import AllCore Int List FSet SmtMap Distr DList.
require import Aux.

(* Lists *)

abbrev cons x (xs:'a list) = x :: xs.
abbrev uncons (xs:'a list) = (head witness xs,behead xs).
abbrev cat (x y:'a list) = x ++ y.

op zipl ['a 'b] (b:'b) (s : 'a list) (t : 'b list) =
  with s = x :: s' => (x,head b t) :: zipl b s' (behead t)
  with s = [] => [].

op zipr ['a 'b] (a:'a) (s : 'a list) (t : 'b list) =
  with t = y :: t' => (head a s,y) :: zipr a (behead s) t'
  with t = [] => [].

op rconss (xxs:('a list) list) (ys : 'a list) : ('a list) list =
    map (fun (xs_y:_*_) => xs_y.`1 ++ [xs_y.`2]) (zipr [] xxs ys).

lemma size_zipl y (xs:'a list) (ys:'b list) :
  size (zipl y xs ys) = size xs.
  elim xs ys => />. move => l H ys. rewrite H => />. qed.

lemma size_zipr x (xs:'a list) (ys:'b list) :
  size (zipr x xs ys) = size ys.
  elim ys xs => />. move => l H xs. rewrite H => />. qed.

lemma size_foldl_z (f:'b list->'a->'b list) (z:'b list) (xs:'a list) :
  (forall b a, a \in xs => size (f b a) = size b) =>
  size (foldl f z xs) = size z.
  move => H. move :H. elim xs z => />. move => x l H z H0. 
  have : (forall (b : 'b list) (a : 'a), a \in l => size (f b a) = size b) => size (foldl f (f z x) l) = size (f z x). rewrite H => />. move => b a H1. rewrite H0 => />. smt(). clear H.
  move => H1. rewrite H1 => />. move => b a H2. rewrite H0 => />. smt(). 
  rewrite H0 => />. qed.

lemma size_cons x (xs:'a list) :
  size (x :: xs) = 1 + size xs.
  case xs => />*. qed.

lemma size_nenil (x:'a list) :
  0 < size x <=> (x <> []).
  case x => />*. smt(size_ge0). qed.

lemma size_behead (xs:'a list) :
  size (behead xs) = max 0 (size xs - 1).
  case xs => />l. have : 0 <= size l. rewrite size_ge0 => />*. smt(). qed.

lemma foldl_map (f:'b->'a->'b) (z:'b) (g:'c->'a) xs :
  foldl f z (map g xs) = foldl (fun b c => f b (g c)) z xs.
  elim xs z => />. move => x l H z. rewrite H => />. qed.

op foldl1 def (f:'a->'a->'a) (xs:'a list) : 'a =
  with xs = [] => def
  with xs = y :: ys => foldl f y ys.

lemma index_out x (xs:'a list) :
  !(x \in xs) => index x xs = size xs.
  elim xs => />x0 xs0 H H0. rewrite index_cons => />*. case (x=x0) => />H1. rewrite H => />*. move :H0. rewrite H1 => />*. algebra. qed.

lemma rcons_cat (xs:'a list) x :
  rcons xs x = xs ++ [x].
  elim xs => />*. qed.

lemma foldl_rcons (f:'b->'a->'b) z xs x :
  foldl f z (rcons xs x) = f (foldl f z xs) x.
  move :z. elim xs => />*. smt(). qed.

lemma foldl1_rcons def (f:'a->'a->'a) xs x :
  (forall x y, f x y = f y x) =>
  (forall x y z, f x (f y z) = f (f x y) z) =>
  foldl1 def f (rcons xs x) = (foldl f x xs).
  move => H1 H2. case xs => />. move => x0 l. rewrite foldl_rcons => />.
  elim l x0 => />x0. rewrite H1 => />.
  move => x1 H3 l. rewrite H3 => />. congr. rewrite H2 => />.
  qed.

op iseq (n:int) = iota_ 0 n.

lemma mkseq_iseq (f:int->'a) n :
  mkseq f n = map f (iseq n).
  rewrite /mkseq /iseq => />. qed.

lemma iseq_nil n :
  n <= 0 => iseq n = [].
  rewrite /iseq => />*. rewrite iota0 => />*. qed. 

lemma iseq_1 :
  iseq 1 = [0].
  rewrite /iseq => />*. smt (iotaS iota0). qed.

lemma iseq_5 :
  iseq 5 = [0;1;2;3;4].
  rewrite /iseq => />*. smt (iotaS iota0). qed.
  
lemma iseq_6 :
  iseq 6 = [0;1;2;3;4;5].
  rewrite /iseq => />*. smt (iotaS iota0). qed.

lemma iseq_10 :
  iseq 10 = [0;1;2;3;4;5;6;7;8;9].
  rewrite /iseq => />*. smt (iotaS iota0). qed.  

lemma size_iseq n :
  size (iseq n) = max 0 n.
  rewrite /iseq size_iota => />*. qed.

lemma index_nil (x:'a) :
  index x [] = 0.
  rewrite /index => />*. qed.
 
lemma rcons_nenil (xs:'a list) (x:'a) :
  rcons xs x <> [].
  elim xs => />. qed.

lemma iseq_succ n :
  0 <= n => iseq (n+1) = rcons (iseq n) n.
  auto => />*. rewrite /iseq iota_add => />*. rewrite rcons_cat iota1 => />?. qed.

lemma iseq_rcons n :
  0 < n => iseq n = rcons (iseq (n-1)) (n-1).
  move => H. rewrite (_:n=(n-1)+1). algebra. rewrite iseq_succ => />. smt(). qed.

lemma nth_iseq d i n :
  nth d (iseq n) i = if (0 <= i /\ i < n) then i else d.
  rewrite /iseq. elim/natind:n => />n H. rewrite iota0 => />*. smt().
  rewrite iotaSr => />H0. rewrite nth_rcons => />*. rewrite size_iota => />. smt(). qed.

lemma in_iseq i n :
  i \in iseq n = (0 <= i /\ i < n).
  rewrite /iseq mem_iota => />*. qed.

lemma index_rcons x y (s : 'a list):
  index x (rcons s y) = if x \in s then index x s else if x=y then size s else 1 + size s.
  elim s => />. rewrite index_cons => />*.
  move => x0 l H. rewrite !index_cons => />. rewrite H => />*. clear H. case (x=x0) => />*. case (x \in l) => />*. case (x=y) => />*. algebra. qed.

lemma index_iseq i n :
  i \in iseq n => index i (iseq n) = i.
  elim/natind n => />. move => n H H0. move :H0. rewrite !iseq_nil => />*. 
  move => n H H0 H1. move :H1. rewrite !iseq_succ => />H1. rewrite index_rcons => />*. case (i=n) => />.
   have : !(n \in iseq n). move :H1. rewrite mem_rcons => />*. rewrite in_iseq => />*. progress. rewrite H2 => />*. rewrite size_iseq => />*. rewrite ge0_max => />*.
  move => H2. have : i \in iseq n. move :H1. rewrite mem_rcons => />H1. move :H1. rewrite H2 => />*. move :H1. rewrite mem_rcons => />*. rewrite H0 => />*. qed.

op replicate (i:int) (x:'a) : 'a list =
  map (fun _ => x) (iseq i).

lemma last_map_some (da:'a) (db:'b) (f:'a->'b) (xs:'a list) :
  0 < size xs => last db (map f xs) = f (last da xs).
  move => H. rewrite -(last_map f) => />. 
  move : H. 
  elim/last_ind xs => />*. rewrite !map_rcons => />*.
  rewrite !last_rcons => />*. qed.

lemma rcons_map (f : 'a -> 'b) s x y:
  y = f x => rcons (map f s) y = map f (rcons s x).
  rewrite map_rcons => />*. qed.

lemma onth_map (f:'a->'b) (xs:'a list) :
  forall i, onth (map f xs) i = omap f (onth xs i).
  elim xs => />? ? ? i. case (i=0) => />*; smt(). qed.

lemma onth_none (xs:'a list) :
  forall i, (i < 0 || size xs <= i) => onth xs i = None.
  elim xs => />. move => x l H i H0. case (i<0) => />H1. smt(). case (i=0) => />. smt(size_ge0). smt(). qed.

lemma onth_rcons xs (x:'a) :
  forall i, onth (rcons xs x) i = if i = size xs then Some x else onth xs i.
  elim xs => />.
  move => x0 l H i. case (i=0) => />. case (0=1+size l) => />H0. smt(size_ge0). move => H0. case (i=1+size l) => />. rewrite H => />*. move => H1. clear H. move :H0 H1. move :i. elim l => />. smt().
  move => x1 l H i H0 H1. case (i-1=0) => />. move => H2. have : (i-1) <> 0 => (i-1) <> 1 + size l => onth (rcons l x) ((i-1) - 1) = onth l ((i-1) - 1). rewrite H => />*. smt(). clear H. rewrite H2 => />. move => H3. rewrite H3 => />*. smt(size_ge0). qed.

lemma onth_s0 (xs:'a list) :
  forall i, (i < 0) => onth xs i = None.
  elim xs => />.
  move => x l H i H0. have : !(i=0). smt(). move => H2. rewrite H2 => />. rewrite H => />. smt(). qed.

lemma onth_gesize (xs:'a list) :
  forall i, (size xs <= i) => onth xs i = None.
  move => i.
  elim xs i => />. move => x l H i H0. case (i=0) => />. smt(size_ge0).
  move => H1. rewrite H => />. smt(). qed.

lemma onth_behead_gt0 (xs:'a list) i :
  0 <= i /\ 1 <= size xs => onth (behead xs) i = onth xs (i+1).
  move :i. case xs => /> x l i.  
  case l => />*. have : !(i + 1 = 0). smt(). smt(). smt(). qed.
  
op lsame (p:'b->'c->bool) (xs:'b list) (ys:'c list) : bool =
  forall n, 0 <= n => osame p (onth xs n) (onth ys n)
  axiomatized by lsameP.

op nolast (xs:'a list) : 'a list =
  take (size xs - 1) xs.

lemma nolast_cons x (xs:'a list) :
  nolast (cons x xs) = if 0 < size xs then x::nolast xs else [].
  rewrite /nolast => />*. smt(). qed.

lemma nolast_rcons (xs:'a list) x :
  nolast (rcons xs x) = xs.
  elim xs => />*. rewrite nolast_cons size_rcons => />*. smt(size_ge0). qed.

lemma size_nolast (xs:'a list) :
  size (nolast xs) = max 0 (size xs - 1).
  elim/last_ind xs => />*. rewrite nolast_rcons => />*. smt(size_rcons size_ge0). qed.

lemma nolast_last (xs : 'a list) z0:
  xs <> [] => rcons (nolast xs) (last z0 xs) = xs.
  elim xs z0 => />. move => x l H. rewrite nolast_cons => />. case (0 < size l) => />.
  move => H1. rewrite H => />. smt(size_nenil size_ge0).
  clear H. case l => />l. smt(size_ge0). qed.

lemma onth_size0 (ys:'a list) :
  (forall (n : int), 0 <= n => onth ys n = None) => 0 = size ys.
  case ys => />*. smt(size_ge0). qed.

lemma lsame_cons p (x:'a) xs (y:'b) ys :
  lsame p (x::xs) (y::ys) = (p x y /\ lsame p xs ys).
  rewrite !lsameP => />*. rewrite eq_logical.
  split. move => H. have : osame p (if 0 = 0 then Some x else onth xs (0 - 1)) (if 0 = 0 then Some y else onth ys (0 - 1)). rewrite H => />. simplify. move => H1. rewrite H1 => />n Hn.
  have : osame p (if (n+1) = 0 then Some x else onth xs ((n+1) - 1)) (if (n+1) = 0 then Some y else onth ys ((n+1) - 1)). rewrite H => />. smt(). have : !(n+1=0). smt(). move => H2. rewrite !H2 => />. 
  move => |> H1 H2 n Hn. case (n=0) => />. move => H3. rewrite H2 => />. smt(). qed.
 
lemma lsame_size (p:'a->'b->bool) xs ys :
  lsame p xs ys => size xs = size ys.
  elim: xs ys => />. move => ys. rewrite /lsame => />H. have : is_none (onth ys 0). rewrite H => />. move :H. case ys => />. 
  move => x l H ys H0.
  move :H H0. elim: ys => />.
  move => H. rewrite lsameP => />H0. have : osame p (if 0 = 0 then Some x else onth l (0 - 1)) None. rewrite H0 => />. progress. 
  move => x0 l0 H H0 H1. move :H1. rewrite lsame_cons => />H1 H2. rewrite (H0 l0) => />. 
  qed.

lemma lsame_map p (f:'a1->'a2) (g:'b1->'b2) xs ys :
  lsame p (map f xs) (map g ys) = lsame (fun x y => p (f x) (g y)) xs ys. 
  rewrite !lsameP => />. rewrite eq_logical. 
  split.
  move => H n H0.
  have : osame p (onth (map f xs) n) (onth (map g ys) n). rewrite H => />.  
  rewrite !onth_map. case (onth xs n). case (onth ys n) => />. case (onth ys n) => />. 
  move => H n H1. rewrite !onth_map. 
  have : osame (fun (x : 'a1) (y : 'b1) => p (f x) (g y)) (onth xs n) (onth ys n). smt(). 
  case (onth xs n). case (onth ys n) => />*. case (onth ys n) => />*. qed.

lemma lsame_comp p1 p2 (xs:'a list) (ys:'b list) :
  lsame p1 xs ys => lsame p2 xs ys = lsame (fun x y => p1 x y => p2 x y) xs ys.
  rewrite !lsameP => />H10. rewrite eq_logical.
  split. 
  move => H n H0.
  have : osame p1 (onth xs n) (onth ys n). rewrite H10 => />. move => H1. 
  have : osame p2 (onth xs n) (onth ys n). rewrite H => />. move => H2.
  clear H10 H. move :H1 H2.
  case (onth xs n). case (onth ys n) => />. case (onth ys n) => />.
  move => H n H0. 
  have : osame p1 (onth xs n) (onth ys n). rewrite H10 => />. move => H1. clear H10.
  have : 0 <= n => osame (fun (x : 'a) (y : 'b) => p1 x y => p2 x y) (onth xs n) (onth ys n). rewrite H => />. clear H. move => H2.
  move : H1 H2. case (onth xs n) => />. case (onth ys n) => />. move => x y H1 H2. rewrite H2 => />. 
  qed.

lemma lsame_cons_left1 p x dy (xs:'a list) (ys:'b list) :
  lsame p (x::xs) ys => p x (head dy ys).
  rewrite /lsame => />H. have : osame p (if 0 = 0 then Some x else onth xs (0 - 1)) (onth ys 0). rewrite H => />. simplify. clear H. case ys => />. qed.

lemma lsame_cons_left2 p x (xs:'a list) (ys:'b list) :
  lsame p (x::xs) ys => lsame p xs (behead ys).
  move => H.
  have : size (cons x xs) = size ys. rewrite (lsame_size p (cons x xs) ys) => />*.
  move => H0.
  move :H. rewrite -(head_behead ys witness). smt(size_ge0).
  rewrite lsame_cons => |>. qed.

lemma lsame_rcons p (x:'a) xs (y:'b) ys :
  lsame p (rcons xs x) (rcons ys y) = (p x y /\ lsame p xs ys). 
  rewrite eq_logical. 
  split. 
  move => H.
  split. 
  have : size (rcons xs x) = size (rcons ys y). 
  rewrite (lsame_size p (rcons xs x) (rcons ys y)) => />H. 
  rewrite !size_rcons => />H0. have : size xs = size ys. smt(). 
   rewrite !lsameP in H => /> H1. 
   have : osame p (onth (rcons xs x) (size xs)) (onth (rcons ys y) (size xs)). 
   rewrite H => />. rewrite size_ge0 => />. 
   rewrite !onth_rcons. rewrite -H1 => />*. 
   move :H. rewrite !lsameP => /> H n Hn. 
   have : osame p (onth (rcons xs x) n) (onth (rcons ys y) n).  
   rewrite H => />. 
   rewrite !onth_rcons. 
   have : size (rcons xs x) = size (rcons ys y). 
   rewrite (lsame_size p (rcons xs x) (rcons ys y)) => />. 
   rewrite lsameP => />. rewrite !size_rcons => />. move => H1.
   have : size xs = size ys. smt(). move => H2.
   case (n=size xs) => />. rewrite H2 => />. 
   rewrite !onth_none => />. smt(). 
   move => H3. rewrite -H2 H3 => />. move => /> H1 H2.
   have : size xs = size ys. rewrite (lsame_size p xs ys) => />. move => H3.
   move :H2. rewrite !lsameP => /> K0 n K1. rewrite !onth_rcons => />. 
   case (n = size xs) => />. rewrite H3 => />. 
   move => H4. rewrite -H3 H4 => />. rewrite K0 => />.  qed.

lemma lsame_rcons_left1 p x dy (xs:'a list) (ys:'b list) :
  lsame p (rcons xs x) ys => p x (last dy ys).
   move => H. 
   have : size (rcons xs x) = size ys. 
   rewrite (lsame_size p (rcons xs x) ys) => />. 
   auto => /> H0. 
   rewrite -(nolast_last ys dy). rewrite -size_nenil => />. rewrite size_rcons in H0 => />. smt(size_ge0). 
   rewrite size_rcons in H0 => />. 
   move :H. rewrite last_rcons => />. rewrite -(nolast_last ys witness) => />. rewrite -size_nenil => />. rewrite -H0 => />. smt(size_ge0).
   rewrite lsame_rcons => />. rewrite last_rcons => />. qed.

lemma lsame_rcons_left2 p x (xs:'a list) (ys:'b list) :
  lsame p (rcons xs x) ys => lsame p xs (nolast ys).
  auto => />H. have : size (rcons xs x) = size ys. rewrite (lsame_size p (rcons xs x) ys) => />*. auto => />H1. rewrite -(nolast_last ys witness). rewrite -size_nenil => />. rewrite size_rcons in H1 => />. rewrite -H1 => />. smt(size_ge0). auto => />*. 
  move :H1. rewrite size_rcons => />H1.
  move :H. rewrite -(nolast_last ys witness) => />. rewrite -size_nenil => />. smt(size_ge0).
  rewrite lsame_rcons => />. rewrite !nolast_rcons => />. qed.

lemma lsame_nil (p:'a->'b->bool) xs ys:
  xs=[] => lsame p xs ys = (ys=[]).
  move => ?. rewrite eq_logical. split. move => ?. have : size xs = size ys. rewrite (lsame_size p xs ys) => />*. auto => />*. smt(size_eq0).  smt().  qed.

op allsame (xs:'a list) : bool =
  with xs = [] => true
  with xs = y :: ys => all (fun x => x = y) ys.

(*lemma size_indices (xs:'a list) is :
    size (indices is xs) = size is.
    rewrite /indices size_map => />*. qed.*)

lemma in_nth (x:'a) (xs:'a list) :
  x \in xs = (exists i, 0 <= i /\ i < size xs /\ x = nth witness xs i). 
  rewrite eq_logical => />*. auto => />*. 
  elim xs => /> x0 l. smt().
  move => H H0. 
  split. 
  case (x=x0) => />. exists 0 => />. smt(size_ge0).
  move => H1 H2. move :H. rewrite H2 => />i Hi1 Hi2 H3. 
  exists (i+1) => />. split. smt(). split. smt(). smt().
  move => i H1 H2. smt(). qed.

lemma nth_in_zip (i:int) (x:'a list) (y:'b list) :
  (size x = size y /\ 0 <= i /\ i < size x) => (nth witness x i,nth witness y i) \in zip x y.
  rewrite in_nth => />H1 H2 H3. exists i => />*. rewrite size_zip => />*. rewrite -nth_zip => />*. rewrite !(nth_onth) !(onth_nth witness) => />. rewrite size_zip => />. rewrite H1 min_eq => />. rewrite -H1 => />. rewrite -H1 min_eq => />. qed.

lemma nth_in d (xs:'a list) i :
  0 <= i < size xs =>
  nth d xs i \in xs.
  elim xs i => />*. smt(). smt(size_ge0). qed.

lemma lsame_eq (xs ys : 'a list) :
  (xs = ys) = (lsame (fun x y => x = y) xs ys). 
  rewrite eq_logical => />. split.
  rewrite lsameP => /> n Hn. case (onth ys n) => />. 
  move => H. apply (eq_from_nth witness) => />. apply (lsame_size (fun (x y : 'a) => x = y) xs ys) => />.
  have : size xs = size ys. apply (lsame_size (fun (x y : 'a) => x = y) xs ys) => />. move => sz. 
  move => i Hi1 Hi2. move :H. rewrite lsameP => />H.
  have : osame (fun (x y : 'a) => x = y) (onth xs i) (onth ys i). rewrite H => />. rewrite !(onth_nth witness) => />. progress. rewrite -sz Hi2 => />. qed.

lemma list_eq (xs ys:'a list) :
  (xs=ys) = ((size xs = size ys) /\ (forall n, 0 <= n < size xs => nth witness xs n = nth witness ys n)).
  rewrite eq_logical => />H H0. apply (eq_from_nth witness) => />. qed.

lemma map_eq_same (f:'a->'b) (g:'a->'b) xs :
  (map f xs = map g xs) = (forall x, x \in xs => f x = g x).
  rewrite eq_logical => />. split.
  move => H x. rewrite in_nth => |>i Hi1 Hi2.
  have : nth witness (map f xs) i = nth witness (map g xs) i. rewrite H => />. rewrite !(nth_map witness) => />.
  move =>H. apply (eq_from_nth witness) => />. rewrite !size_map => />.
  move => i. rewrite !size_map => />Hi1 Hi2. rewrite !(nth_map witness) => />. rewrite H => />. rewrite nth_in => />. qed.

lemma nosmt ind_n (p : int -> 'a list -> bool):
    forall xs, p (size xs) [] /\ (forall y ys, p (size xs-size ys) ys => p (size xs-size ys-1) (y::ys)) => p 0 xs.
  move => xs. pose sz := size xs. rewrite (_:0=sz-size xs). rewrite /sz => />*. 
  elim xs sz => />*. smt(). qed.

lemma take_rcons_le n (xs:'a list) x :
  n <= size xs => take n (rcons xs x) = take n xs.
  auto => />*. rewrite rcons_cat take_cat => />*. case (n=size xs) => />*. rewrite take_size => />*. rewrite cats0 => />*. 
  have : n < size xs. smt(). auto => />*.  qed.

lemma take1 n (xs:'a list) :
  n = 1 => take n xs = if 0 < size xs then [head witness xs] else [].
  case (0 < size xs) => />*. rewrite -(head_behead xs witness) => />*. rewrite -size_nenil => />*.
  rewrite take0 => />*. rewrite (_:xs=[]). smt(size_ge0). auto => />*. qed.

lemma map_eq (f g:'a->'b) xs :
  (forall i, 0 <= i < size xs => f (nth witness xs i) = g (nth witness xs i)) => map f xs = map g xs.
  move => R. rewrite (eq_from_nth witness (map f xs) (map g xs)) => />. rewrite !size_map => />. move => i H H1. rewrite !(nth_map witness) => />. rewrite size_map in H1 => />*. rewrite size_map in H1 => />*. rewrite R => />. rewrite size_map in H1 => />. qed.

lemma none_assoc (xs : ('a * 'b) list) k :
  k \in map fst xs => assoc xs k <> None.
  rewrite assocTP => />*. qed.

lemma some_assoc_uniq (s : ('a * 'b) list) (a : 'a) (b : 'b) :
  uniq (map fst s) => mem s (a, b) => assoc s a = Some b.
  auto => />*. rewrite -mem_assoc_uniq => />*. qed.

lemma some_assoc (xs : ('a * 'b) list) k :
  k \in map fst xs => assoc xs k = Some (nth witness xs (index k (map fst xs))).`2.
  elim xs => /> x ll H1. rewrite index_cons => />*. rewrite (prod_id x) assoc_cons => />*.
  case (k=x.`1) => />*. 
  smt(index_ge0). qed.

lemma take_min n1 n2 (xs:'a list) :
  take n1 (take n2 xs) = take (min n1 n2) xs.
  elim xs n1 n2 => /> x l H n1 n2. 
  case (n1 <= 0) => />. case (n2 <= 0) => />. 
  move => H2 H1. 
  have : min n1 n2 <= 0. smt(). smt(). smt().
  move => H1. case (n2 <= 0) => />. move => H2. smt().
  move => H2. rewrite H1 => />. have : !min n1 n2 <= 0. smt(). move => N12. rewrite N12 => />.
  rewrite H => />. clear H. congr. smt(). qed.

lemma take_min' n1 n2 :
  take<:'a> n1 \o take n2 = take (min n1 n2) .
  rewrite fun_ext /(\o) => />*. rewrite take_min => />*. qed.

lemma head_nolast d (xs:'a list) :
  1 < size xs => head d (nolast xs) = head d xs.
  move => ?. rewrite /nolast -!nth0_head nth_take => />*. smt(). smt(size_ge0). qed.

lemma last_behead d (xs:'a list) :
  1 < size xs => last d (behead xs) = last d xs.
  move => ?. rewrite -!nth_last => />*. rewrite nth_behead => />*. rewrite size_behead => />*. smt(size_ge0). rewrite size_behead => />*. smt(). qed.

lemma nolast_behead (xs:'a list) :
  1 < size xs => nolast (behead xs) = behead (nolast xs).
  rewrite /nolast => />. rewrite size_behead => />.
  elim xs => /> x l H H0. have : ! (size l <= 0). smt().
  move => S. move :H. rewrite !ge0_max => />. smt(size_ge0). rewrite size_ge0 => />. move => H.
  rewrite S => />. qed.

lemma head_last_eq d (xs:'a list) :
  size xs <= 1 => last d xs = head d xs.
  case xs => />. move => x l H. have : size l = 0. smt(size_ge0).
  move => S. rewrite (last_nth witness) => />. rewrite S => />. qed.

lemma zipl_rcons dy (xs:'a list) x (ys:'b list)  :
  zipl dy (rcons xs x) ys = rcons (zipl dy xs ys) (x,nth dy ys (size xs)).
  elim xs ys => />l . rewrite nth0_head => />.
  move => H ys. 
  rewrite H => />*. congr. rewrite eq2 => />*. rewrite nth_behead => />*. rewrite size_ge0 => />?*. congr. algebra. qed.

lemma drop_behead n (xs:'a list) :
  0 <= n => 0 < size xs => drop n (behead xs) = drop (n+1) xs. 
  move => ? ?. rewrite -(head_behead xs witness). rewrite -size_nenil => />*. 
  rewrite drop_cons => />*. have : 0 < n + 1. smt(). auto => />*.  qed.

lemma nth_drop d n (xs:'a list) i :
  0 <= i => 0 <= n <= size xs => nth d (drop n xs) i = nth d xs (n+i).
  move => H .
  elim/natind:n xs => />. move => n H0 xs H1 H2.
  have : n=0. smt(). move => N0. rewrite N0 drop0 => />. 
  move => n Hn H0 xs H1 H2. rewrite (_:n+1+i=(n+i)+1). algebra. rewrite -nth_behead => />. 
  smt(). rewrite -H0 => />. rewrite size_behead => />. rewrite ge0_max => />. smt(size_ge0).
  smt(size_ge0). rewrite drop_behead => />. smt(size_ge0). qed.
 
lemma behead_drop (xs:'a list) :
  behead xs = drop 1 xs.
  case xs => />*. rewrite drop0 => />*. qed.

lemma nth_cons d x (l:'a list) i :
  nth d (cons x l) i = if i=0 then x else nth d l (i-1).
  rewrite /nth => />*. qed.

lemma zip_cons x (xs:'a list) y (ys:'b list) :
  zip (cons x xs) (cons y ys) = (x,y) :: zip xs ys.
  rewrite /zip => />*. qed.

lemma map_congr (f g:'a->'b) (xs ys:'a list) :
  f = g /\ xs = ys => map f xs = map g ys.
  auto => />*. qed.

lemma head_take_some d n (xs:'a list) : 
  0 < n => head d (take n xs) = head d xs.
  case xs => />*. smt(). qed.

lemma take_behead n (xs:'a list) :
  0 <= n => take n (behead xs) = behead (take (1 + n) xs).
  case xs => />*. have : !(1+n<=0). smt(). auto => />*.  qed.

lemma assoc_map_r (f:'a->'b) (xs:'a list) i :
  assoc (map (fun a => (a,f a)) xs) i = if i \in xs then Some (f i) else None.
  elim xs => />*. rewrite assoc_cons => />*. smt(). qed.

lemma assoc_map_prod (f:'b->'c) (xs:('a*'b) list) (i:'a) :
  assoc (map (prod idfun f) xs) i = omap f (assoc xs i).
  elim xs => />. move => x l. rewrite !assoc_cons /idfun => />H. 
  rewrite !H => />. rewrite (prod_id x) => />. rewrite !assoc_cons => />. 
  clear H. case (i=x.`1) => />. qed.

lemma unzip1_eq_nth (xs:('a*'b) list) ys i :
  0 <= i < size xs =>
  unzip1 xs = ys => (nth witness xs i).`1 = nth witness ys i.
  elim xs i => />. move => i Hi1 Hi2. smt().
  move => x l H i Hi1 Hi2 H0. case (i=0) => />.
  move => H1. rewrite (nth_map witness) => />. smt(). qed.

lemma assoc_nth_some d (xs:('a*'b) list) i :
  0 <= i < size xs => uniq (unzip1 xs) => 
  assoc xs (nth d xs i).`1 = Some (nth d xs i).`2.
  elim xs i => />. rewrite assoc_nil => />. smt().
  move => x l H i Hi1 Hi2. case (i=0) => />. move => H1.
  rewrite (prod_id x) assoc_cons => />. move => H2 H3.
  have : (nth d l (i - 1)).`1 <> x.`1. move :H2. rewrite in_nth => />. rewrite negb_exists => />H4. have : ! (0 <= (i-1) /\ (i-1) < size (unzip1 l) /\ x.`1 = nth witness (unzip1 l) (i-1)). rewrite H4 => />. rewrite !negb_and => H5. case H5 => />. smt().
  rewrite !(nth_map d) => />. smt().
  rewrite size_map => />H5. case H5 => />. smt(). smt().
  move => H4. rewrite H4 => />. rewrite H => />. smt(). qed.

lemma assoc_iseq_some d (xs:(int*'b) list) i :
  unzip1 xs = iseq (size xs) =>
  0 <= i < size xs =>
  oget (assoc xs i) = (nth d xs i).`2.
  rewrite -(zip_unzip xs) => /> H H0 H1. 
  rewrite nth_onth (onth_nth (witness,witness)) => />. 
  rewrite assoc_zip => />. 
  rewrite !size_map => />. 
  rewrite (onth_nth witness) => />. 
  move :H1. rewrite size_zip !size_map min_eq => /> H1. 
  move :H. rewrite size_zip !size_map unzip1_zip => />. rewrite !size_map => />.
  rewrite min_eq => />H2. rewrite !H2 => />. rewrite !index_iseq => />. rewrite in_iseq => />. 
  move :H H1. rewrite !size_zip !size_map unzip1_zip => />. rewrite !size_map => />.
  rewrite nth_zip => />. rewrite !size_map => />.
  rewrite min_eq => />H1 H2. 
  rewrite !(nth_map witness) => />. rewrite !H1 !index_iseq => />. rewrite in_iseq => />.
  rewrite !H1 !index_iseq => />. rewrite in_iseq => />. qed.

lemma mem_nil :
  mem [<:'a>] = pred0.
  rewrite /mem => />*. qed.

lemma zip_nil_l (ys: 'b list) :
  zip [<:'a>] ys = [].
  elim ys => />*. qed.

lemma zip_nil_r (xs: 'a list) :
  zip xs [<:'b>] = [].
  elim xs => />*. qed.
  
op del_index (i:int) (xs:'a list) : 'a list = take i xs ++ drop (i+1) xs.  

lemma size2E (xs:'a list) :
  size xs = 2 => xs = [nth witness xs 0;nth witness xs 1].
  case xs => />l H. move :H. case l => />l. move => H. 
  have : size l = 0. smt(). move => H0.
  rewrite -size_eq0 //. qed.

op foldl_iseq (f:'b ->  int -> 'b) (z:'b) (n:int) : 'b.

axiom foldl_iseqE f (z:'b) n :
  foldl_iseq f z n = foldl f z (iseq n).

op all_iseq (p:int -> bool) (n:int) : bool =
  foldl_iseq (fun b i => b && p i) true n.

lemma all_rcons p (xs:'a list) x :
  all p (rcons xs x) = (all p xs /\ p x).
  rewrite -cats1 => />*. rewrite all_cat => />*. qed.

lemma all_iseqE p n :
  all_iseq p n = all p (iseq n).
  rewrite /all_iseq foldl_iseqE => />*. elim/natind: n => />*. 
  rewrite !iseq_nil => />*. 
  rewrite !iseq_succ => />*. rewrite foldl_rcons => />*. smt(all_rcons).  qed.

abbrev iall (p:int -> 'a -> bool) (xs:'a list) : bool =
  all_iseq (fun i => p i (nth witness xs i)) (size xs).

lemma onth_zipl (xs:'a list) :
  forall (dy:'b) ys i, onth (zipl dy xs ys) i = omap (fun x => (x,nth dy ys i)) (onth xs i).
  elim xs => />x l H dy ys i. rewrite H => />. clear H.
  case (i=0) => />. rewrite nth0_head => />.
  move => I0. case (0 < i) => />I1. congr. rewrite fun_ext => />y. congr. rewrite nth_behead => />. smt().
  rewrite !onth_none => />. smt(size_ge0). qed.

lemma onth_zipr (ys:'b list) :
  forall (dx:'a) (xs:'a list) i, onth (zipr dx xs ys) i = omap (fun y => (nth dx xs i,y)) (onth ys i).
  elim ys => />x l H dx xs i. rewrite H => />. clear H.
  case (i=0)  => />. rewrite nth0_head => />.
  move => I0. case (0 < i) => />I1. congr. rewrite fun_ext => />y. congr. rewrite nth_behead => />. smt().
  rewrite !onth_none => />. smt(size_ge0). qed.

lemma zipl_zip y (xs:'a list) (ys:'b list) :
  size xs = size ys => zipl y xs ys = zip xs ys.
  elim xs ys => />. move => ys. elim ys => />.
  move => x l H0 zs H1. rewrite H0 => />. rewrite size_behead => />. rewrite ge0_max => />. smt(size_ge0). rewrite -H1 => />.
  rewrite -(head_behead zs witness) => />. rewrite -size_nenil => />. smt(size_ge0).
  qed.

lemma zipr_zip x (xs:'a list) (ys:'b list) :
  size xs = size ys => zipr x xs ys = zip xs ys.
  elim ys xs => />. move => xs. elim xs => />.
  move => y l H0 zs H1. rewrite H0 => />. rewrite size_behead => />. rewrite ge0_max => />. smt(size_ge0). rewrite H1 => />.
  rewrite -(head_behead zs witness) => />. rewrite -size_nenil => />. smt(size_ge0).
  qed.

lemma unzip2_zipr (x:'a) (xs:'a list)(ys:'b list) :
  unzip2 (zipr x xs ys) = ys.
  move :xs. elim ys => />l H ys. rewrite H => />*. qed.

lemma unzip1_zipl (y:'b) (xs:'a list) (ys:'b list) :
  unzip1 (zipl y xs ys) = xs.
  move :ys. elim xs => />l H xs. rewrite H => />*. qed.

lemma replicate0 n (x:'a) :
  n <= 0 => replicate n x = [].
  rewrite /replicate => />H. rewrite iseq_nil => />. qed.

lemma replicate_succ n (x:'a) :
  0 <= n => replicate (n+1) x = cons x (replicate n x).
  move => H. rewrite /replicate => />. rewrite iseq_succ => />.
  rewrite map_rcons => />. move :H. elim/natind:n => />n. 
  move => N0 N1. rewrite !iseq_nil => />. 
  move => N0 H N1. rewrite !iseq_succ => />. rewrite !map_rcons => />. rewrite H => />. qed.

lemma unzip2_zipl (y:'b) (xs:'a list) (ys:'b list) :
  size ys <= size xs =>
  unzip2 (zipl y xs ys) = ys ++ replicate (size xs - size ys) y.
  move :ys. elim xs => />. move => ys H. rewrite replicate0 => />.
  have : 0 <= size ys. rewrite size_ge0 => />. move => H0. have : size ys = 0. smt().
  move => H1. rewrite size_eq0 in H1 => />. rewrite H1 => />. 
  have : 0 <= size ys. rewrite size_ge0 => />. move => H0. have : size ys = 0. smt().
  move => H1. rewrite size_eq0 in H1 => />. rewrite H1 => />.
  move => l H ys H0. move :H H0. elim ys l => />. 
  move => l H H0. rewrite H => />. rewrite size_ge0 => />.  
  rewrite (_:1+size l = size l+1). algebra. rewrite replicate_succ => />. rewrite size_ge0 => />. 
  move => l0 H l1 H1 H2. rewrite H1 => />. smt(). congr. congr. algebra. qed.

lemma onth_zip (xs:'a list) (ys:'b list) i :
  size xs = size ys =>
  onth (zip xs ys) i = if 0 <= i < size xs then Some (nth witness xs i, nth witness ys i) else None.
  move => Sz. case (0 <= i < size xs) => />.
  move => Hi1 Hi2. rewrite !(onth_nth (witness,witness)) => />. rewrite size_zip Sz min_eq => />. move => ?. rewrite -Sz Hi2. rewrite nth_zip => />. 
  move => Hi. rewrite onth_none => />. rewrite size_zip Sz min_eq => />. smt(). qed.

lemma zip_eq (xs1 xs2:'a list) (ys1 ys2 : 'b list) :
  size xs1 = size xs2 =>
  size xs1 = size ys1 =>
  size xs2 = size ys2 =>
  (zip xs1 ys1 = zip xs2 ys2) = (xs1=xs2 /\ ys1=ys2).
  move => Sz1 Sz2 Sz3. rewrite eq_logical => />. rewrite !lsame_eq !lsameP => />H. split.
  move => n Hn. have : osame (fun (x y : 'a * 'b) => x = y) (onth (zip xs1 ys1) n) (onth (zip xs2 ys2) n). rewrite H => />. rewrite !onth_zip => />. rewrite !Hn => />. case (n < size xs2) => />. move => Sz4. rewrite Sz1 Sz4 => />. rewrite !(onth_nth witness) => />. rewrite Sz1 => />.
  move => Sz4. rewrite Sz1 Sz4 => />. rewrite !onth_none => />. smt(). smt().
  move => n Hn. have : osame (fun (x y : 'a * 'b) => x = y) (onth (zip xs1 ys1) n) (onth (zip xs2 ys2) n). rewrite H => />. rewrite !onth_zip => />. rewrite !Hn => />. case (n < size xs2) => />. move => Sz4. rewrite Sz1 Sz4 => />. rewrite !(onth_nth witness) => />. rewrite -Sz2 Sz1 => />. rewrite -Sz3 Sz4 => />. 
  move => Sz4. rewrite Sz1 Sz4 => />. rewrite !onth_none => />. smt(). smt(). qed.

lemma rcons_eq (xs ys:'a list) (x y:'a) :
  (rcons xs x = rcons ys y) = (xs=ys/\x=y).
  rewrite eq_logical => />H.
  have : size xs = size ys. have : size (rcons xs x) = size (rcons ys y). rewrite H => />. rewrite !size_rcons => />. smt(). move => Sz.
  move : H. rewrite !lsame_eq !lsameP => />H. split.
  move => n Hn. case (n < size xs) => />. move => Hn1. have : osame (fun (x0 y0 : 'a) => x0 = y0) (onth (rcons xs x) n) (onth (rcons ys y) n). rewrite H => />. rewrite !onth_rcons -Sz => />. have : ! n = size xs. smt(). move => Hn2. rewrite !Hn2 => />. 
  move => Hn1. rewrite !onth_none => />. smt(). smt(). 
  have : osame (fun (x0 y0 : 'a) => x0 = y0) (onth (rcons xs x) (size xs)) (onth (rcons ys y) (size xs)). rewrite H => />. rewrite size_ge0 => />. rewrite !onth_rcons => />. rewrite Sz => />. qed.

lemma mkseq_eq_same (f g:int->'a) (i:int) :
  (mkseq f i = mkseq g i) = (forall k, 0 <= k < i => f k = g k).
  rewrite eq_logical => />. split.
  elim/natind:i => />i.
  move => I0. move => H k Hk1 Hk2. have : false. smt(). progress.
  move => I0. move => H. rewrite !mkseqS => />H0 k Hk1 Hk2.
  move :H0. rewrite rcons_eq => />H0 H1. move :H. rewrite H0 => />H. 
  case (k = i) => />. move => K. rewrite H => />. smt().
  move => H. apply (eq_from_nth witness) => />. rewrite !size_mkseq => />.
  move => k. rewrite !size_mkseq => />Hk1 Hk2. 
  rewrite !nth_mkseq => />. smt(). smt(). rewrite H => />. smt(). qed.

lemma onth_iseq i n :
  onth (iseq n) i = if (0 <= i < n) then Some i else None.
  elim/natind:n => />n. move => N. rewrite !iseq_nil => />. smt().
  move => N H. rewrite !iseq_succ => />. rewrite !onth_rcons => />.
  rewrite size_iseq => />. rewrite ge0_max => />. rewrite H => />. 
  case (i=n) => />. have : 0 <= n < n + 1. smt(). move => H0. rewrite H0 => />.
  move => H0. case (0 <= i < n) => />. move => H1 H2. have : i < n + 1. smt(). move => H3. rewrite H3 => />. 
  move => H1. have : ! (0 <= i < n + 1). smt(). move => H2. rewrite H2 => />. qed.

lemma iseq_eq (n1 n2:int) :
  0 <= n1 => 0 <= n2 =>
  (iseq n1 = iseq n2) = (n1 = n2). 
  rewrite eq_logical => />N1 N2 H. 
  have : size (iseq n1) = size (iseq n2). rewrite H !size_iseq => />. rewrite !size_iseq => />. rewrite !ge0_max => />. qed.

lemma assoc_in i (xs: ('a*'b) list) :
  i \in unzip1 xs => (i,oget (assoc xs i)) \in xs.
  elim xs i => />. move => x l H i H0.
  rewrite (prod_id x) => />. rewrite !assoc_cons => />. elim H0 => />H0. 
  case (i=x.`1) => />H1. rewrite H => />. qed.

(* Distributions *)

lemma dlist_djoin (d: 'a distr) n :
  dlist d n = djoin (replicate n d).
  elim/natind:n => />n.
  move => H. rewrite replicate0 => />. rewrite dlist0 => />. rewrite djoin_nil => />. 
  move => H H0. rewrite replicate_succ => />. rewrite djoin_cons => />. rewrite dlistS => />. rewrite H0 => />. qed.
