require import AllCore Int List.
require import Aux AuxList.

(* A init-fixed size array *)
theory Array.

  type 'a array.
  op get (xs:'a array) (i:int) : 'a.
  op set (xs:'a array) (i:int) (x:'a) : 'a array.
  op init (sz:int) (f:int->'a) : 'a array.
  op size : 'a array -> int.

  op of_list (l:'a list) : 'a array = init (List.size l) (fun i => nth witness l i).
  op to_list (t:'a array) = mkseq (fun i => get t i) (size t).
  op to_assoc (t:'a array) = zip (iseq (size t)) (to_list t).

  op create sz (x:'a) = init sz (fun _ => x).
  op singl i (x:'a) = init 1 (fun j => if j=i then x else witness).
  op imap (f:int -> 'a -> 'b) (xs:'a array) : ('b array) =
    init (size xs) (fun j => f j (get xs j)).
  abbrev map (f:'a->'b) (xs:'a array) : ('b array) = imap (fun _ => f) xs.
  op merge (f:'a -> 'b -> 'c) (xs:'a array) (ys:'b array) : ('c array) =
    init (min (size xs) (size ys)) (fun i => f (get xs i) (get ys i)).
  abbrev zip (xs:'a array) (ys:'b array) = merge (fun x y => (x,y)) xs ys.
  op filter (p:int->'a->bool) (xs:'a array) : ('a array) =
    init (size xs) (fun j => if p j (get xs j) then (get xs j) else witness).
  (*op empty (sz:int) : ('a array) = create sz witness<:'a>.*)
  op all (f : int -> 'a -> bool) (t : 'a array) =
    all (fun i => f i (get t i)) (iseq (size t)).
  op allsame (xs :'a array) =
    all (fun i => all (fun j => get xs i = get xs j) (iseq (size xs))) (iseq (size xs)).

  abbrev zip3 (xs:'a array) (ys:'b array) (zs:'c array) : ('a*('b*'c)) array =
    zip xs (zip ys zs).

  op eq_array (f:'a->'b->bool) (m1:'a array) (m2:'b array) : bool =
    size m1 = size m2 /\ all (fun i => f (get m1 i) (get m2 i) ) (iseq (size m1)).

  op lsize def (xxs : ('b array) list) : int = foldl1 def min (map size xxs).

  op concat (xxs : ('b array) list) : ('b list) array =
    foldl (fun xs b => merge rcons xs b) (create (lsize 0 xxs) []) xxs.

  axiom get_out (t:'a array) i : !(0 <= i < size t) => get t i = witness.

  axiom tP (t1 t2: 'a array) :
    t1 = t2 <=> (size t1 = size t2 /\ forall i, 0 <= i < size t1 => get t1 i = get t2 i).

  axiom get_set_eqE (m : 'b array) (x : int) b :
    0 <= x < size m => get (set m x b) x = b.

  axiom get_set_neqE (m : 'a array) (x y : int) (a:'a) :
    (y <> x) => get (set m x a) y = get m y.

  axiom size_init sz (f:int->'a) :
    size (init sz f) = max 0 sz.

  axiom size_set (xs:'a array) i x :
    size (set xs i x) = size xs.

  axiom size_ge0 (xs:'a array) :
    0 <= size xs.

  lemma get_setE (m : 'a array) (x y : int) (a:'a) :
    get (set m x a) y = if 0 <= y < size m /\ y=x then a else get m y.
    case (0 <= y < size m /\ y=x) => />. move => H1 H2. rewrite get_set_eqE => />.
    move => /> H1. case (y=x) => />. rewrite get_out => />. rewrite size_set => />. rewrite get_out => />. 
    move => H2. rewrite get_set_neqE => />. qed.

  lemma size_filter (p:int->'a->bool) (xs:'a array) :
    size (filter p xs) = size xs.
    rewrite size_init => />*. smt(size_ge0). qed.

  axiom get_init sz (f:int -> 'a) (i:int) :
    get (init sz f) i = if 0 <= i < sz then f i else witness.

  (*lemma get_empty sz (i:int) :
    get ((empty<:'a> sz)) i = witness.
    rewrite /empty /create => />*. rewrite get_init => />*. qed.*)

  lemma get_map (f:'a->'b) (xs:'a array) (i:int) :
    0 <= i < size xs => get (map f xs) i = f (get xs i).
    progress. rewrite /map get_init => />*. rewrite andabP andaP => />*. qed.

  lemma get_imap (f:int -> 'a->'b) (xs:'a array) (i:int) :
    0 <= i < size xs => get (imap f xs) i = f i (get xs i).
    rewrite /imap get_init => />*. qed.

  lemma size_zip (xs:'b array) (ys: 'c array) :
    size (zip xs ys) = min (size xs) (size ys).
    rewrite /merge => />*. rewrite size_init => />*. smt(size_ge0). qed.

  lemma get_zip (xs:'b array) (ys: 'c array) (i:int) : 
    get (zip xs ys) i = if 0 <= i < min (size xs) (size ys) then (get xs i,get ys i) else witness.
    rewrite /zip get_init => />*. qed.

  lemma get_zip3 (xs:'b array) (ys: 'c array) (zs:'d array) (i:int) : 
    (get (zip3 xs ys zs) i) = if 0 <= i < min (size xs) (min (size ys) (size zs)) then (get xs i,(get ys i,get zs i)) else witness.
    rewrite /zip3 !get_init => />*. rewrite !get_zip => />*. rewrite size_zip => />*. case (0 <= i && i < min (size xs) (min (size ys) (size zs))) => H1 />*. have : (0 <= i && i < min (size ys) (size zs)). smt(size_ge0). move => H2. rewrite H2 => />*. qed.

  lemma get_merge (f:'a->'b->'c) (xs:'a array) (ys:'b array) (i:int) :
    get (merge f xs ys) i = if 0 <= i < min (size xs) (size ys) then f (get xs i) (get ys i) else witness.
    case (0 <= i < min (size xs) (size ys)) => />. rewrite /merge get_init => />.  rewrite andabP => H.
    rewrite get_init => />. smt(). qed. 

  lemma allP (t: 'a array) (f:int->'a->bool) :
    all f t <=> (forall i, 0 <= i < size t => f i (get t i)).
    rewrite /all allP => />*. progress.
    rewrite H => />*. rewrite mem_iota => />*. 
    rewrite H => />*. move :H0. rewrite mem_iota => />*. qed.

  lemma filter_comp (f:int->'a->bool) (g:int->'a ->bool) (xs:'a array) :
    filter f (filter g xs) = filter (fun i x => f i x /\ g i x) xs.
    rewrite tP => />*. rewrite /filter !size_init => />*. split. smt(size_ge0). move => i H2 H3. rewrite !get_init andabP andaP. rewrite H2. smt().
    simplify. rewrite !get_init => />*. have : 0 <= i && i < size xs. smt(size_ge0). move => H4. rewrite !H4. simplify. smt(). qed.

    lemma zip3_id xs1 xs2 xs3 (xs:('a*('b*'c)) array) :
    xs1 = map fst3 xs /\ xs2 = map snd3 xs /\ xs3 = map thr3 xs => zip3 xs1 xs2 xs3 = xs.
    progress. rewrite tP => />*. rewrite /zip3 /zip !size_init => />*. split. smt(size_ge0).
    move => i H1 H2. rewrite get_zip3 andabP andaP. rewrite H1. rewrite !size_init. smt(size_ge0). simplify. rewrite !get_map /fst3 /snd3 /thr3 => /> . smt(). smt(). smt(). smt(). qed.

  lemma id_zip3 (xs:('a*('b*'c)) array) :
    xs = zip3 (map fst3 xs) (map snd3 xs) (map thr3 xs).
    rewrite tP => />. 
    split. 
    rewrite /zip3. rewrite !size_zip. rewrite !size_init /min /max. smt(size_ge0).
    move => i H H0.
    rewrite get_zip3 /= !size_init /min /max /= !get_map => />. smt(size_ge0).
  qed.

  lemma map_fst_zip3 (f:'b*('c*'d)->'b) (xs:('b) array) (ys:('c) array) (zs:('d) array) :
  size xs <= min (size ys) (size zs) => f = fst3 => map f (zip3 xs ys zs) = xs.
  move => sizes Hf. rewrite tP => />. 
  split. rewrite size_init !size_zip /=. smt(size_ge0). 
  move => i. rewrite size_init /= !size_zip => H H0. rewrite get_map /=. rewrite !size_zip. smt(size_ge0). rewrite Hf /= !get_zip /= size_zip.
  move : H0. 
  have -> : ((min (size xs) (min (size ys) (size zs))) = size xs); first by rewrite /min /= ; smt(size_ge0). smt(). qed.

  lemma map_snd_zip3 (f:'b*('c*'d)->'c) (xs:('b) array) (ys:('c) array) (zs:('d) array) :
  size ys <= min (size xs) (size zs) =>  f = snd3 => map f (zip3 xs ys zs) = ys.
  move => sizes Hf. rewrite tP => />. 
  split. rewrite size_init !size_zip /=. smt(size_ge0). 
  move => i. rewrite size_init /= !size_zip => H H0. rewrite get_map /=. rewrite !size_zip. smt(size_ge0). rewrite Hf /= !get_zip /= size_zip.
  move : H0. 
  have -> : ((min (size xs) (min (size ys) (size zs))) = size ys); first by rewrite /min /= ; smt(size_ge0). smt(). qed.

  lemma map_thr_zip3 (f:'b*('c*'d)->'d) (xs:('b) array) (ys:('c) array) (zs:('d) array) :
  size zs <= min (size xs) (size ys) => f = thr3 => map f (zip3 xs ys zs) = zs.
  move => sizes Hf. rewrite tP => />. 
  split. rewrite size_init !size_zip /=. smt(size_ge0). 
  move => i. rewrite size_init /= !size_zip => H H0. rewrite get_map /=. rewrite !size_zip. smt(size_ge0). rewrite Hf /= !get_zip /= size_zip.
  move : H0. 
  have -> : ((min (size xs) (min (size ys) (size zs))) = size zs); first by rewrite /min /= ; smt(size_ge0). smt(). qed.

  lemma map_comp (f:'b->'c) (g:'a ->'b) (xs:'a array) :
    map f (map g xs) = map (f \o g) xs.
    rewrite tP => />.
    split. rewrite !size_init. smt(size_ge0). 
    move=> i; rewrite size_init => *. rewrite !get_map => />*. 
    smt(size_init). smt(size_init). smt(size_init). qed.

  lemma imap_comp (f:int -> 'b->'c) (g:int -> 'a ->'b) (xs:'a array) :
    imap f (imap g xs) = imap (fun i => f i \o g i) xs.
    rewrite tP => />.
    split. rewrite !size_init. smt(size_ge0).
    move=> i; rewrite size_init => *. rewrite !get_imap => />*. 
    smt(size_init). smt(size_init). smt(size_init). qed.

  lemma imap_map_comp (f:int -> 'b->'c) (g:'a ->'b) (xs:'a array) :
    imap f (map g xs) = imap (fun i => f i \o g) xs.
    rewrite tP => />.
    split. rewrite !size_init. smt(size_ge0).
    move=> i; rewrite size_init => *. rewrite !get_imap => />*. 
    smt(size_init). smt(size_init). smt(size_init). qed.

  lemma map_imap_comp (f:'b->'c) (g:int -> 'a ->'b) (xs:'a array) :
    map f (imap g xs) = imap (fun i => f \o g i) xs.
    rewrite tP => />.
    split. rewrite !size_init. smt(size_ge0). 
    move=> i; rewrite size_init => *. rewrite !get_imap => />*. 
    smt(size_init). smt(size_init). smt(size_init). qed.

  lemma map_id (f:'a->'a) (xs:'a array) :
    f = idfun => map f xs = xs.
    rewrite /map tP => />*. 
    split. rewrite /idfun /= size_init /=. by smt(size_ge0).
    move=> i.  rewrite size_init => *. 
    rewrite !get_map => />*. 
    smt(size_init). qed.

  lemma concat0 :
    concat [<:'a array>] = create 0 [].
    rewrite /concat => />*. qed.

  lemma concat1 (x:'b array) :
    concat [x] = init (size x) (fun i => [get x i]).
    rewrite /concat => />*. rewrite tP => />*. rewrite !size_init => />. split. rewrite /lsize !ge0_max => />. smt(size_ge0). smt(size_ge0). smt(size_ge0). smt(size_ge0). move => i H1 H2.
    rewrite get_merge !get_init !andabP !andaP => />H3. move :H2. rewrite /lsize !size_init => />. smt(size_ge0). move :H2. rewrite /lsize => />. smt(size_ge0). move :H2. rewrite /lsize => />. smt(size_ge0). qed.

  (*lemma concat_rcons (xxs : ('b t) list) xs :
    concat (rcons xxs xs) = merge rcons (concat xxs) xs.
    rewrite /concat => />. rewrite foldl_rcons => />*. congr. congr. congr. qed.

  lemma concat_cat (xxs1 xxs2 : ('b t) list) :
    concat (xxs1 ++ xxs2) = merge cat (concat xxs1) (concat xxs2).
    elim xxs2 xxs1 => /> x. rewrite cats0 => />*. rewrite concat0 => />*.
    rewrite tP => /> i. rewrite /create !get_init !andabP => /> H H0. rewrite !get_init !andabP !andaP => />*. rewrite cats0 => />*. 
    move => l H x0.
    rewrite -cat_rcons H => />*. rewrite tP => /> i HL HH.
     rewrite !get_merge !andabP; rewrite HH HL => />*. 
    rewrite concat_rcons => />*. rewrite get_merge andabP HH HL => />. 
    rewrite cat_rcons => />*. congr.  rewrite (_:x::l=[x]++l). rewrite cat1s => />*. rewrite H => />*. rewrite get_merge andabP andaP => />*. rewrite concat1 => />*. rewrite get_init andabP andaP => />*. qed.

  lemma concat_cons (l : ('b t) list) x :
    (concat (cons x l)) = merge cons x (concat l).
    rewrite (_:x::l=[x]++l). rewrite cat1s => />*. rewrite concat_cat => />*.
    rewrite tP => />*. rewrite !get_merge !andabP !andaP => />*. 
    rewrite concat1 => />*. rewrite get_init andabP andaP => />*. qed.

  lemma size_get_concat (xxs : ('b t) list) i :
    0 <= i < size => size (get (concat xxs) i) = size xxs.
    progress. elim xxs => />*. rewrite concat0 => />*. rewrite /create get_init andabP andaP => />*. 
    rewrite concat_cons => />*. rewrite get_merge andabP andaP => />.  smt(). qed.

  lemma nth_get_concat (xxs : ('b t) list) i j :
    0 <= i < size => 0 <= j < size xxs => 
      (nth (get witness i) ((get (concat xxs) i)) j) = get (nth witness xxs j) i.
    elim xxs i j => />.
    move => si sj H H0 H1 H2. 
    rewrite concat0 => />*. rewrite /create get_init andabP. smt().
    move => x l H i j H2 H3.
    rewrite concat_cons get_merge andabP andaP => />*. case (j=0) => />*. rewrite H => />*. smt(size_ge0). qed.

  lemma nth_get_concat_gt0 d1 d2 (xxs : ('b t) list) i j :
    0 <= i < size => 0 <= j < size xxs => 0 < size xxs => 
      (nth d1 ((get (concat xxs) i)) j) = get (nth d2 xxs j) i.
    elim xxs i j => />.
    move => si sj H H0 H1 H2. 
    rewrite concat_cons get_merge andabP. smt().  qed.*)

  lemma size_to_list (xs:'a array) :
    size (to_list xs) = size xs. rewrite /to_list => />*. rewrite size_mkseq => />*.
    smt(size_ge0). qed.

  lemma size_of_list (xs:'a list) :
    size (of_list xs) = size xs.
    rewrite /of_list => />. rewrite size_init => />. rewrite ge0_max => />. rewrite size_ge0 => />. qed.

  lemma to_of_list (xs:'a list) :
    to_list (of_list xs) = xs.
    rewrite /to_list /of_list => />. rewrite !size_init ge0_max => />. rewrite size_ge0 => />.
    apply (eq_from_nth witness) => />. rewrite size_mkseq => />. rewrite ge0_max => />. rewrite size_ge0 => />.
    move => i. rewrite size_mkseq ge0_max => />. rewrite size_ge0 => />. move => Hi1 Hi2. rewrite nth_mkseq => />. rewrite get_init andabP andaP => />. qed.

  lemma of_to_list (xs:'a array) :
    of_list (to_list xs) = xs.
    rewrite /to_list /of_list => />. rewrite size_mkseq ge0_max => />. rewrite size_ge0 => />. rewrite tP => />. rewrite size_init => />. rewrite ge0_max => />. rewrite size_ge0 => />.
    move => i Hi1 Hi2. rewrite get_init andabP andaP => />. rewrite nth_mkseq => />. qed.

  lemma size_to_assoc (xs:'a array) :
    size (to_assoc xs) = size xs. rewrite /to_assoc => />*. rewrite size_zip size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. qed.

  (*lemma eq_of_list_cons_l x (xs:'a list) (ys:'a array) :
  0 < size xs => (of_list (x::xs) = ys) = (x = get ys 0 /\ (forall i, 0 <= i < size xs -1 => nth witness xs i = get ys (i+1)) ).
  rewrite tP => /> H. rewrite eq_logical => />.
 rewrite /of_list => />. 
split.
move => /> H0 H1. move => /> i H1.
rewrite -H0; first by smt().

rewrite get_init => />*. rewrite H => /> i H1 H2. 
rewrite -(H0) => />. smt().
rewrite get_init => />. smt().

move => /> H0 i H1 H2. 
rewrite get_init => />. smt().
qed.*)

  lemma onth_to_list (xs:'a array) i :
    onth (to_list xs) i = if 0 <= i < size xs then Some (get xs i) else None.
    case (0 <= i < size xs) => />. 
    move => H1 H2. rewrite /to_list (onth_nth witness) => />. rewrite size_mkseq ge0_max => />. rewrite size_ge0 => />. rewrite nth_mkseq => />.
    move => H. rewrite onth_none => />. rewrite size_to_list => />. smt().
    qed.

  (*lemma nth_to_list_some (xs:'a t) i :
    0 <= i < size =>
    nth witness (to_list xs) i = get xs i.
    move => ?. rewrite /to_list nth_mkseq => />*. qed.

  lemma assoc_to_assoc (xs:'a t) (i:int) :
    assoc (to_assoc xs) i = if 0 <= i < size then Some (get xs i) else None.
    rewrite /to_assoc. rewrite assoc_zip => />*. rewrite size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. case (0 <= i && i < size) => />*.
    rewrite index_iseq => />*. rewrite in_iseq => />*. rewrite (onth_nth witness) => />*. rewrite size_to_list => />*. rewrite nth_to_list_some => />*. rewrite index_out => />*. rewrite in_iseq => />*. smt(). rewrite size_iseq => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. rewrite onth_none => />*. rewrite size_to_list => />*. qed. 
    
  lemma nth_to_assoc_some (xs:'a t) i :
    0 <= i < size => 
    nth witness (to_assoc xs) i = (i,get xs i).
    rewrite /to_assoc => />*. rewrite nth_onth. rewrite (onth_nth (witness,witness)) => />*. rewrite size_zip size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. rewrite nth_zip => />*. rewrite size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. rewrite nth_iseq nth_to_list_some => />*. rewrite andaP => />*. qed.

  lemma get_to_assoc (xs:'a t) (i:int) :
    0 <= i < size =>
    get xs i = oget (assoc (to_assoc xs) i).
    rewrite assoc_to_assoc => />*. qed.

  lemma to_assoc_eq (xs ys : 'a t) :
    (to_assoc xs = to_assoc ys) = (xs = ys).
    rewrite tP => />*. rewrite eq_logical => />*. progress.
    rewrite !get_to_assoc => />*. rewrite H => />*. 
    apply (eq_from_nth witness) => />*. rewrite !size_to_assoc => />*. rewrite /to_assoc.
    rewrite !nth_onth => />*. rewrite !(onth_nth (witness,witness)) => />*. rewrite size_zip => />*. rewrite size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. smt(@List).  
    rewrite !nth_zip => />*. rewrite size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. rewrite size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. rewrite !nth_to_list_some => />*. smt(@List). 
smt(@List).
smt(@List).
 qed.   *)

  lemma lsame_to_list f (xs:'a array) (ys:'b array) :
    lsame f (to_list xs) (to_list ys) = (size xs = size ys /\ all (fun i => f (get xs i) (get ys i)) (iseq (size xs)) ).
    rewrite eq_logical => |>. split.
   move => H.  rewrite -!size_to_list //. have : size (to_list xs) = size (to_list ys). rewrite (lsame_size f (to_list xs) (to_list ys)) //.
   rewrite allP => />. move => H2 x H1. move :H. rewrite lsameP => />H. 
   have : osame f (onth (to_list xs) x) (onth (to_list ys) x). rewrite H => |>. move :H1. rewrite size_to_list in_iseq => />. rewrite onth_to_list => />. rewrite !onth_to_list => />. rewrite size_to_list in_iseq in H1. have : 0 <= x < size xs. move :H1. progress. move => H3. rewrite !H3 => />. rewrite !size_to_list in H2. rewrite -H2 => />. rewrite H3 => />. 
   move => H. rewrite allP lsameP => />H1 n Hn. rewrite !onth_to_list => />. case (0 <= n < size xs) => />. move => H2 H3. rewrite -H H3 => />. rewrite H1 => />. rewrite in_iseq => />. move => H2. rewrite -H H2 => />. qed.

  (*lemma set_eq (xs ys: 'a array) i (x y:'a) :
    0 <= i < size xs =>
    (set xs i x = set ys i y) <=> (x = y /\ forall k, 0 <= k < size xs => k <> i => get xs k = get ys k ).
    rewrite !tP => />Hi1 Hi2. rewrite !size_set => />. split. 
    move => H H0. have : get (set xs i x) i = get (set ys i y) i. rewrite H0 => />. rewrite !get_set_eqE => />. rewrite -H Hi2 => />. move => k Hk1 Hk2 Hk3. have : get (set xs i y) k = get (set ys i y) k. rewrite H0 => />. rewrite !get_set_neqE => />. 
    move => H.*)

end Array.
