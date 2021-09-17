require import AllCore Int List.
require import Aux AuxList.

(* A fixed size array *)
theory ArrayN.

  op size: int.
  axiom size_ge0 : 0 <= size.

  type 'a arrayN.
  op get (xs:'a arrayN) (i:int) : 'a.
  op set (xs:'a arrayN) (i:int) (x:'a) : 'a arrayN.
  op init (f:int->'a) : 'a arrayN.

  op of_list (l:'a list) : 'a arrayN = init (fun i => nth witness l i).
  op to_list (t:'a arrayN) = mkseq (fun i => get t i) size.
  op to_assoc (t:'a arrayN) = zip (iseq size) (to_list t).

  op create (x:'a) = init (fun _ => x).
  op singl i (x:'a) = init (fun j => if j=i then x else witness).
  op imap (f:int -> 'a -> 'b) (xs:'a arrayN) : ('b arrayN) =
    init (fun j => f j (get xs j)).
  abbrev map (f:'a->'b) (xs:'a arrayN) : ('b arrayN) = imap (fun _ => f) xs.
  op merge (f:'a -> 'b -> 'c) (xs:'a arrayN) (ys:'b arrayN) : ('c arrayN) =
    init (fun i => f (get xs i) (get ys i)).
  abbrev zip (xs:'a arrayN) (ys:'b arrayN) = merge (fun x y => (x,y)) xs ys.
  op filter (p:int->'a->bool) (xs:'a arrayN) : ('a arrayN) =
    init (fun j => if p j (get xs j) then (get xs j) else witness).
  (*op empty : ('a arrayN) = create witness<:'a>.*)
  op all (f : int -> 'a -> bool) (t : 'a arrayN) =
    all (fun i => f i (get t i)) (iseq size).
  op allsame (xs :'a arrayN) =
    all (fun i => all (fun j => get xs i = get xs j) (iseq size)) (iseq size).

  abbrev zip3 (xs:'a arrayN) (ys:'b arrayN) (zs:'c arrayN) : ('a*('b*'c)) arrayN =
    zip xs (zip ys zs).

  op concat (xxs : ('b arrayN) list) : ('b list) arrayN =
    foldl (fun xs b => merge rcons xs b) (create []) xxs.

  axiom get_out (t:'a arrayN) i : !(0 <= i < size) => get t i = witness.

  axiom tP (t1 t2: 'a arrayN) :
    t1 = t2 <=> forall i, 0 <= i < size => get t1 i = get t2 i.

  axiom get_set_eqE (m : 'b arrayN) (x : int) b :
    0 <= x < size => get (set m x b) x = b.

  axiom get_set_neqE (m : 'a arrayN) (x y : int) (a:'a) :
    (y <> x) => get (set m x a) y = get m y.

  axiom get_init (f:int -> 'a) (i:int) :
    get (init f) i = if 0 <= i < size then f i else witness.

  (*lemma get_empty (i:int) :
    get empty<:'a> i = witness.
    rewrite /empty /create => />*. rewrite get_init => />*. qed.*)

  lemma get_map (f:'a->'b) (xs:'a arrayN) (i:int) :
    0 <= i < size => get (map f xs) i = f (get xs i).
    progress. rewrite /map get_init => />*. rewrite andabP andaP => />*. qed.

  lemma get_imap (f:int -> 'a->'b) (xs:'a arrayN) (i:int) :
    0 <= i < size => get (imap f xs) i = f i (get xs i).
    rewrite /imap get_init => />*. qed.

  lemma get_zip (xs:'b arrayN) (ys: 'c arrayN) (i:int) : 
    get (zip xs ys) i = if 0 <= i < size then (get xs i,get ys i) else witness.
    rewrite /zip get_init => />*. qed.

  lemma get_zip3 (xs:'b arrayN) (ys: 'c arrayN) (zs:'d arrayN) (i:int) : 
    (get (zip3 xs ys zs) i) = if 0 <= i < size then (get xs i,(get ys i,get zs i)) else witness.
    rewrite /zip3 !get_init => />*. rewrite !get_zip => />*. case (0 <= i && i < size) => />*. qed.

  lemma get_merge (f:'a->'b->'c) (xs:'a arrayN) (ys:'b arrayN) (i:int) :
    get (merge f xs ys) i = if 0 <= i < size then f (get xs i) (get ys i) else witness.
    case (0 <= i < size) => />. rewrite /merge get_init => />.  rewrite andabP => H.
    rewrite get_init => />. smt(). qed. 

  lemma allP (t: 'a arrayN) (f:int->'a->bool) :
    all f t <=> (forall i, 0 <= i < size => f i (get t i)).
    rewrite /all allP => />*. progress.
    rewrite H => />*. rewrite mem_iota => />*. 
    rewrite H => />*. move :H0. rewrite mem_iota => />*. qed.

  lemma filter_comp (f:int->'a->bool) (g:int->'a ->bool) (xs:'a arrayN) :
    filter f (filter g xs) = filter (fun i x => f i x /\ g i x) xs.
    rewrite tP => />*. rewrite !get_init andabP andaP => />*. rewrite !get_init => />*. smt(). qed.

    lemma zip3_id xs1 xs2 xs3 (xs:('a*('b*'c)) arrayN) :
    xs1 = map fst3 xs /\ xs2 = map snd3 xs /\ xs3 = map thr3 xs => zip3 xs1 xs2 xs3 = xs.
    progress. rewrite tP => />i. rewrite get_zip3 andabP => /> H H1. rewrite !get_map /fst3 /snd3 /thr3 => /> . smt().
 qed.

  lemma id_zip3 (xs:('a*('b*'c)) arrayN) :
    xs = zip3 (map fst3 xs) (map snd3 xs) (map thr3 xs).
    rewrite tP => />*. rewrite get_zip3 andabP andaP => />*. rewrite !get_map /fst3 /snd3 /thr3 => />*. rewrite -prod3_id => />*. qed.

  lemma map_fst_zip3 (f:'b*('c*'d)->'b) (xs:('b) arrayN) (ys:('c) arrayN) (zs:('d) arrayN) :
  f = fst3 => map f (zip3 xs ys zs) = xs.
  move => ?. rewrite tP => />i H H1. rewrite get_map => />. rewrite get_zip3 andabP => />. rewrite /fst3 => />*. smt(). qed.

  lemma map_snd_zip3 (f:'b*('c*'d)->'c) (xs:('b) arrayN) (ys:('c) arrayN) (zs:('d) arrayN) :
  f = snd3 => map f (zip3 xs ys zs) = ys.
  move => ?. rewrite tP => /> i H H1. rewrite get_map => />*. rewrite get_zip3 andabP andaP => />*.  rewrite /snd3 => />*. smt().  qed.

  lemma map_thr_zip3 (f:'b*('c*'d)->'d) (xs:('b) arrayN) (ys:('c) arrayN) (zs:('d) arrayN) :
  f = thr3 => map f (zip3 xs ys zs) = zs.
  move => ?. rewrite tP => /> i H H1. rewrite get_map => />*. rewrite get_zip3 andabP andaP => />*. rewrite /thr3 => />*. smt(). qed.

  lemma map_comp (f:'b->'c) (g:'a ->'b) (xs:'a arrayN) :
    map f (map g xs) = map (f \o g) xs.
    rewrite tP => />*. rewrite !get_map => />*. qed.

  lemma imap_comp (f:int -> 'b->'c) (g:int -> 'a ->'b) (xs:'a arrayN) :
    imap f (imap g xs) = imap (fun i => f i \o g i) xs.
    rewrite tP => />*. rewrite !get_imap => />*. qed. 

  lemma imap_map_comp (f:int -> 'b->'c) (g:'a ->'b) (xs:'a arrayN) :
    imap f (map g xs) = imap (fun i => f i \o g) xs.
    rewrite tP => />*. rewrite !get_imap => />*. qed. 

  lemma map_imap_comp (f:'b->'c) (g:int -> 'a ->'b) (xs:'a arrayN) :
    map f (imap g xs) = imap (fun i => f \o g i) xs.
    rewrite tP => />*. rewrite !get_imap => />*. qed.    

  lemma map_id (f:'a->'a) (xs:'a arrayN) :
    f = idfun => map f xs = xs.
    rewrite /map tP => />*. rewrite get_map /idfun => />*. qed.

  lemma concat0 :
    concat [<:'a arrayN>] = create [].
    rewrite /concat => />*. qed.

  lemma concat1 (x:'b arrayN) :
    concat [x] = init (fun i => [get x i]).
    rewrite /concat => />*. rewrite tP => />*. rewrite get_merge !get_init !andabP !andaP => />*. qed.

  lemma concat_rcons (xxs : ('b arrayN) list) xs :
    concat (rcons xxs xs) = merge rcons (concat xxs) xs.
    rewrite /concat => />*. rewrite foldl_rcons => />*. qed.

  lemma concat_cat (xxs1 xxs2 : ('b arrayN) list) :
    concat (xxs1 ++ xxs2) = merge cat (concat xxs1) (concat xxs2).
    elim xxs2 xxs1 => /> x. rewrite cats0 => />*. rewrite concat0 => />*.
    rewrite tP => /> i. rewrite /create !get_init !andabP => /> H H0. rewrite !get_init !andabP !andaP => />*. rewrite cats0 => />*. 
    move => l H x0.
    rewrite -cat_rcons H => />*. rewrite tP => /> i HL HH.
     rewrite !get_merge !andabP; rewrite HH HL => />*. 
    rewrite concat_rcons => />*. rewrite get_merge andabP HH HL => />. 
    rewrite cat_rcons => />*. congr.  rewrite (_:x::l=[x]++l). rewrite cat1s => />*. rewrite H => />*. rewrite get_merge andabP andaP => />*. rewrite concat1 => />*. rewrite get_init andabP andaP => />*. qed.

  lemma concat_cons (l : ('b arrayN) list) x :
    (concat (cons x l)) = merge cons x (concat l).
    rewrite (_:x::l=[x]++l). rewrite cat1s => />*. rewrite concat_cat => />*.
    rewrite tP => />*. rewrite !get_merge !andabP !andaP => />*. 
    rewrite concat1 => />*. rewrite get_init andabP andaP => />*. qed.

  lemma size_get_concat (xxs : ('b arrayN) list) i :
    0 <= i < size => size (get (concat xxs) i) = size xxs.
    progress. elim xxs => />*. rewrite concat0 => />*. rewrite /create get_init andabP andaP => />*. 
    rewrite concat_cons => />*. rewrite get_merge andabP andaP => />.  smt(). qed.

  lemma nth_get_concat (xxs : ('b arrayN) list) i j :
    0 <= i < size => 0 <= j < size xxs => 
      (nth (get witness i) ((get (concat xxs) i)) j) = get (nth witness xxs j) i.
    elim xxs i j => />.
    move => si sj H H0 H1 H2. 
    rewrite concat0 => />*. rewrite /create get_init andabP. smt().
    move => x l H i j H2 H3.
    rewrite concat_cons get_merge andabP andaP => />*. case (j=0) => />*. rewrite H => />*. smt(size_ge0). qed.

  lemma nth_get_concat_gt0 d1 d2 (xxs : ('b arrayN) list) i j :
    0 <= i < size => 0 <= j < size xxs => 0 < size xxs => 
      (nth d1 ((get (concat xxs) i)) j) = get (nth d2 xxs j) i.
    elim xxs i j => />.
    move => si sj H n1 n2 H2 H3 H4 H5 H6. 
    rewrite concat_cons get_merge !andabP => />.
    rewrite andaP => />. case (n2=0) => />H7. rewrite H => />. smt().
    smt().  qed.

  lemma size_to_list (xs:'a arrayN) :
    size (to_list xs) = size. rewrite /to_list => />*. rewrite size_mkseq => />*.
    smt(size_ge0). qed.

  lemma size_to_assoc (xs:'a arrayN) :
    size (to_assoc xs) = size. rewrite /to_assoc => />*. rewrite size_zip size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. qed.

  lemma eq_of_list_cons_l x (xs:'a list) (ys:'a arrayN) :
  0 < size => (of_list (x::xs) = ys) = (x = get ys 0 /\ (forall i, 0 <= i < size-1 => nth witness xs i = get ys (i+1)) ).
  rewrite tP => /> H. rewrite eq_logical => />.
 rewrite /of_list => />. 
split.
move => /> H0.  
rewrite -H0; first by smt().

rewrite get_init => />*. rewrite H => /> i H1 H2. 
rewrite -(H0) => />. smt().
rewrite get_init => />. smt().

move => /> H0 i H1 H2. 
rewrite get_init => />. smt().
qed.

  lemma nth_to_list_some (xs:'a arrayN) i :
    0 <= i < size =>
    nth witness (to_list xs) i = get xs i.
    move => ?. rewrite /to_list nth_mkseq => />*. qed.

  lemma assoc_to_assoc (xs:'a arrayN) (i:int) :
    assoc (to_assoc xs) i = if 0 <= i < size then Some (get xs i) else None.
    rewrite /to_assoc. rewrite assoc_zip => />*. rewrite size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. case (0 <= i && i < size) => />*.
    rewrite index_iseq => />*. rewrite in_iseq => />*. rewrite (onth_nth witness) => />*. rewrite size_to_list => />*. rewrite nth_to_list_some => />*. rewrite index_out => />*. rewrite in_iseq => />*. smt(). rewrite size_iseq => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. rewrite onth_none => />*. rewrite size_to_list => />*. qed. 
    
  lemma nth_to_assoc_some (xs:'a arrayN) i :
    0 <= i < size => 
    nth witness (to_assoc xs) i = (i,get xs i).
    rewrite /to_assoc => />*. rewrite nth_onth. rewrite (onth_nth (witness,witness)) => />*. rewrite size_zip size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. rewrite nth_zip => />*. rewrite size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. rewrite nth_iseq nth_to_list_some => />*. rewrite andaP => />*. qed.

  lemma get_to_assoc (xs:'a arrayN) (i:int) :
    0 <= i < size =>
    get xs i = oget (assoc (to_assoc xs) i).
    rewrite assoc_to_assoc => />*. qed.

  lemma to_assoc_eq (xs ys : 'a arrayN) :
    (to_assoc xs = to_assoc ys) = (xs = ys).
    rewrite tP => />. rewrite eq_logical => />. progress.
    rewrite !get_to_assoc => />. rewrite H => />. 
    apply (eq_from_nth witness) => />. rewrite !size_to_assoc => />. rewrite /to_assoc.
    rewrite size_zip !size_iseq !size_to_list ge0_max => />. rewrite size_ge0 => />. 
    move => i H1. rewrite min_eq => />H2. 
    rewrite !nth_onth => />. rewrite !(onth_nth (witness,witness)) => />. move => H3. rewrite size_zip => />. rewrite size_iseq size_to_list => />. rewrite ge0_max => />. rewrite size_ge0 => />. rewrite size_zip size_iseq size_to_list => />. rewrite ge0_max => />. rewrite size_ge0 => />.
    rewrite !nth_zip => />*. rewrite size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. rewrite size_iseq size_to_list => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. rewrite !nth_to_list_some => />*. rewrite H => />. 
 qed.   

  lemma of_list_eq (xs ys : 'a list) :
    size xs = size => size ys = size =>
    (xs = ys) = (of_list xs = of_list ys).
    move => Sz1 Sz2. rewrite list_eq tP => />. rewrite eq_logical => />. split.
    move => H H0 i Hi1 Hi2. rewrite !get_init !andabP !Hi1 !Hi2 => />. rewrite H0 => />. rewrite Sz1 => />.
    move => H. rewrite Sz1 Sz2 => />n Hn1 Hn2. have : get (of_list xs) n = get (of_list ys) n. rewrite H => />. rewrite !get_init !andabP !Hn1 !Hn2 => />. qed.

end ArrayN.
