require import AllCore Int List FSet SmtMap.
require import Aux AuxList NextMsgArray NextMsgFixedArray.
require import NextMsgISet NextMsgIMap.
require import AuxFSet.
import ISet IMap.

theory Trace.

  type public_input. (* same for all parties *)

  (* Parties and Rounds types *)

  clone import ArrayN as P.
  op parties : int = P.size.
  type party = int.
  op partyset = ISet.iset parties.
 
  import Array.

  type round = int.
  op rounds : public_input -> int. (* number of rounds *)
  axiom rounds_ge0 p : 0 <= rounds p.
  op roundset p = ISet.iset (rounds p).

  type 'a pmap = 'a P.arrayN.
  type 'a rmap = 'a array.
  type 'a prmap = ('a rmap) pmap.
  type 'a ppmap = ('a pmap) pmap.
  type 'a pprmap = ('a rmap) ppmap.
  
  (* Traces types *)

  type local_input. (* one share per party *)
  type local_output. (* same for all parties *)
  type local_rand. (* randomness of one party *)
  type msg. (* universal message type, per party, per round *)
  type pmsgs = msg pmap.
  type rmsgs = msg rmap.
  type prmsgs = rmsgs pmap.
  type ppmsgs = pmsgs pmap.
  type pprmsgs = prmsgs pmap.
  (* messages received at the end of each round *)
  type in_msgs = prmsgs.
  (* messages sent at the end of each round *)
  type out_msgs = prmsgs.
  type view = local_input * (in_msgs * local_rand).
  type trace = view pmap.

  op eq_msg : msg -> msg -> bool.
  
  axiom eq_msgP m1 m2 :
    eq_msg m1 m2 = (m1 = m2).

  op eq_pmsgs (m1 m2 : pmsgs) : bool =
    all_iseq (fun i => eq_msg (P.get m1 i) (P.get m2 i)) P.size.

  lemma eq_pmsgsP m1 m2 :
    eq_pmsgs m1 m2 = (m1 = m2).
    rewrite /eq_pmsgs P.tP => |>*. rewrite all_iseqE allP => |>*. rewrite eq_logical => |>*. progress. 
    rewrite -eq_msgP H => |>*. rewrite in_iseq => |>*. 
    rewrite eq_msgP H => |>*. move :H0. rewrite in_iseq => |>*. qed.

  op eq_rmsgs (m1 m2 : rmsgs) : bool =
    size m1 = size m2 /\ all_iseq (fun i => eq_msg (Array.get m1 i) (Array.get m2 i)) (size m1).

  lemma eq_rmsgsP m1 m2 :
    eq_rmsgs m1 m2 = (m1 = m2).
    rewrite /eq_rmsgs Array.tP => |>*. rewrite all_iseqE allP => |>*. rewrite eq_logical => |>*. progress. 
    rewrite -eq_msgP H0 => |>*. rewrite in_iseq => |>*. 
    rewrite eq_msgP H0 => |>*. move :H1. rewrite in_iseq => |>*. qed.

  (* Auxiliary operators *)

  op pinit (f:party->'a) : 'a pmap = P.init f.
  op ppinit (f:party -> party -> 'a) : ('a pmap) pmap = pinit (fun i => pinit (f i)).

  op prempty sz (v:'a) : ('a rmap) pmap = pinit (fun _ => Array.create sz v).
  op pprempty sz (v:'a) : ('a rmap) ppmap = ppinit (fun _ _ => Array.create sz v).

  op ppswap (m:'a ppmap) : 'a ppmap =
    ppinit (fun j i => P.get (P.get m i) j).

  op prget (xs:'a prmap) (r:round) : 'a pmap =
    pinit (fun i => get (get xs i) r).

  op pprget (xs:'a pprmap) (r:round) : 'a ppmap =
    ppinit (fun i j => get (get (get xs i) j) r).

  op prset (xs:'a prmap) n (x:'a pmap) : 'a prmap =
    merge (fun x y => Array.set x n y) xs x. 

  op prext sz (xs:'a prmap) : 'a prmap =
    pinit (fun i => Array.init sz (fun j => if 0 <= j /\ j < size (P.get xs i) then Array.get (P.get xs i) j else witness)).

  op prextset (xs:'a prmap) n (x:'a pmap) : 'a prmap =
    prset (prext (n+1) xs) n x.

  op pprset (xs: 'a pprmap) (n:round) (x: 'a ppmap) : 'a pprmap =
    P.merge (P.merge (fun ys y => Array.set ys n y)) xs x.

  op prfilter (p:round -> bool) (ins:'a prmap) : 'a prmap =
    P.map (Array.filter (fun r x => p r)) ins.

  op pprfilter (p:round -> bool) (ins:'a pprmap) : 'a pprmap =
    P.map (P.map (Array.filter (fun r x => p r))) ins.

  op rdom sz (round:round) (xs:'a rmap) =
    size xs = sz /\ (forall i, round <= i => Array.get xs i = witness).
  op prdom sz round (xs:'a prmap) =
    all (fun _ => rdom sz round) xs.
  op pprdom sz round (xs:'a pprmap) =
    all (fun _ => prdom sz round) xs.

  op rlist sz (xs:'a list) : 'a rmap =
    foldl (fun rs i => Array.set rs i (nth witness xs i)) (Array.create sz witness) (iseq (size xs)).

  op prlist sz (xs:pmsgs list) : (msg rmap) pmap =
    foldl (fun rs i => prset rs i (nth witness xs i)) (prempty sz witness) (iseq (size xs)).

  op pcons (x:'a pmap) (xs:('a list) pmap) : ('a list) pmap =
    merge cons x xs.

  op phead (xs:('a list) pmap) = P.map (head witness) xs.
  op pbehead (xs:('a list) pmap) = P.map (behead) xs.

  op prcons (xs:('a list) pmap) (x:'a pmap) : ('a list) pmap =
    merge rcons xs x.

  op pcat (xs ys:('a list) pmap) =
    merge cat xs ys.

  op ppcons (x:'a ppmap) (xs:('a list) ppmap) : ('a list) ppmap =
    merge pcons x xs.
    
  op pprcons (xs:('a list) ppmap) (x:'a ppmap) : ('a list) ppmap =
    merge prcons xs x.

  op ppcat (xs ys:('a list) ppmap) =
    merge pcat xs ys.

  lemma rlist0 sz :
    rlist sz [<:'a>] = Array.create sz witness.
    rewrite /rlist iseq_nil => |>*. qed.

  lemma rlist_rcons_aux rounds sz rs r :
    0 <= rounds <= List.size rs => foldl (fun (rs0 : 'a array) (i : int) => set rs0 i (nth witness (rcons rs r) i)) (Array.create sz witness) (iseq rounds) = foldl (fun (rs0 : 'a array) (i : int) => set rs0 i (nth witness rs i)) (Array.create sz witness) (iseq rounds).
    elim/natind:rounds => |> n H H0 H1. rewrite !iseq_nil => //=.  
    move => H2. 
    rewrite !iseq_succ; first by smt() => /=.
    rewrite !foldl_rcons /=.
    congr. smt(@List). rewrite nth_rcons //=. smt(@List). qed.

  lemma rlist_rcons sz (rs:'a list) r :
    rlist sz (rcons rs r) = Array.set (rlist sz rs) (size rs) r.
    rewrite /rlist => |>*. rewrite size_rcons iseq_succ => |>*. rewrite size_ge0 => |>*.
    rewrite foldl_rcons => |>*. congr. rewrite rlist_rcons_aux => |>*. rewrite size_ge0 => |>*. rewrite nth_rcons => |>*. qed.

  lemma size_rlist (sz:int) (xs:'a list) :
    0 <= sz => 
    size (rlist sz xs) = sz.
    move => H. elim/last_ind:xs => |>. rewrite rlist0 => />. rewrite size_init => />. rewrite ge0_max => />. 
    move => x l R. rewrite rlist_rcons => />. rewrite size_set => />. qed.

  lemma rdom_lt (sz n1 n2 :int) (xs:'a array) :
    n1 <= n2 => rdom sz n1 xs => rdom sz n2 xs.
    rewrite /rdom => |>H1 H2 i H3. rewrite H2. smt(). trivial. qed.

  lemma prdom_lt (sz n1 n2 : int) (xs:'a prmap) :
    n1 <= n2 => prdom sz n1 xs => prdom sz n2 xs.
    rewrite /prdom !P.allP => H1 H2 i H3. simplify. rewrite (rdom_lt _ n1). rewrite H1. smt(). qed.

  lemma pprdom_lt (sz n1 n2 : int) (xs:'a pprmap) :
    n1 <= n2 => pprdom sz n1 xs => pprdom sz n2 xs.
    rewrite /pprdom !P.allP => |>H1 H2 i H3 H4. rewrite (prdom_lt _ n1) => |>. rewrite H2 => |>. qed.

  lemma prdom_rdom_get sz n (xs:'a prmap) i :
    ISet.mem i partyset => prdom sz n xs => rdom sz n (get xs i).
    rewrite /prdom. rewrite allP => H H0. have : (fun (_ : int) => rdom sz n) i (get xs i). rewrite H0 => |>. move :H. rewrite /ISet.mem /ISet.iset iset_in_def => |>. progress. qed.

  lemma pprdom_prdom_get sz n (xs:'a pprmap) i :
    ISet.mem i partyset => pprdom sz n xs => prdom sz n (get xs i).
    rewrite /pprdom => |>. rewrite allP => |> H H0. rewrite H0 => |>*. move :H. rewrite /ISet.mem iset_in_def => |>*. qed.

  lemma prdom_rdom sz i n (xs:'a prmap) :
    ISet.mem i partyset => prdom sz n xs => rdom sz n (get xs i).
    rewrite /prdom. rewrite allP => H H0. have : (fun (_ : int) => rdom sz n) i (get xs i). rewrite H0 => |>. move :H. rewrite /ISet.mem iset_in_def => |>*. progress. qed.

  lemma get_pinit (f:party->'a) i : 
    get (pinit f) i = (mem i partyset) ? (f i) : witness.
    rewrite /pinit => |>*. rewrite get_init => |>*. rewrite /ISet.mem /partyset /ISet.iset mem_oflist in_iseq => |>*. smt(). qed.

  lemma get_ppinit (f:party->party->'a) i : 
    get (ppinit f) i = (ISet.mem i partyset) ? (pinit (f i)) : witness.
    rewrite /ppinit => |>*. rewrite get_init => |>*. rewrite /ISet.mem iset_in_def => |>*. smt(). qed.

  lemma get_pmap (f:'a->'b) (xs:'a pmap) i :
    ISet.mem i partyset => get (P.map f xs) i =f (get xs i).
    progress. rewrite get_map => |>*. rewrite /ISet.mem iset_in_def in H => |>*. smt(). qed.

  lemma get_pimap (f:int -> 'a->'b) (xs:'a pmap) i :
    ISet.mem i partyset => get (P.imap f xs) i =f i (get xs i).
    progress. rewrite get_imap => |>*. rewrite /ISet.mem iset_in_def in H => |>*. smt(). qed.

  lemma get_pmerge (f:'a->'b->'c) (xs:'a pmap) (ys:'b pmap) i :
    get (merge f xs ys) i = if ISet.mem i partyset then f (get xs i) (get ys i) else witness.
    progress. rewrite get_merge => |>*. rewrite /ISet.mem iset_in_def andabP => |>*. qed.

  lemma get_pzip (xs:'a P.arrayN) (ys:'b P.arrayN) (i:int) : 
    get (P.zip xs ys) i = (ISet.mem i partyset) ? (get xs i,get ys i) : witness.
    progress. rewrite get_zip => |>*. rewrite /ISet.mem iset_in_def andabP => |>*. qed.

  lemma get_pzip3 (xs:'a P.arrayN) (ys:'b P.arrayN) (zs: 'c P.arrayN) (i:int) : 
    get (P.zip3 xs ys zs) i = (ISet.mem i partyset) ? (get xs i,(get ys i,get zs i)) : witness.
    progress. rewrite get_zip3 => |>*. rewrite /ISet.mem iset_in_def andabP => |>*. qed.

  lemma get_pprget (xs:'a pprmap) (r:round) i :
    get (pprget xs r) i = if ISet.mem i partyset then prget (get xs i) r else witness.
    rewrite /pprget get_ppinit => |>*. qed.

  lemma get_prget (xs:'a prmap) (r:round) i :
    get (prget xs r) i = if ISet.mem i partyset then Array.get (get xs i) r else witness.
    rewrite /prget get_pinit => |>*. qed.

  lemma get_pprempty sz (i:party) (v:'b) :
    get (pprempty sz v) i = if ISet.mem i partyset then (prempty sz v) else witness.
    rewrite /ppempty /pempty /ppinit => |>*. rewrite get_pinit => |>*. qed.

  lemma get_prempty sz (i:party) (v:'b) :
    get (prempty sz v) i = if ISet.mem i partyset then (Array.create sz v) else witness.
    rewrite /prempty => |>*. rewrite get_pinit => |>*. qed.

  lemma get_prset (ins:'a prmap) round outs i :
    get (prset ins round outs) i = if ISet.mem i partyset then set (get ins i) round (get outs i) else witness.
    rewrite /prset => |>. case (ISet.mem i partyset) => |>H. rewrite get_merge => |>. have : 0 <= i && i < P.size. 
    rewrite /ISet.mem iset_in_def in H => |>*. smt(). move => hip. rewrite hip => |>*. 
    rewrite get_merge => |>*. rewrite /ISet.mem iset_in_def in H => |>*. smt(). qed.

  lemma get_pprset (ins:'a pprmap) round outs i :
    get (pprset ins round outs) i = if ISet.mem i partyset then prset (get ins i) round (get outs i) else witness.
    progress. rewrite /pprset => |>*. rewrite get_merge /uncurry => |>*. congr. rewrite /ISet.mem iset_in_def andabP => |>*.
    rewrite /prset => |>*. qed. 

  lemma get_get_ppswap i j (m:'a ppmap) :
    ISet.mem i partyset /\ ISet.mem j partyset => P.get (P.get (ppswap m) j) i = P.get (P.get m i) j.
    rewrite /ppswap /ppinit !get_pinit => |>H. rewrite get_pinit => |>*. 
    rewrite H => |>*. qed.

  lemma rdom_empty sz n :
    n <= 0 => 0 <= sz => rdom sz n (Array.create<:'a> sz witness).
    rewrite /rdom => |>H1 H2. rewrite size_init ge0_max => |>. move => i H3. rewrite get_init => |>*. qed.

  lemma rdom_ge sz (xs:'a rmap) (n1 n2:round) :
    n1 <= n2 => rdom sz n1 xs => rdom sz n2 xs.
    move => H H0.
    rewrite !/rdom => |> *. smt().  qed.

  lemma rdom_set sz (xs:'a rmap) n x :
    0 <= n => rdom sz n xs => rdom sz (n+1) (set xs n x).
    rewrite !/rdom => |> H H0. rewrite size_set => |>. move => i H1. have : !(i=n). smt(). move => neq. rewrite get_set_neqE => |>*. rewrite H0 => |>*. smt(). qed.
    
  lemma prdom_prempty sz n :
    n <= 0 => 0 <= sz => prdom sz n (prempty<:'b> sz witness).
    rewrite /prdom /pempty => |> H H5. rewrite allP => i H0. simplify. rewrite get_pinit. have : ISet.mem i partyset. rewrite /ISet.mem iset_in_def => |>*. move :H0. progress. move => domi. rewrite domi. rewrite rdom_empty => |>*. qed.

  lemma pprdom_pprempty sz n :
    n <= 0 => 0 <= sz => pprdom sz n (pprempty<:'b> sz witness).
    rewrite /pprdom /ppempty /ppinit => |> H H5. rewrite allP => |>i H0 H1. rewrite get_pinit => |>*. rewrite /ISet.mem iset_in_def => |>*. rewrite H0 => |>*. rewrite H1 => |>*. have : prdom sz n (prempty<:'b> sz witness). rewrite prdom_prempty => |>*. rewrite /pempty => |>*. qed.

  lemma prdom_ge sz (xs:'a prmap) (n1 n2:round) :
    n1 <= n2 /\ prdom sz n1 xs => prdom sz n2 xs.
    rewrite !/prdom /all !allP => /= H x H0.
    have : n1 <= n2. smt(). move => H1.
    have : forall (x : int), x \in iseq P.size => rdom sz n1 (get xs x). smt(). move => H2.
    rewrite (rdom_ge sz _ n1 n2). rewrite H1. rewrite H2 => |>. qed.

  lemma prdom_prset sz (xs:'a prmap) (n:round) x :
    0 <= n => 0 <= sz => prdom sz n xs => prdom sz (n+1) (prset xs n x).
    rewrite !/prdom /all !allP => H H0 H1 y H2 /=. move :H1. rewrite !/rdom => /= H3. rewrite get_prset => |>*. rewrite /ISet.mem iset_in_def => |>*. rewrite in_iseq in H2. rewrite H2 => |>*. rewrite size_set => |>.
    have : size (get xs y) = sz /\ forall (i : int), n <= i => get (get xs y) i = witness. rewrite H3 => |>. rewrite in_iseq => |>. progress.
    rewrite get_set_neqE => |>*. smt(). rewrite H1 => |>. smt(). qed.

  lemma prdom_foldl_prset sz (f:round -> 'a pmap) g (n:round) :
    0 <= sz => (g = (fun ys r => prset ys r (f r))) => prdom sz n (foldl g (prempty sz witness) (iseq n)). 
    elim/natind:n => |>i H1 H2. rewrite iseq_nil => |>. rewrite prdom_prempty => |>H3. 
    rewrite iseq_succ => |>H4. rewrite foldl_rcons => |>. rewrite prdom_prset => |>. rewrite H2 => |>. qed.

  lemma pprdom_pprset sz (xs:'a pprmap) n x :
    0 <= n => 0 <= sz => pprdom sz n xs => pprdom sz (n+1) (pprset xs n x).
    rewrite /pprset => |>H1 H2 H3. rewrite !/pprdom /uncurry allP => |>i H4 H5. rewrite !get_merge => |>*. rewrite andabP andaP => |>*.
    rewrite /prdom allP => |>i0 H6 H7. rewrite get_merge => |>*. rewrite andabP andaP => |>*. rewrite rdom_set => |>*. 
    have : prdom sz n (get xs i). rewrite pprdom_prdom_get => |>*. rewrite /ISet.mem iset_in_def andaP => |>H8. 
    move => H9. rewrite prdom_rdom_get => |>. by rewrite /ISet.mem iset_in_def /=  => |>*. qed.

  lemma rdom_filter (n:int) (p:int->bool) (xs:'a rmap) :
    (forall i, n <= i => !(p i)) => rdom (size xs) n (filter (fun r _ => p r) xs).
    rewrite /rdom => |> H. rewrite size_init ge0_max => |>. rewrite size_ge0. move => i H1.
    rewrite get_init. case (0 <= i && i < size xs) => |>*. rewrite H => |>*. qed.

  lemma prdom_prfilter sz (n:int) (p:int->bool) (xs:'a prmap) :
    all (fun _ rs => Array.size rs = sz /\ forall i, n <= i => !(p i)) xs => prdom sz n (prfilter p xs).
    rewrite allP /prdom /prfilter allP => |> H i H1 H2. have : ISet.mem i partyset. rewrite /ISet.mem iset_in_def => |>*. 
    rewrite get_map => |> H3. have : size (get xs i) = sz. smt(). 
    move => H4. rewrite -H4. rewrite rdom_filter => |>i0 H5. rewrite /ISet.mem iset_in_def  in H3 => |>*. smt(). qed.

  lemma pmap_eqP (m1 m2 : 'a pmap) :
    (m1 = m2) = (forall x, ISet.mem x partyset => (get m1 x) = (get m2 x)).
    rewrite tP eq_logical => |>*. progress. rewrite H => |>*. move :H0. rewrite /ISet.mem iset_in_def  => |>*.
    rewrite H => |>*. rewrite /ISet.mem iset_in_def  => |>*. qed.

  lemma ppmap_eqP (m1 m2 : 'a ppmap) :
    (m1 = m2) = (forall x y, ISet.mem x partyset /\ ISet.mem y partyset => P.get (P.get m1 x) y = P.get (P.get m2 x) y).
    rewrite tP eq_logical => |>. do split. 
    move => H x y. rewrite /ISet.mem !iset_in_def => |> *.
    have : get m1 x = get m2 x. rewrite H => |>.  rewrite tP => |>. smt(). 
    move => H x y.
    rewrite tP => |> *. rewrite H => |>*. rewrite /ISet.mem !iset_in_def => |>*. qed.

  lemma ppswap_eqP (xs ys:'a ppmap) :
    (ppswap xs = ppswap ys) = (xs = ys).
    rewrite eq_logical => |>. rewrite !ppmap_eqP /ppswap => |> H x y H0 H1.
    have : get (get (ppinit (fun (j i : int) => get (get xs i) j)) y) x = 
           get (get (ppinit (fun (j i : int) => get (get ys i) j)) y) x. 
    rewrite H => |>*. clear H. rewrite !get_ppinit !H1. simplify. rewrite !get_pinit !H0 => |>*. qed.

  lemma get_rlist_aux sz n xs :
    size (foldl (fun (rs : 'a array) (i : int) => set rs i (nth witness xs i)) (create sz witness) (iseq n)) = max 0 sz.
    elim/natind:n => |> i H.
    rewrite iseq_nil => |>*. rewrite size_init => |>*. 
    move => H1. rewrite iseq_succ // foldl_rcons => //=. rewrite size_set => //=. qed.

  lemma get_rlist sz (xs:'a list) n :
    0 <= n < size xs => size xs <= sz => get (rlist sz xs) n = nth witness xs n.
    rewrite /rlist => |>. pose szxs := size xs. have : 0 <= szxs /\ szxs <= size xs. rewrite /sz => |>. rewrite size_ge0 => |>. rewrite /szxs => />.
    elim/natind:szxs => |> n0 H H0 H1 H2 H3 H4.
    rewrite iseq_nil => |>. rewrite get_init => |>*. have : false. smt(size_ge0). progress.
    move => H5. rewrite iseq_succ => |>*. rewrite foldl_rcons => |>*. case (n=n0) => |>*.
    rewrite get_set_eqE => |> H6.
    rewrite get_rlist_aux //=. smt().
    rewrite get_set_neqE => |>*. smt(size_ge0). qed.

  lemma get_prlist sz (xs:pmsgs list) n :
    ISet.mem n partyset => get (prlist sz xs) n = rlist sz (map (transpose P.get n) xs).
    rewrite /prlist /rlist => |> H. rewrite size_map => |>. pose szxs := size xs. have : szxs <= size xs. smt(). 
    elim/natind:szxs => |> n0 H0 H1.
    rewrite !iseq_nil => |>. rewrite get_prempty => |>.  rewrite H => |>. 
    move => H2.
    rewrite !iseq_succ => |>. rewrite !foldl_rcons => |>*. rewrite get_prset => |>*. rewrite H1 => |>*. smt(size_ge0). rewrite (nth_map witness) => |>*. smt(size_ge0). smt(size_ge0).  qed.

  lemma prget_prlist sz (xs:pmsgs list) n :
    0 <= n < size xs => size xs <= sz => prget (prlist sz xs) n = nth witness xs n.
    rewrite pmap_eqP => |>*. rewrite get_prget => |>*. rewrite get_prlist => |>*. 
    rewrite get_rlist => |>*. rewrite size_map => |>*. rewrite size_map => |>*.
    rewrite (nth_map witness) => |>*. smt(). qed.

   op prmsgs_up_to (round:round) (ins:prmsgs) : prmsgs =
    prfilter (fun r => ISet.mem r (ISet.iset round)) ins.
  op pprmsgs_up_to (round:round) (ins:pprmsgs) : pprmsgs =
    pprfilter (fun r => ISet.mem r (ISet.iset round)) ins.

  op get_trace_inputs (tr:trace) : local_input pmap = map fst3 tr.
  op get_trace_in_msgs (tr:trace) : in_msgs pmap = map snd3 tr.
  op get_trace_rands (tr:trace) : local_rand pmap = map thr3 tr.
  op get_view (i:party) (tr:trace) : view = P.get tr i.

  op get_trace_in_msgs_round (round:round) (tr:trace) =
    pprget (get_trace_in_msgs tr) round.

  op get_view_in_msgs_round round (v:view) = 
    prget (snd3 v) round.

  op add_view_in_msgs (r:round) (ins:pmsgs) (v:view) : view =
    (fst3 v,(prset (snd3 v) r ins,thr3 v)).

  op get_trace_in_msgs_up_to round tr =
    pprmsgs_up_to round (get_trace_in_msgs tr).

  op add_trace_in_msgs (r:round) (ins:ppmsgs) (tr:trace) : trace =
    map (fun (ins_v:pmsgs*view) => add_view_in_msgs r ins_v.`1 ins_v.`2 ) (zip ins tr).

  op valid_trace (x:public_input) (tr:trace) =
    pprdom (rounds x) (rounds x) (get_trace_in_msgs tr).

  op valid_view (x:public_input) (v:view) =
    prdom (rounds x) (rounds x) (snd3 v).

  (** Properties **)

  lemma size_prmsgs_up_to n xs i :
    ISet.mem i partyset =>
    size (P.get (prmsgs_up_to n xs) i) = size (P.get xs i).
    move => H. rewrite /prmsgs_up_to /prfilter => />. rewrite get_map => />. move :H. rewrite /ISet.mem iset_in_def => />. rewrite size_filter => />. qed.

  lemma valid_get_trace_in_msgs x tr :
    valid_trace x tr => pprdom (rounds x) (rounds x) (get_trace_in_msgs tr).
    rewrite /valid_trace => |>*. qed.

  lemma valid_get_get_trace_in_msgs i x tr :
    valid_trace x tr /\ ISet.mem i partyset => prdom (rounds x) (rounds x) (P.get tr i).`2.`1.
    rewrite /valid_trace => |>*. have : prdom (rounds x) (rounds x) (P.get (get_trace_in_msgs tr) i). rewrite pprdom_prdom_get => |>*. rewrite /get_trace_in_msgs. rewrite get_pmap => |>*. qed.

  lemma valid_get_get_get_trace_in_msgs i j x tr :
    valid_trace x tr /\ ISet.mem i partyset /\ ISet.mem j partyset => rdom (rounds x) (rounds x) (P.get (P.get tr i).`2.`1 j).
    rewrite /valid_trace => /= H. rewrite prdom_rdom_get. smt(). 
    have : prdom (rounds x) (rounds x) (P.get (get_trace_in_msgs tr) i).
    rewrite pprdom_prdom_get => |>*. smt(). smt(). rewrite /get_trace_in_msgs. rewrite get_pmap => |>*. smt(). qed.

  lemma valid_get_trace_in_msgs_up_to tr n x :
    valid_trace x tr /\ 0 <= n /\ n <= (rounds x) => pprdom (rounds x) n (get_trace_in_msgs_up_to n tr).
    rewrite /valid_trace /get_trace_in_msgs_up_to => |> H1 H2 H3. rewrite /pprmsgs_up_to. rewrite /pprdom /pprfilter allP => |> i H5 H6. rewrite !get_map => |>*.  
    have : prdom (rounds x) (rounds x) (get (get_trace_in_msgs tr) i). rewrite (pprdom_prdom_get (rounds x)) => |>*. rewrite /ISet.mem iset_in_def  => |>*. progress.
    rewrite /prdom allP => |> j H7 H8. rewrite get_map => |>*. have : rdom (rounds x) (rounds x) (get (get (get_trace_in_msgs tr) i) j). rewrite (prdom_rdom_get (rounds x)) => |>*. rewrite /ISet.mem iset_in_def  => |>*.
    rewrite !/rdom /get_trace_in_msgs !get_map => |> H9 H10. rewrite size_init H9 ge0_max => |>. rewrite rounds_ge0 => |>. move => k H11.
    rewrite get_init => |>. case (0 <= k && k < size (get (snd3 (get tr i)) j)) => |>H12 H13. rewrite /ISet.mem iset_in_def => |>*. case (0 <= k /\ k < n) => |> H14 H15. rewrite H10 => |>*. smt(). qed.

  lemma get_pprmsgs_up_to i r xs :
    ISet.mem i partyset => P.get (pprmsgs_up_to r xs) i = (prmsgs_up_to r) (P.get xs i).
    progress. rewrite /pprmsgs_up_to /prmsgs_up_to /pprfilter. case (ISet.mem i partyset) => |>*. rewrite get_map => |>*. move :H. rewrite /ISet.mem iset_in_def  => |>*. qed.

  lemma prget_prmsgs_up_to_lt sz (n r:round) xs :
    (forall i, ISet.mem i partyset => Array.size (P.get xs i) = sz ) =>
    0 <= n /\ n < r /\ r <= sz =>
      prget (prmsgs_up_to r xs) n = prget xs n.
    rewrite tP => |> H1 H2 H3 H5 i H6 H7. rewrite /prget /pinit !get_init /prmsgs_up_to /prfilter => |>*. rewrite !get_map => |>*. rewrite get_init => |>*.
    case (0 <= n && n < sz) => |>H8. move => H9. rewrite /ISet.mem iset_in_def andaP => |>*. rewrite !andabP !andaP => |>*. have : n < size (get xs i). rewrite H1 => |>. rewrite /ISet.mem iset_in_def  => |>. progress. rewrite H => |>*.
    have : false. smt(). progress. qed.

  lemma prmsgs_up_to_0 sz xs :
    (forall i, ISet.mem i partyset => Array.size (P.get xs i) = sz) =>
    prmsgs_up_to 0 xs = prempty sz witness.
    rewrite /prmsgs_up_to /prempty /prfilter /pinit => |>. rewrite pmap_eqP => |>H i H0.
    rewrite get_pmap => |>. rewrite get_pinit => |>. rewrite H0 /ISet.mem /ISet.set0 => />. 
    rewrite Array.tP => |>*. rewrite !size_init => |>*. rewrite H => |>. progress. 
    rewrite !get_init => |>. rewrite H. rewrite H0. rewrite andabP andaP => |>. smt(size_ge0). rewrite /ISet.iset iset_fset0 => />. rewrite in_fset0 => |>*. qed.

  lemma pprmsgs_up_to_0 sz xs :
    (forall i j, ISet.mem i partyset => ISet.mem j partyset => Array.size (P.get (P.get xs i) j) = sz) =>
    pprmsgs_up_to 0 xs = pprempty sz witness.
    rewrite /pprmsgs_up_to /pprempty /pprfilter /ppinit /pinit => |>H. rewrite ppmap_eqP => |>x y H1 H2.
    rewrite get_pmap => |>*. rewrite get_pinit => |>*. rewrite H2 /ISet.mem /ISet.iset iset_fset0 => |>*. rewrite !get_pinit !H1 => |>*.
    rewrite get_pinit H2 => |>*. rewrite Array.tP => |>*. rewrite size_filter size_init => |>. rewrite -(H x y) => |>*. split. smt(size_ge0). progress.
    rewrite /empty !get_init andabP andaP => |>*. rewrite in_fset0 => |>*. qed.

  lemma prmsgs_up_to_min (n1 n2: round) xs :
    prmsgs_up_to n1 (prmsgs_up_to n2 xs) = prmsgs_up_to (min n1 n2) xs.
    rewrite /prmsgs_up_to /prfilter => |>*. rewrite tP => |>i H0 H1. rewrite !get_map => |>*. rewrite tP => |>*. rewrite !size_init. split. smt(size_ge0). progress.
    rewrite !get_init !andabP andaP => |>. rewrite size_init => |>. smt(size_ge0).
    rewrite get_init => |>*. have : 0 <= i0 /\ i0 < size (get xs i). smt(size_ge0). move => H3. rewrite !H3 => |>. rewrite /ISet.mem !iset_in_def => |>. 
    case (0 <= i0 /\ i0 < n1) => |>. smt(). smt(). qed.

  lemma prmsgs_up_to_lt (n1 n2:round) xs :
    n1 <= n2 => prmsgs_up_to n1 (prmsgs_up_to n2 xs) = prmsgs_up_to n1 xs.
    rewrite /prmsgs_up_to => |>H. rewrite /prfilter map_comp /(\o). congr. rewrite fun_ext => |>i. rewrite fun_ext => |>x. rewrite filter_comp. congr. rewrite fun_ext => |>i0. rewrite fun_ext => |>x0. rewrite /ISet.mem !iset_in_def => |>*. smt(). qed.

  lemma prmsgs_up_to_lt_set (n1 n2:round) ins xs :
    n1 <= n2 => prmsgs_up_to n1 (prset ins n2 xs) = prmsgs_up_to n1 ins.
    rewrite /prmsgs_up_to /prset => |>H. rewrite /prfilter tP => |>i H1 H2. rewrite !get_map => |>*. rewrite tP => |>*. rewrite !size_init => |>. rewrite ge0_max => |>. rewrite !get_init andabP andaP => |>. rewrite size_set size_ge0. rewrite !get_init andabP andaP => |>. rewrite ge0_max => |>. rewrite size_ge0. rewrite H1 H2 => |>. rewrite size_set => |>. rewrite H1 H2 => |>. rewrite size_set ge0_max => |>. rewrite size_ge0. progress.
    rewrite get_init andabP andaP => |>. rewrite size_set => |>. rewrite get_init andabP andaP => |>*. case (ISet.mem i0 (ISet.iset n1)) => |>H4. rewrite get_set_neqE => |>. rewrite /ISet.mem iset_in_def in H4. smt(). qed.

  lemma pprmsgs_up_to_lt_set (n1 n2:round) ins xs :
    n1 <= n2 => pprmsgs_up_to n1 (pprset ins n2 xs) = pprmsgs_up_to n1 ins.
    rewrite /pprmsgs_up_to /pprfilter => |>H. rewrite ppmap_eqP => |>x y H1 H2. 
    rewrite !get_pmap => |>*. rewrite !get_pmap => |>*. rewrite tP => |>*. rewrite !size_init => |>. rewrite get_pprset H1 => |>. rewrite get_prset H2 => |>. rewrite size_set => |>. move => i H5. rewrite ge0_max. rewrite size_ge0. move => H6. rewrite !get_init !andabP !andaP => |>. rewrite size_set => |>. 
    case (ISet.mem i (ISet.iset n1)) => |>H7. rewrite get_set_neqE => |>*. rewrite /ISet.mem iset_in_def in H7 => |>. smt(). qed.

  lemma prmsgs_up_to_id sz n1 n2 xs :
    prdom sz n1 xs /\ 0 <= n1 /\ n1 <= n2 => prmsgs_up_to n2 xs = xs.
    rewrite /prmsgs_up_to /prfilter => |>H H1 H2. move :H. rewrite /prdom => |>H3. rewrite pmap_eqP => |>x H4. rewrite !get_pmap => |>*. rewrite tP => |>*. rewrite !size_init => |>. rewrite ge0_max => |>. rewrite size_ge0 => |>. progress.
    rewrite get_init andabP andaP => |>*. case (ISet.mem i (ISet.iset n2)) => |>. rewrite /ISet.mem iset_in_def => |>. rewrite allP in H3 => |>. have : (fun (_ : int) => rdom sz n1) x (get xs x). rewrite H3 => |>*. move :H4. rewrite /ISet.mem iset_in_def  => |>. progress. move :H5. rewrite /rdom => |> H5. rewrite H5 => |>*. smt(). qed.

  lemma pprmsgs_up_to_id sz n1 n2 xs :
    pprdom sz n1 xs /\ 0 <= n1 /\ n1 <= n2 => pprmsgs_up_to n2 xs = xs.
    rewrite /pprmsgs_up_to /pprfilter => |>H H0 H1. move :H. rewrite /pprdom => |>H. rewrite ppmap_eqP => |>y j H3. rewrite !get_pmap => |>H4. rewrite get_pmap => |>*. rewrite tP => |>*. rewrite size_init ge0_max => |>. rewrite size_ge0. progress.
    rewrite get_init andabP andaP => |>*. case (ISet.mem i (ISet.iset n2)) => |>H7. move :H4 H3 H7. rewrite /ISet.mem !iset_in_def => |>N1 N2 N3 N4 N5. rewrite allP in H => |>*. have : (fun (_ : int) => prdom sz n1) y (get xs y). rewrite H => |>*. progress. rewrite /prdom allP in H3. have : (fun (_ : int) => rdom sz n1) j (get (get xs y) j). rewrite H3 => |>*.
    progress. move :H4. rewrite /rdom => |> H4. rewrite H4 => |>*. smt(). qed.

  lemma prdom_prmsgs_up_to sz (n1 n2:round) xs :
    (forall i, ISet.mem i partyset => Array.size (P.get xs i) = sz) =>
    n1 <= n2 => prdom sz n2 (prmsgs_up_to n1 xs).
    rewrite /prmsgs_up_to !/prdom /prfilter allP => |>H0 H1 i H2 H3. rewrite /rdom get_map => |>. rewrite size_init => |>. rewrite -(H0 i). rewrite /ISet.mem iset_in_def  => |>. rewrite ge0_max => |>. rewrite size_ge0 => |>. move => j Hj.
    rewrite get_init => |>*. case (0 <= j && j < size (get xs i)) => |>C1 C2. case (ISet.mem j (ISet.iset n1)) => |>C3. rewrite /ISet.mem iset_in_def in C3.
    have : false. smt(). progress. qed.

  lemma get_trace_in_msgs_up_to_succ n p tr : 
    (valid_trace p tr /\ ISet.mem n (roundset p)) => get_trace_in_msgs_up_to (n+1) tr = pprset (get_trace_in_msgs_up_to n tr) n (get_trace_in_msgs_round n tr).
    rewrite /get_trace_in_msgs_up_to /get_trace_in_msgs_round /pprset => |>H1 H2. rewrite /pprmsgs_up_to. rewrite /pprfilter /fmap_zip /uncurry. 
    rewrite pmap_eqP => |>x H3. rewrite /pprget /ppinit => |>*.
    have : pprdom (rounds p) (rounds p) (get_trace_in_msgs tr). rewrite valid_get_trace_in_msgs => |>*. progress. have : prdom (rounds p) (rounds p) (get (get_trace_in_msgs tr) x). rewrite pprdom_prdom_get => |>*. progress. rewrite get_map. move :H3. rewrite /ISet.mem iset_in_def  => |>*. 
    progress. rewrite /get_trace_in_msgs !get_pmap => |>*. rewrite !get_pmerge H3 => |>*. rewrite !get_pmap => |>*. rewrite get_pinit H3 => |>*. 
    rewrite pmap_eqP => |>x0 H4. rewrite get_pmerge H4 => |>*. rewrite !get_pmap => |>*. rewrite get_pinit H4 => |>. 
    rewrite tP => |>. rewrite /snd3 size_set !size_init => |>. move => i Hi1. rewrite ge0_max => |>. rewrite size_ge0 => |>. move => Hi2. rewrite get_init andabP andaP => |>.
    case (i=n) => |>. rewrite get_set_eqE => |>. rewrite size_init => |>. rewrite ge0_max => |>. rewrite size_ge0 => |>. rewrite /ISet.mem iset_in_def => |>. rewrite Hi1 gt_succ => |>. move => H7.
    rewrite get_set_neqE => |>. rewrite get_init /snd3 => |>. rewrite Hi1 Hi2 => |>. rewrite /ISet.mem !iset_in_def /snd3 => |>. rewrite !Hi1 => |>.
    have : i < n = i < n + 1. smt(). move => H8.
    rewrite -H8 => |>. qed.

  lemma get_trace_in_msgs_up_to_end p tr :
    valid_trace p tr => get_trace_in_msgs_up_to (rounds p) tr = get_trace_in_msgs tr.
    rewrite /valid_trace /get_trace_in_msgs_up_to /pprmsgs_up_to /pprfilter => |>H. 
    rewrite ppmap_eqP => |>x y H1 H2. rewrite !get_pmap => |>*. rewrite !get_pmap => |>*. 
    have : prdom (rounds p) (rounds p) (get (get_trace_in_msgs tr) x). rewrite pprdom_prdom_get => |>*. progress. have : rdom (rounds p) (rounds p) (get (get (get_trace_in_msgs tr) x) y). rewrite (prdom_rdom_get (rounds p)) => |>*. rewrite /rdom /get_trace_in_msgs !get_pmap => |>H3. rewrite tP => |>C. rewrite size_init /snd3 => |>. rewrite ge0_max => |>. rewrite size_ge0. move => i Hi1 Hi2. 
    rewrite get_init andabP andaP => |>. case (ISet.mem i (ISet.iset (rounds p))) => |>H6. rewrite C => |>*. move :H6. rewrite /ISet.mem iset_in_def => |>H6. smt(). qed.

  lemma get_trace_in_msgs_up_to_neg0 tr n p :
    valid_trace p tr => n <= 0 => get_trace_in_msgs_up_to n tr = pprempty (rounds p) witness.
    rewrite /valid_trace => |>H1 H2. rewrite pmap_eqP => |>x H3.
    have : prdom (rounds p) (rounds p) (get (get_trace_in_msgs tr) x). rewrite pprdom_prdom_get => |>*. progress. 
    rewrite /get_trace_in_msgs_up_to /in_msgs_up_to => |>*. rewrite pmap_eqP => |>y H4. 
    rewrite /pprmsgs_up_to /get_trace_in_msgs get_pprempty /pprfilter => |>. rewrite !get_pmap H3 => |>*. rewrite get_prempty get_map => |>*. move :H4. rewrite /ISet.mem iset_in_def  => |>*. rewrite H4 => |>*. rewrite tP => |>*. rewrite !size_init => |>. split. rewrite !ge0_max => |>. rewrite size_ge0 => |>. rewrite rounds_ge0 => |>. move :H. rewrite /prdom allP => |>H. have : rdom (rounds p) (rounds p) (get (get (get_trace_in_msgs tr) x) y). rewrite H => |>. move :H4. rewrite /ISet.mem iset_in_def  => |>. rewrite /rdom => |>H5 H6. rewrite /get_trace_in_msgs get_map in H5. move :H3. rewrite /ISet.mem iset_in_def  => |>. move :H5. rewrite /get_trace_in_msgs => |>. move => i H5 H6. 
    rewrite ge0_max in H6. rewrite size_ge0. rewrite !get_init andabP andaP => |>. case (ISet.mem i (ISet.iset n)) => |>H8. have : rdom (rounds p) (rounds p) (get (get (get_trace_in_msgs tr) x) y). rewrite prdom_rdom_get => |>. rewrite /rdom /get_trace_in_msgs => |>H9 H10.
    rewrite get_pmap in H9 => |>. have : get (get (get (map (fun (x0 : local_input * (in_msgs * local_rand)) => snd3 x0) tr) x) y) i = witness. rewrite H10 => |>. rewrite /ISet.mem iset_in_def in H8 => |>*. have : 0 <= rounds p. rewrite rounds_ge0 => |>*. smt().
    rewrite get_pmap /snd3 => |>*. qed.

  lemma map_head_pcons x (xs:('a list) pmap) :
    map (head witness) (pcons x xs) = x.
    rewrite /pcons => |>*. rewrite tP => |>*. rewrite get_map => |>*. rewrite get_merge => |>*. rewrite andabP andaP => |>*. qed.
  
  lemma map_behead_pcons x (xs:('a list) pmap) :
    map behead (pcons x xs) = xs.
    rewrite /pcons => |>*. rewrite tP => |>*. rewrite get_map => |>*. rewrite get_merge => |>*. rewrite andabP andaP => |>*. qed. 

  lemma phead_behead (xs:('a list) pmap) :
    all (fun _ x => 0 < List.size x) xs => 
      pcons (map (head witness) xs) (map behead xs) = xs.
    rewrite /pcons pmap_eqP allP => |>H x H1. rewrite get_pmerge H1 => |>*. rewrite !get_pmap => |>*.
    have : 0 < size (get xs x). rewrite H => |>*. move :H1. rewrite /ISet.mem iset_in_def => |>*. progress. rewrite head_behead => |>*. rewrite -size_nenil => |>*. qed.

  lemma pcons_eq x y (xs ys:('a list) pmap) :
    (x = y /\ xs = ys) = (pcons x xs = pcons y ys).
    rewrite eq_logical => |>H. progress. move :H. rewrite !pmap_eqP => |>H x0 H1.
    have : get (pcons x xs) x0 = get (pcons y ys) x0. rewrite H => |>*. 
    rewrite /pcons !get_pmerge !H1 => |>*.  
    move :H. rewrite !pmap_eqP => |>H x0 H1. have : get (pcons x xs) x0 = get (pcons y ys) x0. rewrite H => |>*. 
    rewrite /pcons !get_pmerge !H1 => |>*. qed.

  lemma pcons_eq_l x (xs ys:('a list) pmap) :
    (pcons x xs = ys) = (all (fun _ y => 0 < List.size y) ys /\ x = phead ys /\ xs = pbehead ys ).
    rewrite eq_logical => |>*. rewrite !allP => |>*. progress.
    rewrite /pcons get_pinit /ISet.mem iset_in_def  andaP => |>. have : 0 <= size (get xs i). rewrite size_ge0 => |>*. smt(). rewrite /phead map_head_pcons => |>*. rewrite /pbehead map_behead_pcons => |>*. rewrite phead_behead => |>*. rewrite allP => |>*. qed.

  lemma rdom0 (x:'a array) :
    rdom (Array.size x) 0 x = (x = Array.create (Array.size x) witness).
    rewrite Array.tP => |>*. rewrite /rdom => |>*. rewrite eq_logical => |>*. progress.
    rewrite size_init => |>*. smt(Array.size_ge0).
    rewrite Array.get_init H => |>*.
    case (i < Array.size x) => |>H2.
    rewrite H0 => |>*. rewrite Array.get_init => |>*. 
    rewrite Array.get_out => |>*. smt(). qed.

  lemma prdom0 (sz:int) (x:('a array) P.arrayN) :
    (forall i, ISet.mem i partyset => Array.size (P.get x i) = sz) =>
    prdom sz 0 x = (x = prempty sz witness).
    rewrite /prdom P.tP allP => |>. rewrite eq_logical => |>. progress.
    rewrite get_prempty => |>. rewrite /ISet.mem iset_in_def  andaP => |>. have : rdom sz 0 (get x i). rewrite H0 andabP andaP => |>. rewrite /rdom => |>H3. rewrite Array.tP => |>. rewrite size_init => |>. rewrite H => |>. rewrite /ISet.mem iset_in_def  => |>. rewrite ge0_max => |>. rewrite Array.size_ge0 => |>. move => j H4 H5. rewrite get_init H3 => |>. 
    rewrite /rdom H /prempty => |>. rewrite /ISet.mem iset_in_def  => |>.
    rewrite H0 => |>. rewrite get_pinit /ISet.mem iset_in_def  !andaP => |>. rewrite get_init => |>. qed.

  lemma pcat1s x (xs:('a list) pmap) :
    pcons x xs = pcat (P.map (fun x => [x]) x) xs.
    rewrite /pcons /pcat => |>*. rewrite pmap_eqP => |>y H. rewrite !get_pmerge !H => |>*.
    rewrite get_pmap => |>*. qed.

  lemma ppcat1s x (xs:('a list) ppmap) :
    ppcons x xs = ppcat (P.map (P.map (fun x => [x])) x) xs.
    rewrite /ppcons /ppcat => |>*. rewrite pmap_eqP => |>y H. rewrite !get_pmerge !H => |>*.
    rewrite get_pmap => |>*. rewrite pcat1s => |>*. qed.

  lemma pcats1 (xs:('a list) pmap) x :
    prcons xs x = pcat xs (P.map (fun x => [x]) x).
    rewrite /prcons /pcat => |>*. rewrite pmap_eqP => |>y H. rewrite !get_pmerge !H => |>*.
    rewrite get_pmap => |>*. rewrite cats1 => |>*. qed.

  lemma ppcats1 (xs:('a list) ppmap) x :
    pprcons xs x = ppcat xs (P.map (P.map (fun x => [x])) x).
    rewrite /pprcons /ppcat => |>*. rewrite pmap_eqP => |>y H. rewrite !get_pmerge !H => |>*.
    rewrite pcats1 => |>*. rewrite get_pmap => |>*. qed.

  lemma prcons_pcat (s1 s2:('a list) pmap) x :
    prcons (pcat s1 s2) x = pcat s1 (prcons s2 x).
    rewrite /prcons /pcat => |>*. rewrite pmap_eqP => |>y H. rewrite !get_pmerge !H => |>*. 
    rewrite (List.rcons_cat) => |>*. qed.

  lemma pprcons_ppcat (s1 s2:('a list) ppmap) x :
    pprcons (ppcat s1 s2) x = ppcat s1 (pprcons s2 x).
    rewrite /pprcons /ppcat => |>*. rewrite pmap_eqP => |>H H1. rewrite !get_pmerge !H1 => |>*. 
    rewrite prcons_pcat => |>*. qed.

  lemma ppcons_pprcons x (xs:('a list) ppmap) y :
    ppcons x (pprcons xs y) = pprcons (ppcons x xs) y.
    rewrite !ppcat1s. rewrite pprcons_ppcat => |>*. qed.

  lemma prmsgs_up_to_nesucc ins n j i:
    i <> n => 
    Array.get ((P.get ((prmsgs_up_to (n + 1) ins)) j)) i = Array.get ((P.get ((prmsgs_up_to n ins)) j)) i.
    rewrite /prmsgs_up_to /prfilter /filter => |>H. case (0 <= j < P.size) => |>H1. move => H0.
    rewrite !get_map => |>*. rewrite !Array.get_init => |>*. case (0 <= i < size (get ins j)) => |>H3 H4.
    case (ISet.mem i (ISet.iset n)) => |>H5. have : ISet.mem i (ISet.iset (n+1)). move :H5. rewrite /ISet.mem !iset_in_def => |>H6 H7. smt(). progress. rewrite H2 => |>*. have : !(ISet.mem i (ISet.iset (n+1))). move :H5. rewrite /ISet.mem !iset_in_def => |>H6. smt(). progress. rewrite H2 => |>*. 
    congr. rewrite !(get_out) => |>*. qed.

  lemma get_prmsgs_up_to_in (n n2:int) ins (i:int) :
    ISet.mem i partyset =>
    0 <= n2 => n2 < n => n2 < Array.size (P.get ins i) => 
    Array.get (P.get (prmsgs_up_to n ins) i) n2 = Array.get (P.get ins i) n2.
    rewrite /prmsgs_up_to /prfilter /filter /ISet.mem iset_in_def => />H1 H2 H3 H4 H5. rewrite get_map => />. rewrite get_init => />. have : n2 \in ISet.iset n. rewrite /ISet.iset iset_in_def => />. move => H6. rewrite H6 => />. rewrite andabP H3 H5 => />. qed.

  lemma get_prmsgs_up_to_out (n n2:int) ins i :
    ISet.mem i partyset => n <= n2 =>
    Array.get (P.get (prmsgs_up_to n ins) i) n2 = witness.
    rewrite /prmsgs_up_to /prfilter /filter => |>H1 H2. rewrite get_map => |>*. move :H1. rewrite /ISet.mem iset_in_def  => |>*. rewrite get_init => |>. case (0 <= n2 && n2 < size (get ins i)) => |>H3 H4. have : !((ISet.mem n2 ((ISet.iset n)))). rewrite /ISet.mem iset_in_def => |>. smt(size_ge0). move => H5. rewrite H5 => |>. qed.

end Trace.
