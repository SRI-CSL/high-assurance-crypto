require import AllCore List.

lemma headP (s : 'a list) (z0 : 'a) :
  0 < size s => head z0 s \in s.
proof. by elim s => //. qed.

lemma map_assoc (f : 'a -> 'b) (x : 'a) (s : 'a list) :
  x \in s => assoc (map (fun x => (x, f x)) s) x = Some (f x).
proof. 
  elim s => //= x' l hind h.
  case (x = x') => hx.
    by rewrite hx assoc_cons /=.
  by rewrite assoc_cons hx /= hind /#.
qed.

lemma map_assocN (f : 'a -> 'b) (x : 'a) (s : 'a list) :
  !(x \in s) => assoc (map (fun x => (x, f x)) s) x = None.
proof. 
  elim s => //= x' l hind h.
  by rewrite assoc_cons hind => /#. 
qed.

lemma unzip1_map_assoc (f : 'a -> 'b) (s : 'a list) :
  unzip1 (map (fun x => (x, f x)) s) = s.
proof. by elim s => //. qed.

lemma assoc_uniq_snd (x : 'a * 'b) (s : ('a * 'b) list) :
  uniq (unzip1 s) =>
  x \in s =>
  assoc s (fst x) = Some (snd x).
proof. 
  elim s => //= x'. 
  elim x => x1 x2 /=.
  elim x' => x1' x2' /=.
  move => l hind [h] uniql h1. smt.
qed.

lemma nth_assoc (x : 'a) (y : 'b) (s : ('a * 'b) list) i :
  0 <= i < size s =>
  nth (x,y) s i = (nth x (unzip1 s) i, nth y (unzip2 s) i).
proof.
  elim s => /> x' s; progress.
  case (i = 0); progress; first by smt().
  by smt.
qed.

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

lemma uniq_assoc (s : ('a * 'b) list) :
  uniq (unzip1 s) =>
  uniq s.
proof.
  elim s => //; progress; first by smt.
  by rewrite H.
qed.

(*lemma nth_assoc_unzip2 (x : 'a) (y : 'b) (s : ('a * 'b) list) i :
  uniq (unzip1 s) =>
  0 <= i < size s => nth y (unzip2 s) i = odflt y (assoc s (nth x (unzip1 s) i)).
proof.
search (assoc).
progress.
have : exists x' y', 
rewrite assoc_uniq_snd.



  elim s => /> x' s; progress.
  case (i = 0); progress.
print assoc_cons.
move : H0.
elim x' => x' y'.
progress.
rewrite assoc_cons.
have ->: nth x (unzip1 s) (i - 1) = x' <=> false.
smt.
simplify.
smt tmo=60.
smt(@List @ListExt).



  by smt(@List).
qed.*)

(* -------------------------------------------------------------------- *)
(*                           zip3 pairs                                 *)
(* -------------------------------------------------------------------- *)
op zip3 (ws : 'a list) (xs : 'b list) (ys : 'c list) : ('a * 'b * 'c) list =
  with ws = [], xs = [], ys = [] => []
  with ws = w :: ws', xs = [], ys = [] => []
  with ws = w :: ws', xs = x :: xs', ys = [] => []
  with ws = w :: ws', xs = [], ys = y :: ys' => []
  with ws = [], xs = x :: xs', ys = [] => []
  with ws = [], xs = x :: xs', ys = y :: ys' => []
  with ws = [], xs = [], ys = y :: ys' => []
  with ws = w :: ws', xs = x :: xs', ys = y :: ys' => (w, x, y) :: zip3 ws' xs' ys'.

abbrev unzip3_1 (s : ('a * 'b * 'c) list) : 'a list = map (fun wxy => let (w,x,y) = wxy in w) s.
abbrev unzip3_2 (s : ('a * 'b * 'c) list) : 'b list = map (fun wxy => let (w,x,y) = wxy in x) s.
abbrev unzip3_3 (s : ('a * 'b * 'c) list) : 'c list = map (fun wxy => let (w,x,y) = wxy in y) s.

lemma zip3_unzip (s : ('a * 'b * 'c) list) :
  zip3 (unzip3_1 s) (unzip3_2 s) (unzip3_3 s) = s.
proof. by elim: s => // -[x y s]. qed.

lemma unzip3_1_zip ['a 'b 'c] (ws : 'a list) (xs : 'b list) (ys : 'c list) :
  size ws <= size xs <= size ys => unzip3_1 (zip3 ws xs ys) = ws.
proof.
  elim: ws xs ys; first by smt(size_ge0).
  simplify => w ws hind1 xs ys.
  elim: xs ys; first by smt(size_ge0).
  simplify => x xs hind2 ys [hsize].
  elim: ys; first by smt(size_ge0).
  by simplify => y ys ?; rewrite hind1 /#.
qed.

lemma unzip3_2_zip ['a 'b 'c] (ws : 'a list) (xs : 'b list) (ys : 'c list) :
  size xs <= size ws <= size ys => unzip3_2 (zip3 ws xs ys) = xs.
proof.
  elim: ws xs ys; first by smt(size_ge0).
  simplify => w ws hind1 xs ys.
  elim: xs ys; first by smt(size_ge0).
  simplify => x xs hind2 ys [hsize].
  elim: ys; first by smt(size_ge0).
  by simplify => y ys ?; rewrite hind1 /#.
qed.

lemma unzip3_3_zip ['a 'b 'c] (ws : 'a list) (xs : 'b list) (ys : 'c list) :
  size ys <= size ws <= size xs => unzip3_3 (zip3 ws xs ys) = ys.
proof.
  elim: ys ws xs; first by smt(size_ge0).
  simplify => y ys hind1 ws xs.
  elim: ws xs; first by smt(size_ge0).
  simplify => w ws hind2 xs [hsize].
  elim: xs; first by smt(size_ge0).
  by simplify => x xs ?; rewrite hind1 /#.
qed.

lemma size1_zip3 ['a 'b 'c] (ws : 'a list) (xs : 'b list) (ys : 'c list) :
  size ws <= size xs <= size ys => size (zip3 ws xs ys) = size ws.
proof.
  elim: ws xs ys; first by smt(size_ge0).
  simplify => w ws hind1 xs ys.
  elim: xs ys; first by smt(size_ge0).
  simplify => x xs hind2 ys [hsize].
  elim: ys; first by smt(size_ge0).
  by simplify => y ys ?; rewrite hind1 /#.
qed.

lemma size2_zip3 ['a 'b 'c] (ws : 'a list) (xs : 'b list) (ys : 'c list) :
  size xs <= size ws <= size ys => size (zip3 ws xs ys) = size xs.
proof.
  elim: ws xs ys; first by smt(size_ge0).
  simplify => w ws hind1 xs ys.
  elim: xs ys; first by smt(size_ge0).
  simplify => x xs hind2 ys [hsize].
  elim: ys; first by smt(size_ge0).
  by simplify => y ys ?; rewrite hind1 /#.
qed.

lemma size3_zip3 ['a 'b 'c] (ws : 'a list) (xs : 'b list) (ys : 'c list) :
  size ys <= size ws <= size xs => size (zip3 ws xs ys) = size ys.
proof.
  elim: ys ws xs; first by smt(size_ge0).
  simplify => y ys hind1 ws xs.
  elim: ws xs; first by smt(size_ge0).
  simplify => w ws hind2 xs [hsize].
  elim: xs; first by smt(size_ge0).
  by simplify => x xs ?; rewrite hind1 /#.
qed.

lemma size_zip3 ['a 'b 'c] (ws : 'a list) (xs : 'b list) (ys : 'c list) :
  size (zip3 ws xs ys) = min (min (size ws) (size xs)) (size ys).
proof. 
  elim: ws xs ys; first by smt(size_ge0).
  simplify => w ws hind1 xs ys.
  elim: xs ys; first by smt(size_ge0).
  simplify => x xs hind2 ys.
  elim: ys; first by smt(size_ge0).
  by simplify => y ys; rewrite hind1 /#.
qed.

(*lemma zip_cat ['a 'b] (s1 s2 : 'a list) (t1 t2 : 'b list) :
  size s1 = size t1 => zip (s1 ++ s2) (t1 ++ t2) = zip s1 t1 ++ zip s2 t2.
proof. elim: s1 t1 => [|x s1 ih] [|y t1] //=; smt(size_ge0). qed.*)

lemma nth_zip3 ['a 'b 'c] (ws : 'a list) (xs : 'b list) (ys : 'c list) w x y i :
  size ws = size xs => size xs = size ys => nth (w,x,y) (zip3 ws xs ys) i = (nth w ws i, nth x xs i, nth y ys i).
proof. by elim: ws xs ys i => [|xs s ih] [|xt t] //=; smt(size_ge0). qed.

(*lemma nth_zip_cond ['a 'b] p (s : 'a list) (t : 'b list) i :
   nth p (zip s t) i
     = (if i < size (zip s t) then (nth p.`1 s i, nth p.`2 t i) else p).
proof.
case: (i < 0) => [le0_i|].
+ by rewrite !nth_neg // -(pairS p) if_same.
by elim: s t i => [|x s ih] [|y t] i //=; (move=> ->// || smt(size_ge0)).
qed.*)

(*lemma zip_rcons ['a 'b] s1 s2 (z1 : 'a) (z2 : 'b) :
  size s1 = size s2 =>
    zip (rcons s1 z1) (rcons s2 z2) = rcons (zip s1 s2) (z1, z2).
proof. by move=> eq_sz; rewrite -!cats1 zip_cat //= eq_sz. qed.*)

(*lemma rev_zip ['a 'b] (s1 : 'a list) (s2 : 'b list) :
  size s1 = size s2 => rev (zip s1 s2) = zip (rev s1) (rev s2).
proof.
elim: s1 s2 => [|x s1 ih] [|y s2] //=; 1,2: smt(size_ge0).
by move/addzI=> eq_sz; rewrite !(rev_cons, zip_rcons) ?size_rev // ih.
qed.*)

lemma mem_zip3 ['a 'b 'c] ws xs ys (w : 'a) (x : 'b) (y : 'c) :
  (w, x, y) \in zip3 ws xs ys => w \in ws /\ x \in xs /\ y \in ys.
proof.
  elim: ws xs ys; first by smt(size_ge0).
  simplify => w' ws hind1 xs ys.
  elim: xs ys; first by smt(size_ge0).
  simplify => x' xs hind2 ys.
  elim: ys; first by smt(size_ge0).
  by simplify => y' ys /#.
qed.

lemma nosmt mem_zip3_fst ['a 'b 'c] (ws : 'a list) (xs : 'b list) (ys : 'c list) w x y:
  (w,x,y) \in zip3 ws xs ys => w \in ws.
proof. by smt. qed.

lemma nosmt mem_zip3_snd ['a 'b 'c] (ws : 'a list) (xs : 'b list) (ys : 'c list) w x y:
  (w,x,y) \in zip3 ws xs ys => x \in xs.
proof. by smt. qed.

lemma nosmt mem_zip3_trd ['a 'b 'c] (ws : 'a list) (xs : 'b list) (ys : 'c list) w x y:
  (w,x,y) \in zip3 ws xs ys => y \in ys.
proof. by smt. qed.

(*lemma zip_map ['a1 'a2 'b1 'b2] (f : 'a1 -> 'a2) (g : 'b1 -> 'b2) xs ys :
    zip (map f xs) (map g ys)
  = map (fun xy => (f (fst xy), g (snd xy))) (zip xs ys).
proof. by elim: xs ys => [|x xs ih] [|y ys] //=; rewrite ih. qed.*)

(*lemma zip_mapl ['a1 'a2 'b] (f : 'a1 -> 'a2) xs (ys : 'b list) :
  zip (map f xs) ys = map (fun xy => (f (fst xy), snd xy)) (zip xs ys).
proof. by rewrite -(@map_id ys) zip_map map_id. qed.*)

(*lemma zip_mapr ['a 'b1 'b2] (g : 'b1 -> 'b2) (xs : 'a list) ys :
  zip xs (map g ys) = map (fun xy => (fst xy, g (snd xy))) (zip xs ys).
proof. by rewrite -(@map_id xs) zip_map map_id. qed.*)

(*lemma assoc_zip ['a, 'b] (ks : 'a list) (vs : 'b list) k:
 size ks = size vs => assoc (zip ks vs) k = onth vs (index k ks).
proof.
elim: ks vs => [|k' ks ih] [|v vs] //=; rewrite ?(assoc_cons, index_cons).
+ by rewrite eq_sym addzC addz1_neq0.
move/addzI => /ih -> /=; case: (k = k') => //=.
by rewrite addz1_neq0 1:index_ge0.
qed.*)

(*lemma map_fst_zip ['a1, 'a2, 'b] (f : 'a1 -> 'a2) xs (ys : 'b list) :
 size xs = size ys => map (f \o fst) (zip xs ys) = map f xs.
proof. by move => eq_sz; rewrite map_comp unzip1_zip // eq_sz. qed.*)

(*lemma map_snd_zip ['a, 'b1, 'b2] (g : 'b1 -> 'b2) (xs : 'a list) ys :
 size xs = size ys => map (g \o snd) (zip xs ys) = map g ys.
proof. by move => eq_sz; rewrite map_comp unzip2_zip // eq_sz. qed.*)

(*lemma nosmt zip_map_proj ['a, 'b, 'c] (f : 'a -> 'b * 'c) xs:
  zip (map (fst \o f) xs) (map (snd \o f) xs) = map f xs.
proof. by elim: xs => // x xs ih @/(\o) /=; rewrite ih /=; case: (f x). qed.*)

(*lemma nosmt onth_zip_some ['a 'b] (xs : 'a list) (ys : 'b list) n xy:
      onth (zip xs ys) n = Some xy
  <=> (onth xs n = Some (fst xy)) /\ (onth ys n = Some (snd xy)).
proof.
elim: xs ys n => [|x xs ih] [|y ys] n //=; case: xy ih => [x' y'] ih.
by case: (n = 0) => // _; apply/ih.
qed.*)

(*lemma nosmt eq_keys_amap ['a, 'b1, 'b2, 'c]
  (f : 'a -> 'b1 -> 'c) (g : 'a -> 'b2 -> 'c) xs ys
: amap f xs = amap g ys => unzip1 xs = unzip1 ys.
proof. move=> eq_amap.
have ->: (map fst xs) = (map fst (amap f xs)) by rewrite -map_comp.
have ->: (map fst ys) = (map fst (amap g ys)) by rewrite -map_comp.
by rewrite eq_amap.
qed.*)

(*lemma assoc_amap ['a, 'b, 'c] (f : 'a -> 'b -> 'c) xs k:
 assoc (amap f xs) k = omap (f k) (assoc xs k).
proof.
elim: xs => /= [|[k' v'] xs ih]; 1: by rewrite !assoc_nil.
by rewrite !assoc_cons /=; case: (k = k').
qed.*)

(*lemma nosmt map_zip_nth ['a, 'b, 'c] dk dv (f: 'a * 'b -> 'c) ks vs:
 size ks = size vs => map f (zip ks vs)
   = map (fun i => f (nth dk ks i, nth dv vs i)) (range 0 (size ks)).
proof.
move=> eq_sz; rewrite -(@map_nth_range (dk, dv) (zip ks vs)).
rewrite /range /= size_zip /min eq_sz //= -map_comp.
by apply: eq_in_map => i @/(\o); rewrite mem_iota /= nth_zip.
qed.*)

(*lemma amap_assoc_zip ['a, 'b, 'c] (f : 'a -> 'b -> 'c) ks vs:
 size ks = size vs => uniq ks => amap f (zip ks vs) =
   amap (fun k _ => f k (nth witness vs (index k ks))) (zip ks vs).
proof.
move=> eq_sz uq_ks; rewrite (map_zip_nth witness witness) //= eq_sym.
rewrite (map_zip_nth witness witness) //= &(eq_in_map).
by move=> x /mem_range [? ?] /=; congr; rewrite index_uniq.
qed.*)

(* -------------------------------------------------------------------- *)
(*                               sumt                                   *)
(* -------------------------------------------------------------------- *)
from General require import PrimeField.

op sumt (st : t list) = foldr fadd fzero st.

lemma sumt0 : sumt [] = fzero.
proof. by rewrite /sumt /=. qed.

lemma sumt_cons x st : sumt (x :: st) = fadd x (sumt st).
proof. by rewrite /sumt /=. qed.

lemma sumt_distr (st : t list) c :
  fmul c (sumt st) = sumt (map (fun x => fmul c x) st).
proof.
  elim st => /=; first by rewrite sumt0; ringeq.
  by move => x st; progress; rewrite !sumt_cons -H; ringeq.
qed.

lemma sumt_comm_assoc (s s' : t list) f :
  sumt (map (fun x => sumt (map (fun y => f x y) s)) s') =
  sumt (map (fun y => sumt (map (fun x => f x y) s')) s).
proof. admit. qed.
