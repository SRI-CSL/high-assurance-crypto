require import AllCore List Distr Dfilter.
require import RealFun RealSeq RealSeries.
require import Ring StdRing StdOrder StdBigop Discrete.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.

from General require import CyclicGroup PrimeField.

lemma existsN : forall (p : 'a -> bool), !(exists x, p x) <=> (forall x, !p x) by [].
lemma forallN : forall (p : 'a -> bool), !(forall x, p x) <=> (exists x, !p x) by [].

op uncurry (f : 'a -> 'b -> 'c) (xy:'a*'b) : 'c =
  f xy.`1 xy.`2.

op prod (f: 'a -> 'c) (g: 'b -> 'd) (ab:'a * 'b) : ('c * 'd) =
  (f ab.`1, g ab.`2).

lemma prod_id (xy:'a*'b) :
  xy = (xy.`1,xy.`2) by elim xy => />*.  

lemma prod3_id (x:'a*('b*'c)) :
  x = (x.`1,(x.`2.`1,x.`2.`2)) by elim x => /> x2; elim x2 => />*. 

lemma eq2 (x y:'a*'b) :
  (x = y) = ((x.`1 = y.`1) /\ (x.`2 = y.`2)) by case x => />*; case y => />*. 

lemma eq3 (x y:'a*('b*'c)) :
  (x = y) = ((x.`1 = y.`1) /\ (x.`2.`1 = y.`2.`1) /\ (x.`2.`2 = y.`2.`2)) by
    case x => />*; case y => />*; rewrite !eq2 => />*. 

lemma eq_logical (p1:bool) (p2:bool) :
  (p1 = p2) = (p1 <=> p2) by [].

lemma min_eq (x:int) : min x x = x by []. 

lemma ge0_max (x:int) : 0 <= x => max 0 x = x by [].

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

(* ==================================================================== *)
(** Party identifiers *)
type pid_zk_t = [ | Prover | Verifier ].
type pid_mpc_t = [ | P1 | P2 | P3 | P4 | P5 ].
op pid_mpc_set = [P1;P2;P3;P4;P5].

(*op pid_mpc_distr_f : pid_mpc_t -> real = fun pid => if pid \in pid_mpc_set then inv 5%r else 0%r.*)
op pid_mpc_distr_f : pid_mpc_t -> real = fun pid => inv 5%r.
op pid_mpc_distr : pid_mpc_t distr = mk pid_mpc_distr_f.

lemma uniq_mpc_size (s : pid_mpc_t list) : uniq s => size s <= 5.
proof.
  elim s => // x s.
  elim s => // x1 s.
  elim s => // x2 s.
  elim s => // x3 s.
  elim s => // x4 s.
  by smt().
qed.

lemma uniq_mpc_sizeN (s : pid_mpc_t list) x : !(x \in s) => uniq s => size s <= 4.
proof.
  elim s => // x1 s.
  elim s => // x2 s.
  elim s => // x3 s.
  elim s => // x4 s.
  elim s => // x5 s.
  by smt().
qed.

lemma isdistr_pid_mpc_distr_f : isdistr pid_mpc_distr_f.
proof.
  split => s; first by smt().
  elim s; first by smt().
  move => x s; elim s; first by rewrite /big /= /predT /= /#.
  move => x1 s; elim s; first by rewrite /big /= /predT /= /#.
  move => x2 s; elim s; first by rewrite /big /= /predT /= /#.
  move => x3 s; elim s; first by rewrite /big /= /predT /= /#.
  move => x4 s; elim s; first by rewrite /big /= /predT /= /#.
  by smt().
qed.

lemma pid_mpc_distr1E x :
  mu1 pid_mpc_distr x = inv 5%r.
proof. 
rewrite /pid_mpc_distr.
rewrite -massE.
rewrite muK //.
apply isdistr_pid_mpc_distr_f.
qed.

lemma supp_pid_mpc_distr x :
  x \in pid_mpc_distr <=> x \in pid_mpc_set.
proof.
rewrite supportP pid_mpc_distr1E. simplify.
by case x; rewrite /pid_mpc_set // => /#. 
qed.

lemma weight_pid_mpc_distr:
  weight pid_mpc_distr = 1%r.
proof. 
  rewrite muE (sumE_fin (mass pid_mpc_distr) pid_mpc_set).
    by rewrite /pid_mpc_set //.
    by smt().
    by rewrite /big /pid_mpc_set filter_predT foldr_map /= !massE !pid_mpc_distr1E. 
qed.

lemma pid_mpc_distr_ll : is_lossless pid_mpc_distr. 
proof. by rewrite /is_lossless weight_pid_mpc_distr. qed.

op pid_mpc_tuple_distr : (pid_mpc_t * pid_mpc_t) distr = pid_mpc_distr `*` pid_mpc_distr.
op challenge_distr : (pid_mpc_t * pid_mpc_t) distr.

axiom challenge_distr1E x :
  mu1 challenge_distr x = inv 10%r.

axiom pid_mpc_distr_tuple_ll : is_lossless pid_mpc_tuple_distr. 

op next_pid (pid : pid_mpc_t) : pid_mpc_t =
  with pid = P1 => P2
  with pid = P2 => P3
  with pid = P3 => P4
  with pid = P4 => P5
  with pid = P5 => P1.

op get_party_data (pid : pid_mpc_t) (x : 'a * 'a * 'a * 'a * 'a) : 'a =
  with pid = P1 => let (x1,x2,x3,x4,x5) = x in x1
  with pid = P2 => let (x1,x2,x3,x4,x5) = x in x2
  with pid = P3 => let (x1,x2,x3,x4,x5) = x in x3
  with pid = P4 => let (x1,x2,x3,x4,x5) = x in x4
  with pid = P5 => let (x1,x2,x3,x4,x5) = x in x5.

op get_other_pids (i j : pid_mpc_t) : pid_mpc_t * pid_mpc_t * pid_mpc_t =
  with i = P1, j = P1 => (P3,P4,P5) (*witness*)
  with i = P1, j = P2 => (P3,P4,P5)
  with i = P1, j = P3 => (P2,P4,P5)
  with i = P1, j = P4 => (P2,P3,P5)
  with i = P1, j = P5 => (P2,P3,P4)

  with i = P2, j = P1 => (P3,P4,P5)
  with i = P2, j = P2 => (P3,P4,P5) (*witness*)
  with i = P2, j = P3 => (P1,P4,P5)
  with i = P2, j = P4 => (P1,P3,P5)
  with i = P2, j = P5 => (P1,P3,P4)

  with i = P3, j = P1 => (P2,P4,P5)
  with i = P3, j = P2 => (P1,P4,P5)
  with i = P3, j = P3 => (P1,P4,P5) (*witness*)
  with i = P3, j = P4 => (P1,P2,P5)
  with i = P3, j = P5 => (P1,P2,P4)

  with i = P4, j = P1 => (P2,P3,P5)
  with i = P4, j = P2 => (P1,P3,P5)
  with i = P4, j = P3 => (P1,P2,P5)
  with i = P4, j = P4 => (P1,P2,P5) (*witness*)
  with i = P4, j = P5 => (P1,P2,P3)

  with i = P5, j = P1 => (P2,P3,P4)
  with i = P5, j = P2 => (P1,P3,P4)
  with i = P5, j = P3 => (P1,P2,P4)
  with i = P5, j = P4 => (P1,P2,P3)
  with i = P5, j = P5 => (P1,P2,P3) (*witness*).

op replace5_tuple (x : (pid_mpc_t * 'a) * (pid_mpc_t * 'a) * 
                       (pid_mpc_t * 'a) * (pid_mpc_t * 'a) * (pid_mpc_t * 'a)) 
                  (pid : pid_mpc_t) (xi : 'a) =
  with pid = P1 => let (x1,x2,x3,x4,x5) = x in ((pid,xi),x2,x3,x4,x5)
  with pid = P2 => let (x1,x2,x3,x4,x5) = x in (x1,(pid,xi),x3,x4,x5)
  with pid = P3 => let (x1,x2,x3,x4,x5) = x in (x1,x2,(pid,xi),x4,x5)
  with pid = P4 => let (x1,x2,x3,x4,x5) = x in (x1,x2,x3,(pid,xi),x5)
  with pid = P5 => let (x1,x2,x3,x4,x5) = x in (x1,x2,x3,x4,(pid,xi)).

op assemble (xa xb xc xd xe : (pid_mpc_t * 'a)) =
  let (a,xa) = xa in
  let (b,xb) = xb in
  let (c,xc) = xc in
  let (d,xd) = xd in
  let (e,xe) = xe in

  replace5_tuple (replace5_tuple (replace5_tuple (replace5_tuple (replace5_tuple (witness, witness, witness, witness, witness) a xa) b xb) c xc) d xd) e xe.

op tuple5_to_list (x : 'a * 'a * 'a * 'a * 'a) : 'a list =
  let (x1,x2,x3,x4,x5) = x in
  [x1;x2;x3;x4;x5].

lemma assocP1 (x y z w v : 'a) : 
assoc [(P1, x); (P2, y); (P3, z); (P4, w); (P5, v)] P1 = Some x.
proof.
smt().
qed.

lemma assocP2 (x y z w v : 'a) : 
assoc [(P1, x); (P2, y); (P3, z); (P4, w); (P5, v)] P2 = Some y.
proof.
smt().
qed.

lemma assocP3 (x y z w v : 'a) : 
assoc [(P1, x); (P2, y); (P3, z); (P4, w); (P5, v)] P3 = Some z.
proof.
smt().
qed.

lemma assocP4 (x y z w v : 'a) : 
assoc [(P1, x); (P2, y); (P3, z); (P4, w); (P5, v)] P4 = Some w.
proof.
smt().
qed.

lemma assocP5 (x y z w v : 'a) : 
assoc [(P1, x); (P2, y); (P3, z); (P4, w); (P5, v)] P5 = Some v.
proof.
smt().
qed.

(* -------------------------------------------------------------------- *)
(*                               sumt                                   *)
(* -------------------------------------------------------------------- *)
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

axiom sumt_comm_assoc (s s' : t list) f :
  sumt (map (fun x => sumt (map (fun y => f x y) s)) s') =
  sumt (map (fun y => sumt (map (fun x => f x y) s')) s).

lemma sumt_map_fzero (st : t list) :
  sumt (map (fun _ => fzero) st) = fzero.
proof.
  elim st => /=; first by rewrite sumt0; ringeq.
  by move => x st; progress rewrite !sumt_cons st; ringeq.
qed.

(******)
require import DList.

module RsumR = {
  proc gen(n : int, s : t) = {
    var ds;
    ds <$ dlist FDistr.dt n;
    return (fsub s (sumt ds) :: ds);
  }
}.

module RsumI = {
  proc gen(n : int) = {
    var ds;
    ds <$ dlist FDistr.dt (n+1);
    return (ds);
  }
}.

axiom eq_rand_gen : equiv [ RsumR.gen ~ RsumI.gen : ={n} ==> ={res} ].
