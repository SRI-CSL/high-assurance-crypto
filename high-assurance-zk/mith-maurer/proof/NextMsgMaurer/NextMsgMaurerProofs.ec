require import AllCore Int List FSet SmtMap Distr PrimeField Ring.
require import Aux AuxList AuxFSet AuxSmtMap AuxArray.
require import Array5 Array6 Array9 Array10.
require import NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgCircuit.
require import NextMsgWeak NextMsgWeakProofs NextMsgWeakCircuit NextMsgWeakCircuitProofs NextMsgMPC NextMsgMPCProofs NextMsgMPCReveal NextMsgMPCRevealProofs NextMsgMaurer NextMsgMaurerMPC.
require import NextMsgMaurerAuxProofs NextMsgMaurerAddProofs NextMsgMaurerMulProofs NextMsgMaurerConstProofs NextMsgMaurerSMulProofs.

require import NextMsgISet NextMsgIMap NextMsgMaurerP NextMsgMaurerAPI.

require import Maurer5Spec.
import Maurer5Spec.
import Maurer5SS.

lemma valid_rands_add g cs :
  MaurerGate.valid_rands (MaurerGate.Add g) cs = (MaurerP.all (constfun isL) cs /\ MaurerAdd.valid_rands g (MaurerP.map unL cs)).
  rewrite /gate_valid_rands /valid_rands. rewrite /MaurerP.all !allP /consistent_rands => />*. rewrite eq_logical => />*. progress. rewrite /constfun => />*. have : MaurerGate.gate_valid_rand (MaurerGate.Add g) (MaurerGate.ST.P.get cs x) /\ MaurerGate.gate_valid_rand (MaurerGate.Add g) (MaurerGate.ST.P.get cs x). rewrite H => />. move :H0. rewrite /ISet.mem /ISet.iset !iset_in_def in_iseq => />. rewrite /gate_valid_rand => />*.
  have : constfun isL i (MaurerP.get cs i). rewrite H => />. move :H1. rewrite /ISet.mem /ISet.iset iset_in_def in_iseq => />. rewrite /constfun => />. 
  have : constfun isL j (MaurerP.get cs j). rewrite H => />. move :H2. rewrite /ISet.mem /ISet.iset iset_in_def in_iseq => />. rewrite /constfun => />. qed.

lemma valid_rands_smul g cs :
  MaurerGate.valid_rands (MaurerGate.SMul g) cs = (MaurerP.all (constfun isL) cs /\ MaurerSMul.valid_rands g (MaurerP.map unL cs)).
  rewrite /gate_valid_rands /valid_rands. rewrite /MaurerP.all !allP /consistent_rands => />*. rewrite eq_logical => />*. progress. rewrite /constfun => />*. have : MaurerGate.gate_valid_rand (MaurerGate.SMul g) (MaurerGate.ST.P.get cs x) /\ MaurerGate.gate_valid_rand (MaurerGate.SMul g) (MaurerGate.ST.P.get cs x). rewrite H => />. move :H0. rewrite /ISet.mem /ISet.iset !iset_in_def in_iseq => />. rewrite /gate_valid_rand => />*.
  have : constfun isL i (MaurerP.get cs i). rewrite H => />. move :H1. rewrite /ISet.mem /ISet.iset iset_in_def in_iseq => />. rewrite /constfun => />. 
  have : constfun isL j (MaurerP.get cs j). rewrite H => />. move :H2. rewrite /ISet.mem /ISet.iset iset_in_def in_iseq => />. rewrite /constfun => />. qed.

lemma valid_rands_const g cs :
  MaurerGate.valid_rands (MaurerGate.Const g) cs = (MaurerP.all (constfun isL) cs /\ MaurerConst.valid_rands g (MaurerP.map unL cs)).
  rewrite /gate_valid_rands /valid_rands. rewrite /MaurerP.all !allP /consistent_rands => />*. rewrite eq_logical => />*. progress. rewrite /constfun => />*. have : MaurerGate.gate_valid_rand (MaurerGate.Const g) (MaurerGate.ST.P.get cs x) /\ MaurerGate.gate_valid_rand (MaurerGate.Const g) (MaurerGate.ST.P.get cs x). rewrite H => />. move :H0. rewrite /ISet.mem /ISet.iset !iset_in_def in_iseq => />. rewrite /gate_valid_rand => />*.
  have : constfun isL i (MaurerP.get cs i). rewrite H => />. move :H1. rewrite /ISet.mem /ISet.iset iset_in_def in_iseq => />. rewrite /constfun => />. 
  have : constfun isL j (MaurerP.get cs j). rewrite H => />. move :H2. rewrite /ISet.mem /ISet.iset iset_in_def in_iseq => />. rewrite /constfun => />. qed.

lemma valid_rands_mul g cs :
  MaurerGate.valid_rands (MaurerGate.Mul g) cs = (MaurerP.all (constfun isR) cs /\ MaurerMul.valid_rands g (MaurerP.map unR cs)).
  rewrite /valid_rands /gate_valid_rands. rewrite /all !allP /constfun /ISet.mem /ISet.iset => />*. rewrite eq_logical => />*. progress.
  have : MaurerGate.consistent_rands (MaurerGate.Mul g) x x (MaurerGate.ST.P.get cs x) (MaurerGate.ST.P.get cs x). rewrite H => />. move :H0. rewrite !iset_in_def in_iseq => />. rewrite /consistent_rands => />. rewrite H => />. move :H1. rewrite iset_in_def /parties in_iseq => />. rewrite H => />. move :H2. rewrite iset_in_def /parties in_iseq => />. qed.

lemma valid_inputs_add g ws :
  MaurerGate.valid_inputs (MaurerGate.Add g) ws => MaurerAdd.valid_inputs g ws.
  rewrite /valid_inputs /ISet.mem /ISet.iset => />H i j Hi Hj. have : (MaurerGate.consistent_inputs (MaurerGate.Add g) i j ((MaurerGate.ST.P.get ws i)) ((MaurerGate.ST.P.get ws j))). rewrite H => />*. rewrite /consistent_inputs => />*. qed.

lemma valid_inputs_smul g ws :
  MaurerGate.valid_inputs (MaurerGate.SMul g) ws => MaurerSMul.valid_inputs g ws.
  rewrite /valid_inputs /ISet.mem /ISet.iset => />H i j Hi Hj. have : (MaurerGate.consistent_inputs (MaurerGate.SMul g) i j ((MaurerGate.ST.P.get ws i)) ((MaurerGate.ST.P.get ws j))). rewrite H => />*. rewrite /consistent_inputs => />*. qed.

lemma valid_inputs_const g ws :
  MaurerGate.valid_inputs (MaurerGate.Const g) ws => MaurerConst.valid_inputs g ws.
  rewrite /valid_inputs /ISet.mem /ISet.iset => />H i j Hi Hj. have : (MaurerGate.consistent_inputs (MaurerGate.Const g) i j ((MaurerGate.ST.P.get ws i)) ((MaurerGate.ST.P.get ws j))). rewrite H => />*. rewrite /consistent_inputs => />*. qed.

lemma valid_inputs_mul g ws :
  MaurerGate.valid_inputs (MaurerGate.Mul g) ws => MaurerMul.valid_inputs g ws.
  rewrite /valid_inputs /ISet.mem /ISet.iset => />H i j Hi Hj. have : (MaurerGate.consistent_inputs (MaurerGate.Mul g) i j ((MaurerGate.ST.P.get ws i)) ((MaurerGate.ST.P.get ws j))). rewrite H => />*. rewrite /consistent_inputs => />*. qed.

lemma mu1_gen_rand_add p d :
  mu1 ((MaurerWeakAdd.gen_rand p)) d =
  mu1 ((MaurerWeakGate.gen_rand (MaurerGate.Add p))) ((MaurerP.map L d)).
  rewrite /gen_rand /gate_rand => />*. rewrite dunit1E dmap1E => />*. rewrite /gen_rand /pinit => />*. rewrite dunitE /pred1 /(\o) => />*. congr. rewrite !MaurerP.tP => />*. rewrite eq_logical => />*. rewrite !MaurerP.get_map => />*. qed.

lemma unL_gen_rand_add c x :
  c \in (MaurerWeakGate.gen_rand (MaurerGate.Add x)) =>
  (MaurerP.map unL c) \in (MaurerWeakAdd.gen_rand x).
  rewrite /gen_rand => />H. move :H. rewrite !supp_dmap => />a H. move :H. rewrite /gen_rand => />H. move :H. rewrite !supp_dunit /pinit => />*. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. qed.

lemma gen_rand_add_unL c x :
  c \in (MaurerWeakGate.gen_rand (MaurerGate.Add x)) =>
  c = (MaurerP.map L ((MaurerP.map unL c))).
  rewrite /gen_rand /gate_rand => />H. rewrite supp_dmap in H => />*. move :H. progress. rewrite !MaurerP.map_comp /(\o) => />*. qed.

lemma L_gen_rand_add c p :
  c \in (MaurerWeakAdd.gen_rand p) =>
  (MaurerP.map L c) \in (MaurerWeakGate.gen_rand (MaurerGate.Add p)).
  rewrite /gen_rand /gate_rand => />*. rewrite supp_dmap => />*. exists c => />*. qed.

lemma valid_rands_add_L c p :
  c \in (MaurerWeakAdd.gen_rand p) =>
  (MaurerGate.valid_rands (MaurerGate.Add p) ((MaurerP.map L c))).
  rewrite /valid_rands => />H i j Hi Hj. rewrite !MaurerGate.ST.P.get_map => />*. move :Hi. rewrite /ISet.mem /ISet.iset iset_in_def => />*. move :Hj. rewrite /ISet.mem /ISet.iset iset_in_def => />*. qed.

lemma mu1_gen_rand_smul p d :
  mu1 ((MaurerWeakSMul.gen_rand p)) d =
  mu1 ((MaurerWeakGate.gen_rand (MaurerGate.SMul p))) ((MaurerP.map L d)).
  rewrite /gen_rand /gate_rand => />*. rewrite dunit1E dmap1E => />*. rewrite /gen_rand /pinit => />*. rewrite dunitE /pred1 /(\o) => />*. congr. rewrite !MaurerP.tP => />*. rewrite eq_logical => />*. rewrite !MaurerP.get_map => />*. qed.

lemma unL_gen_rand_smul c x :
  c \in (MaurerWeakGate.gen_rand (MaurerGate.SMul x)) =>
  (MaurerP.map unL c) \in (MaurerWeakSMul.gen_rand x).
  rewrite /gen_rand => />H. move :H. rewrite !supp_dmap => />a H. move :H. rewrite /gen_rand => />H. move :H. rewrite !supp_dunit /pinit => />*. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. qed.

lemma gen_rand_smul_unL c x :
  c \in (MaurerWeakGate.gen_rand (MaurerGate.SMul x)) =>
  c = (MaurerP.map L ((MaurerP.map unL c))).
  rewrite /gen_rand /gate_rand => />H. rewrite supp_dmap in H => />. move :H. progress. rewrite !MaurerP.map_comp /(\o) => />*. qed.

lemma L_gen_rand_smul c p :
  c \in (MaurerWeakSMul.gen_rand p) =>
  (MaurerP.map L c) \in (MaurerWeakGate.gen_rand (MaurerGate.SMul p)).
  rewrite /gen_rand /gate_rand => />*. rewrite supp_dmap => />*. exists c => />*. qed.

lemma valid_rands_smul_L c p :
  c \in (MaurerWeakSMul.gen_rand p) =>
  (MaurerGate.valid_rands (MaurerGate.SMul p) ((MaurerP.map L c))).
  rewrite /valid_rands => />H i j Hi Hj. rewrite !MaurerGate.ST.P.get_map => />*. move :Hi. rewrite /ISet.mem /ISet.iset iset_in_def => />*. move :Hj. rewrite /ISet.mem /ISet.iset iset_in_def => />*. qed.

lemma mu1_gen_rand_const p d :
  mu1 ((MaurerWeakConst.gen_rand p)) d =
  mu1 ((MaurerWeakGate.gen_rand (MaurerGate.Const p))) ((MaurerP.map L d)).
  rewrite /gen_rand /gate_rand => />*. rewrite dunit1E dmap1E => />*. rewrite /gen_rand /pinit => />*. rewrite dunitE /pred1 /(\o) => />*. congr. rewrite !MaurerP.tP => />*. rewrite eq_logical => />*. rewrite !MaurerP.get_map => />*. qed.

lemma unL_gen_rand_const c x :
  c \in (MaurerWeakGate.gen_rand (MaurerGate.Const x)) =>
  (MaurerP.map unL c) \in (MaurerWeakConst.gen_rand x).
  rewrite /gen_rand => />H. move :H. rewrite !supp_dmap => />a H. move :H. rewrite /gen_rand => />H. move :H. rewrite !supp_dunit /pinit => />*. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. qed.

lemma gen_rand_const_unL c x :
  c \in (MaurerWeakGate.gen_rand (MaurerGate.Const x)) =>
  c = (MaurerP.map L ((MaurerP.map unL c))).
  rewrite /gen_rand /gate_rand => />H. rewrite supp_dmap in H => />*. move :H. progress. rewrite !MaurerP.map_comp /(\o) => />*. qed.

lemma L_gen_rand_const c p :
  c \in (MaurerWeakConst.gen_rand p) =>
  (MaurerP.map L c) \in (MaurerWeakGate.gen_rand (MaurerGate.Const p)).
  rewrite /gen_rand /gate_rand => />*. rewrite supp_dmap => />*. exists c => />*. qed.

lemma valid_rands_const_L c p :
  c \in (MaurerWeakConst.gen_rand p) =>
  (MaurerGate.valid_rands (MaurerGate.Const p) ((MaurerP.map L c))).
  rewrite /valid_rands => />H i j Hi Hj. rewrite !MaurerGate.ST.P.get_map => />*. move :Hi. rewrite /ISet.mem /ISet.iset iset_in_def => />*. move :Hj. rewrite /ISet.mem /ISet.iset iset_in_def => />*. qed.

lemma map_R_congr (xs ys:'b MaurerP.arrayN) :
  (MaurerP.map R<:'a,'b> xs = MaurerP.map R ys) = (xs=ys).
  rewrite eq_logical => />H. move :H. rewrite !MaurerP.tP => />H i Hi1 Hi2. have : (MaurerP.get ((MaurerP.map R<:'a,'b> xs)) i) = (MaurerP.get ((MaurerP.map R ys)) i). rewrite H => />*. clear H. rewrite !MaurerP.get_map => />*. qed.

lemma replicate_5 (x:'a) :
  replicate 5 x = [x;x;x;x;x].
  rewrite (_:5=4+1). algebra. rewrite replicate_succ => />. 
  rewrite (_:4=3+1). algebra. rewrite replicate_succ => />. 
  rewrite (_:3=2+1). algebra. rewrite replicate_succ => />. 
  rewrite (_:2=1+1). algebra. rewrite replicate_succ => />. 
  rewrite (_:1=0+1). algebra. rewrite replicate_succ => />. 
  rewrite replicate0 => />. qed.

lemma mu1_gen_rand_mul p d :
  mu1 ((MaurerWeakMul.gen_rand p)) d = mu1 ((MaurerWeakGate.gen_rand (MaurerGate.Mul p))) ((MaurerP.map R d)).
  rewrite /gen_rand => />*. rewrite !dmap1E /gen_rand /gen_parties_rand => />*. rewrite !dmapE !dlist_djoin !replicate_5 => />. rewrite !djoinE => />*. rewrite !dmapE /gen_party_rand /pred1 /(\o) => />*. 
  rewrite (_: (fun (x:_*_) => (MaurerP.map R<:unit,t Array9.t> ((MaurerP.of_list (cons x.`1 x.`2)))) = (MaurerP.map R d)) = (fun (x:_*_) => (fun x1 => x1 = MaurerP.get d 0) x.`1 /\ (fun x2 => (forall (i:int), 0 <= i < MaurerP.size - 1 => nth witness x2 i = MaurerP.get d (i+1))) x.`2 )). rewrite fun_ext => />*. rewrite map_R_congr => />*. rewrite MaurerP.eq_of_list_cons_l => />*. rewrite dprodE => />*. rewrite !dmapE /(\o) => />*. 
  rewrite (_: (fun (x:_*_) => forall (i:int), 0 <= i && i < MaurerP.size - 1 => (if i = 0 then x.`1 else nth witness x.`2 (i - 1)) = (MaurerP.get d (i + 1))) = (fun (x:_*_)=> (fun x1 => x1 = MaurerP.get d 1) x.`1 /\ (fun x2 => (forall i, 1 <= i < MaurerP.size - 1 => nth witness x2 (i-1) = MaurerP.get d (i+1)) ) x.`2) ). rewrite fun_ext => />x. rewrite eq_logical => />*. progress. have : (if 0 = 0 then x.`1 else nth witness x.`2 (0 - 1)) = (MaurerP.get d (0 + 1)). rewrite H => />*. progress. have : (if i = 0 then x.`1 else nth witness x.`2 (i - 1)) = (MaurerP.get d (i + 1)). rewrite H => />*. smt(). have : !i=0. smt(). progress. move :H3. rewrite H2 => />*. case (i=0) => />*. rewrite H0 => />*. smt(). rewrite dprodE => />*. rewrite !dmapE /(\o) => />*. 
  rewrite (_: (fun (x :_*_) => forall (i : int), 1 <= i && i < MaurerP.size - 1 => (if i - 1 = 0 then x.`1 else nth witness x.`2 (i - 2)) = (MaurerP.get d (i + 1))) = (fun (x:_*_) => (fun x1 => x1 = MaurerP.get d 2) x.`1 /\ (fun x2 => (forall i, 2 <= i < MaurerP.size - 1 => nth witness x2 (i-2) = MaurerP.get d (i+1) )) x.`2) ). rewrite fun_ext => />x. rewrite eq_logical => />*. progress. smt(). have : (if i - 1 = 0 then x.`1 else nth witness x.`2 (i - 2)) = (MaurerP.get d (i + 1)). rewrite H => />*. smt(). have : ! i-1=0. smt(). progress. move :H3. rewrite H2 => />*. case (i-1=0) => />*. smt(). rewrite H0 => />*. smt(). rewrite dprodE !dmapE /(\o) => />*. 
  rewrite (_: (fun (x : _*_) => forall (i : int), 2 <= i && i < MaurerP.size - 1 => (if i - 2 = 0 then x.`1 else nth witness x.`2 (i - 3)) = (MaurerP.get d (i + 1))) = (fun (x:_*_) => (fun x1 => x1 = MaurerP.get d 3) x.`1 /\ (fun x2 => (forall i, 3 <= i < MaurerP.size - 1 => nth witness x2 (i-3) = MaurerP.get d (i+1) ) ) x.`2 ) ). rewrite fun_ext => />x. rewrite eq_logical => />*. progress. smt(). have : (if i - 2 = 0 then x.`1 else nth witness x.`2 (i - 3)) = (MaurerP.get d (i + 1)). rewrite H => />*. smt(). have : !i-2=0. smt(). progress. move :H3. rewrite H2 => />*. case (i-2=0) => />*. smt(). rewrite H0 => />*. smt(). rewrite dprodE !dmapE /(\o) => />*. 
  rewrite (_: (fun (x :_*_) => forall (i : int), 3 <= i && i < MaurerP.size - 1 => (if i - 3 = 0 then x.`1 else nth witness x.`2 (i - 4)) = (MaurerP.get d (i + 1))) = (fun (x:_*_) => (fun x1 => x1 = MaurerP.get d 4) x.`1 /\ (fun x2 => (forall i, 4 <= i < MaurerP.size - 1 => nth witness x2 (i-4) = MaurerP.get d (i+1) ) ) x.`2 ) ). rewrite fun_ext => />x. rewrite eq_logical => />*. progress. smt(). have : (if i - 3 = 0 then x.`1 else nth witness x.`2 (i - 4)) = (MaurerP.get d (i + 1)). rewrite H => />*. smt(). have : !i-3=0. smt(). progress. move :H3. rewrite H2 => />*. case (i-3=0) => />*. smt(). rewrite H0 => />*. smt(). rewrite dprodE !dmapE /(\o) => />*. rewrite dunitE => />*. 
  rewrite (_: (fun (x:_*_) => (MaurerP.of_list (cons x.`1 x.`2)) = d) = (fun (x:_*_) => (fun x1 => x1 = MaurerP.get d 0 ) x.`1 /\ (fun x2 => (forall i, 0 <= i < MaurerP.size-1 => nth witness x2 i = MaurerP.get d (i+1)) ) x.`2 )). rewrite fun_ext => />*. rewrite MaurerP.eq_of_list_cons_l => />*. rewrite dprodE !dmapE /(\o) => />*. congr. 
  rewrite (_: (fun (x :_*_) => forall (i : int), 0 <= i && i < MaurerP.size - 1 => (if i = 0 then x.`1 else nth witness x.`2 (i - 1)) = (MaurerP.get d (i + 1))) = (fun (x:_*_) => (fun x1 => x1 = MaurerP.get d 1 ) x.`1 /\ (fun x2 => (forall i, 1 <= i < MaurerP.size - 1 => nth witness x2 (i-1) = MaurerP.get d (i+1) ) ) x.`2 ) ). rewrite fun_ext => />x. rewrite eq_logical => />*. progress. smt(). have : (if i = 0 then x.`1 else nth witness x.`2 (i - 1)) = (MaurerP.get d (i + 1)). rewrite H => />*. smt(). have : !i=0. smt(). progress. move :H3. rewrite H2 => />*. case (i=0) => />*. rewrite H0 => />*. smt(). rewrite dprodE !dmapE /(\o) => />*. congr. 
  rewrite (_: (fun (x :_*_) => forall (i : int), 1 <= i && i < MaurerP.size - 1 => (if i - 1 = 0 then x.`1 else nth witness x.`2 (i - 2)) = (MaurerP.get d (i + 1))) = (fun (x:_*_) => (fun x1 => x1 = MaurerP.get d 2 ) x.`1 /\ (fun x2 => (forall i, 2 <= i < MaurerP.size - 1 => nth witness x2 (i-2) = MaurerP.get d (i+1) ) ) x.`2 ) ). rewrite fun_ext => />x. rewrite eq_logical => />*. progress. have : (if 1 - 1 = 0 then x.`1 else nth witness x.`2 (1 - 2)) = (MaurerP.get d (1 + 1)). rewrite H => />*. progress. have : (if i - 1 = 0 then x.`1 else nth witness x.`2 (i - 2)) = (MaurerP.get d (i + 1)). rewrite H => />*. smt(). have : !(i-1=0). smt(). progress. move :H3. rewrite H2 => />*. case (i-1=0) => />*. smt(). rewrite H0 => />*. smt(). rewrite dprodE !dmapE /(\o) => />*. congr. 
  rewrite (_: (fun (x :_*_) => forall (i : int), 2 <= i && i < MaurerP.size - 1 => (if i - 2 = 0 then x.`1 else nth witness x.`2 (i - 3)) = (MaurerP.get d (i + 1))) = (fun (x:_*_) => (fun x1 => x1 = MaurerP.get d 3) x.`1 /\ (fun x2 => (forall i, 3 <= i < MaurerP.size-1 => nth witness x2 (i-3) = MaurerP.get d (i+1) )) x.`2 ) ). rewrite fun_ext => />x. rewrite eq_logical => />*. progress. smt(). have : (if i - 2 = 0 then x.`1 else nth witness x.`2 (i - 3)) = (MaurerP.get d (i + 1)). rewrite H => />*. smt(). have : !(i-2=0). smt(). progress. move :H3. rewrite H2 => />*. case (i-2=0) => />*. smt(). rewrite H0 => />*. smt(). rewrite dprodE !dmapE /(\o) => />*. congr. 
  rewrite (_: (fun (x :_*_) => forall (i : int), 3 <= i && i < MaurerP.size - 1 => (if i - 3 = 0 then x.`1 else nth witness x.`2 (i - 4)) = (MaurerP.get d (i + 1))) = (fun (x:_*_) => (fun x1 => x1 = MaurerP.get d 4) x.`1 /\ (fun x2 => forall i, 4 <= i < MaurerP.size - 1 => nth witness x2 (i-4) = MaurerP.get d (i+1) ) x.`2 ) ). rewrite fun_ext => />x. rewrite eq_logical => />*. progress. smt(). have : (if i - 3 = 0 then x.`1 else nth witness x.`2 (i - 4)) = (MaurerP.get d (i + 1)). rewrite H => />*. smt(). have : !(i-3=0). smt(). progress. move :H3. rewrite H2 => />*. case (i-3=0) => />*. smt(). rewrite H0 => />*. smt(). rewrite dprodE !dmapE /(\o) => />*. congr. rewrite dunitE => />*. qed.
  
lemma unR_gen_rand_mul c x :
  c \in (MaurerWeakGate.gen_rand (MaurerGate.Mul x)) =>
  (MaurerP.map unR c) \in (MaurerWeakMul.gen_rand x).
  rewrite /gen_rand => />H. move :H. rewrite !supp_dmap => />a H. move :H. rewrite /gen_rand => />H. rewrite supp_dmap in H => />*. move :H. progress. exists a0 => />*. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. qed.

lemma gen_rand_mul_unR c x :
  c \in (MaurerWeakGate.gen_rand (MaurerGate.Mul x)) =>
  c = (MaurerP.map R ((MaurerP.map unR c))).
  rewrite /gen_rand /gate_rand => />H. rewrite supp_dmap in H => />*. move :H. progress. rewrite !MaurerP.map_comp /(\o) => />*. qed.

lemma R_gen_rand_mul c p :
  c \in (MaurerWeakMul.gen_rand p) =>
  (MaurerP.map R c) \in (MaurerWeakGate.gen_rand (MaurerGate.Mul p)).
  rewrite /gen_rand /gate_rand => />*. rewrite supp_dmap => />*. exists c => />*. qed.

lemma valid_rands_mul_R c p :
  c \in (MaurerWeakMul.gen_rand p) =>
  (MaurerGate.valid_rands (MaurerGate.Mul p) ((MaurerP.map R c))).
  rewrite /valid_rands => />H i j Hi Hj. rewrite /get !MaurerP.get_map => />*. move :Hi. rewrite /ISet.mem /ISet.iset iset_in_def => />*. move :Hj. rewrite /ISet.mem /ISet.iset iset_in_def => />*. qed.

theory MaurerWeakGateProofs.

  clone include WeakGateProofs with
    theory WG = MaurerWeakGate
    proof *.
    realize valid_gen_rand.
    progress. rewrite /MaurerGate.valid_rands => />i j Hij. move :H. case x => />g H.
    move :H. rewrite /gen_rand /gate_rand. simplify. rewrite supp_dmap => />a H. rewrite /get !MaurerP.get_map => />*. move :Hij. rewrite /ISet.mem /ISet.iset !iset_in_def => />*. move :Hij. rewrite /ISet.mem /ISet.iset !iset_in_def => />*. 
    move :H. rewrite /gen_rand /gate_rand. simplify. rewrite supp_dmap => />a H. rewrite /get !MaurerP.get_map => />*. move :Hij. rewrite /ISet.mem /ISet.iset !iset_in_def => />*. move :Hij. rewrite /ISet.mem /ISet.iset !iset_in_def => />*. 
    move :H. rewrite /gen_rand /gate_rand. simplify. rewrite supp_dmap => />a H. rewrite /get !MaurerP.get_map => />*. move :Hij. rewrite /ISet.mem /ISet.iset !iset_in_def => />*. move :Hij. rewrite /ISet.mem /ISet.iset !iset_in_def => />*. 
    move :H. rewrite /gen_rand /gate_rand. simplify. rewrite supp_dmap => />a H. rewrite /get !MaurerP.get_map => />*. move :Hij. rewrite /ISet.mem /ISet.iset !iset_in_def => />*. move :Hij. rewrite /ISet.mem /ISet.iset !iset_in_def => />*. qed.
    realize dom_simulator.
    move => i x ws r. case x => />g. 
    rewrite /simulator => />*. rewrite fdom_map => />*. rewrite MaurerWeakAddProofs.dom_simulator => />*. 
    rewrite /simulator => />*. rewrite fdom_map => />*. rewrite MaurerWeakSMulProofs.dom_simulator => />*. 
    rewrite /simulator => />*. rewrite fdom_map => />*. rewrite MaurerWeakConstProofs.dom_simulator => />*. 
    rewrite /simulator => />*. rewrite fdom_map => />*. rewrite MaurerWeakMulProofs.dom_simulator => />*. qed.
    realize gen_rand_ll.
    move => p. case p => />g.
    rewrite /gen_rand /gate_rand => />*. rewrite dmap_ll => />*. rewrite MaurerWeakAddProofs.gen_rand_ll => />*.
    rewrite /gen_rand /gate_rand => />*. rewrite dmap_ll => />*. rewrite MaurerWeakSMulProofs.gen_rand_ll => />*.
    rewrite /gen_rand /gate_rand => />*. rewrite dmap_ll => />*. rewrite MaurerWeakConstProofs.gen_rand_ll => />*.
    rewrite /gen_rand /gate_rand => />*. rewrite dmap_ll => />*. rewrite MaurerWeakMulProofs.gen_rand_ll => />*. qed.
    realize weak_correctness.
    progress. rewrite (_:W.P.protocol = MaurerGate.protocol). progress. rewrite gate_protocol_def /functionality => />*. move :H H0. case x => />g H1 H2. 
    rewrite (_: MaurerWeakAdd.functionality g (W.unshare_input ys) = MaurerWeakAddProofs.W.functionality g (MaurerWeakAddProofs.W.unshare_input ys)). progress. rewrite (MaurerWeakAddProofs.weak_correctness g ys (MaurerP.map unL cs)) => />*. rewrite (_: MaurerWeakAddProofs.W.P.protocol = MaurerWeakAddProofs.WG.G.protocol ). progress. rewrite MaurerWeakAddProofs.g_protocol_def => />*. 
    rewrite (_: MaurerWeakSMul.functionality g (W.unshare_input ys) = MaurerWeakSMulProofs.W.functionality g (MaurerWeakSMulProofs.W.unshare_input ys)). progress. rewrite (MaurerWeakSMulProofs.weak_correctness g ys (MaurerP.map unL cs)) => />*. rewrite (_: MaurerWeakSMulProofs.W.P.protocol = MaurerWeakSMulProofs.WG.G.protocol ). progress. rewrite MaurerWeakSMulProofs.g_protocol_def => />*.  
    rewrite (_: MaurerWeakConst.functionality g (W.unshare_input ys) = MaurerWeakConstProofs.W.functionality g (MaurerWeakConstProofs.W.unshare_input ys)). progress. rewrite (MaurerWeakConstProofs.weak_correctness g ys (MaurerP.map unL cs)) => />*. rewrite (_: MaurerWeakConstProofs.W.P.protocol = MaurerWeakConstProofs.WG.G.protocol ). progress. rewrite MaurerWeakConstProofs.g_protocol_def => />*.  
    rewrite (_: MaurerWeakMul.functionality g (W.unshare_input ys) = MaurerWeakMulProofs.W.functionality g (MaurerWeakMulProofs.W.unshare_input ys)). progress. rewrite (MaurerWeakMulProofs.weak_correctness g ys (MaurerP.map unR cs)) => />*. rewrite (_: MaurerWeakMulProofs.W.P.protocol = MaurerWeakMulProofs.WG.G.protocol ). progress. rewrite MaurerWeakMulProofs.g_protocol_def => />*. qed.
    realize weak_privacy.
    exists* p{1}. elim*. move => f. case f => />G. 
    (*Add*)
    proc. sp. simplify. 
    alias{1} 1 t = 0. swap{1} 1 1. alias{1} 2 vi = MaurerWeakAdd.simulator i G yi (MaurerP.map unL cs).
    alias{2} 1 t = 0. swap{2} 1 1. alias{2} 2 vi = MaurerWeakAdd.corrupted i (MaurerWeakAdd.P.protocol G ys (MaurerP.map unL cs)).`1.
    transitivity{1}
      { vi <@ MaurerWeakAddProofs.WeakPrivacy.ideal(i,G,ys); }
      ( ={i,p,ys} /\ p{1}=MaurerGate.Add G /\ yi{1} = (MaurerWeakGate.corrupted i{1} ys{1}) ==> ={vi,i,p,ys} /\ p{1}=MaurerGate.Add G /\ yi{1} = (MaurerWeakGate.corrupted i{1} ys{1}) /\ vi{1}=MaurerWeakAdd.simulator i{1} G yi{1} (MaurerP.map unL cs{1}) )
      ( ={i, p, ys} /\ p{1}=MaurerGate.Add G /\ (MaurerWeakAdd.corrupted_set i{1}) /\ (MaurerAdd.valid_inputs G ys{1}) ==> ={vi,i,p,ys} /\ p{1}=MaurerGate.Add G /\ vi{2}=MaurerWeakAdd.corrupted i{2} (MaurerWeakAdd.P.protocol G ys{2} (MaurerP.map unL cs{2})).`1 /\ (MaurerGate.valid_rands (MaurerGate.Add G) cs{2}) /\ MaurerWeakAdd.corrupted_set i{1} ).
    progress. exists i{2} (MaurerGate.Add G) ys{2} => |>*. 
    progress. rewrite (_:W.P.protocol=MaurerGate.protocol). progress. rewrite gate_protocol_def => />. move :H1. rewrite /corrupted_set => />H1 H2. rewrite /corrupted /simulator => />*. rewrite -fmap_eqIn => />*. rewrite !fdom_map !fdom_ofset => />*. split. rewrite H /corrupted fdom_ofset => />. move => j. rewrite MaurerWeakAddProofs.dom_simulator => />Hi. rewrite map_some => />*. rewrite -!mem_fdom !MaurerWeakAddProofs.dom_simulator => />*. rewrite ofset_some => />*. rewrite !H => />. rewrite /corrupted => />*. rewrite !ofset_some /get => />. rewrite eq3 => />. rewrite (_:MaurerWeakAdd.P.protocol = MaurerWeakAddProofs.WG.G.protocol). progress. rewrite MaurerWeakAddProofs.g_protocol_def => />. have : 0 <= j < MaurerP.size. have : j \in MaurerWeakAdd.P.ST.partyset. rewrite (in_subset i{2}) => />*. rewrite /ISet.iset iset_in_def => />. move => ip. rewrite !MaurerP.get_map => />. 
    inline *. wp. sp. rnd (MaurerP.map unL) (MaurerP.map L) => />. move => &1 &2 H H0. move:H H0. progress. move :H0. rewrite H H1 => />*. rewrite MaurerP.map_comp /(\o) => />*. rewrite MaurerP.map_id => />*. rewrite mu1_gen_rand_add => />*. rewrite unL_gen_rand_add => />*. rewrite (gen_rand_add_unL _ p0{2}) => />*. rewrite !MaurerP.map_comp /(\o) => />*. auto => />*. progress. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite mu1_gen_rand_add => />*. rewrite unL_gen_rand_add => />*. rewrite -(gen_rand_add_unL _ G) => />. 
    transitivity{2}
      { vi <@ MaurerWeakAddProofs.WeakPrivacy.real(i,G,ys); }
      ( ={i, p, ys} /\ p{1} = MaurerGate.Add G /\ (MaurerWeakAdd.corrupted_set i{1}) /\ (MaurerAdd.valid_inputs G ys{1}) ==> ={vi, i, p, ys} /\ p{1} = MaurerGate.Add G /\ (MaurerWeakAdd.corrupted_set i{1}) )
      ( ={i, p, ys} /\ p{1} = MaurerGate.Add G /\ (MaurerWeakAdd.corrupted_set i{1}) /\ (MaurerAdd.valid_inputs G ys{1}) ==> ={vi,i,p,ys} /\ p{1} = MaurerGate.Add G /\ vi{2} = (MaurerWeakAdd.corrupted i{2} ((MaurerAdd.protocol G ys{2} ((MaurerP.map unL cs{2})))).`1) /\ (MaurerGate.valid_rands (MaurerGate.Add G) cs{2}) ).
    progress. exists i{2} (MaurerGate.Add G) ys{2} => />*. 
    progress. 
    call MaurerWeakAddProofs.weak_privacy => />*. trivial.
    inline *. wp. sp. simplify. rnd (MaurerP.map L) (MaurerP.map unL) => />. move => &1 &2 H H0. move :H H0. progress. rewrite mu1_gen_rand_add => />*. congr. rewrite /gen_rand => />. congr. rewrite (gen_rand_add_unL _ p0{1}) => />*. rewrite !MaurerP.map_comp /(\o) => />*. rewrite L_gen_rand_add => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite valid_rands_add_L => />*. auto => />*. progress. rewrite -(gen_rand_add_unL _ G) => />*. rewrite mu1_gen_rand_add => />*. congr. rewrite /gen_rand => />. congr. rewrite -(gen_rand_add_unL _ G) => />*. rewrite L_gen_rand_add => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite valid_rands_add_L => />*. 
    (*SMul*)
    proc. sp. simplify. 
    alias{1} 1 t = 0. swap{1} 1 1. alias{1} 2 vi = MaurerWeakSMul.simulator i G yi (MaurerP.map unL cs).
    alias{2} 1 t = 0. swap{2} 1 1. alias{2} 2 vi = MaurerWeakSMul.corrupted i (MaurerSMul.protocol G ys (MaurerP.map unL cs)).`1.
    transitivity{1}
      { vi <@ MaurerWeakSMulProofs.WeakPrivacy.ideal(i,G,ys); }
      ( ={i,p,ys} /\ p{1}=MaurerGate.SMul G /\ yi{1} = (MaurerWeakGate.corrupted i{1} ys{1}) ==> ={vi,i,p,ys} /\ p{1}=MaurerGate.SMul G /\ yi{1} = (MaurerWeakGate.corrupted i{1} ys{1}) /\ vi{1}=MaurerWeakSMul.simulator i{1} G yi{1} (MaurerP.map unL cs{1}) )
      ( ={i, p, ys} /\ p{1}=MaurerGate.SMul G /\ (MaurerWeakSMul.corrupted_set i{1}) /\ (MaurerSMul.valid_inputs G ys{1}) ==> ={vi,i,p,ys} /\ p{1}=MaurerGate.SMul G /\ vi{2}=MaurerWeakSMul.corrupted i{2} (MaurerSMul.protocol G ys{2} (MaurerP.map unL cs{2})).`1 /\ (MaurerGate.valid_rands (MaurerGate.SMul G) cs{2}) /\ MaurerWeakSMul.corrupted_set i{1} ).
    progress. exists i{2} (MaurerGate.SMul G) ys{2} => |>*. 
    progress. rewrite (_:W.P.protocol=MaurerGate.protocol). progress. rewrite gate_protocol_def => />. move :H1. rewrite /corrupted_set => />H1 H2. rewrite /corrupted /simulator => />*. rewrite -fmap_eqIn => />*. rewrite !fdom_map !fdom_ofset => />*. split. rewrite H /corrupted fdom_ofset => />. move => j. rewrite MaurerWeakSMulProofs.dom_simulator => />Hi. rewrite map_some => />*. rewrite -!mem_fdom !MaurerWeakSMulProofs.dom_simulator => />*. rewrite ofset_some => />*. rewrite !H => />. rewrite /corrupted => />*. rewrite !ofset_some /get => />. rewrite eq3 => />. rewrite (_:MaurerSMul.protocol = MaurerWeakSMulProofs.WG.G.protocol). progress. rewrite MaurerWeakSMulProofs.g_protocol_def => />. have : 0 <= j < MaurerP.size. have : j \in MaurerWeakSMul.P.ST.partyset. rewrite (in_subset i{2}) => />*. rewrite /ISet.iset iset_in_def => />. move => ip. rewrite !MaurerP.get_map => />. 
    inline *. wp. sp. rnd (MaurerP.map unL) (MaurerP.map L) => />. move => &1 &2 H H0. move:H H0. progress. move :H0. rewrite H H1 => />*. rewrite MaurerP.map_comp /(\o) => />*. rewrite MaurerP.map_id => />*. rewrite mu1_gen_rand_smul => />*. rewrite unL_gen_rand_add => />*. rewrite (gen_rand_smul_unL _ p0{2}) => />*. rewrite !MaurerP.map_comp /(\o) => />*. auto => />*. progress. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite mu1_gen_rand_smul => />*. rewrite unL_gen_rand_smul => />*. rewrite -(gen_rand_smul_unL _ G) => />*. 
    transitivity{2}
      { vi <@ MaurerWeakSMulProofs.WeakPrivacy.real(i,G,ys); }
      ( ={i, p, ys} /\ p{1} = MaurerGate.SMul G /\ (MaurerWeakSMul.corrupted_set i{1}) /\ (MaurerSMul.valid_inputs G ys{1}) ==> ={vi, i, p, ys} /\ p{1} = MaurerGate.SMul G /\ (MaurerWeakSMul.corrupted_set i{1}) )
      ( ={i, p, ys} /\ p{1} = MaurerGate.SMul G /\ (MaurerWeakSMul.corrupted_set i{1}) /\ (MaurerSMul.valid_inputs G ys{1}) ==> ={vi,i,p,ys} /\ p{1} = MaurerGate.SMul G /\ vi{2} = (MaurerWeakSMul.corrupted i{2} ((MaurerSMul.protocol G ys{2} ((MaurerP.map unL cs{2})))).`1) /\ (MaurerGate.valid_rands (MaurerGate.SMul G) cs{2}) ).
    progress. exists i{2} (MaurerGate.SMul G) ys{2} => />*. 
    progress. 
    call MaurerWeakSMulProofs.weak_privacy => />*. trivial.
    inline *. wp. sp. simplify. rnd (MaurerP.map L) (MaurerP.map unL) => />. move => &1 &2 H H0. move :H H0. progress. rewrite mu1_gen_rand_smul => />*. congr. rewrite /gen_rand => />. congr. rewrite (gen_rand_smul_unL _ p0{1}) => />*. rewrite !MaurerP.map_comp /(\o) => />*. rewrite L_gen_rand_smul => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite valid_rands_smul_L => />*. auto => />*. progress. rewrite -(gen_rand_smul_unL _ G) => />*. rewrite mu1_gen_rand_smul => />*. congr. rewrite /gen_rand => />. congr. rewrite -(gen_rand_smul_unL _ G) => />*. rewrite L_gen_rand_smul => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite valid_rands_smul_L => />*. 
    (*Const*)
    proc. sp. simplify. 
    alias{1} 1 t = 0. swap{1} 1 1. alias{1} 2 vi = MaurerWeakConst.simulator i G yi (MaurerP.map unL cs).
    alias{2} 1 t = 0. swap{2} 1 1. alias{2} 2 vi = MaurerWeakConst.corrupted i (MaurerConst.protocol G ys (MaurerP.map unL cs)).`1.
    transitivity{1}
      { vi <@ MaurerWeakConstProofs.WeakPrivacy.ideal(i,G,ys); }
      ( ={i,p,ys} /\ p{1}=MaurerGate.Const G /\ yi{1} = (MaurerWeakGate.corrupted i{1} ys{1}) ==> ={vi,i,p,ys} /\ p{1}=MaurerGate.Const G /\ yi{1} = (MaurerWeakGate.corrupted i{1} ys{1}) /\ vi{1}=MaurerWeakConst.simulator i{1} G yi{1} (MaurerP.map unL cs{1}) )
      ( ={i, p, ys} /\ p{1}=MaurerGate.Const G /\ (MaurerWeakConst.corrupted_set i{1}) /\ (MaurerConst.valid_inputs G ys{1}) ==> ={vi,i,p,ys} /\ p{1}=MaurerGate.Const G /\ vi{2}=MaurerWeakConst.corrupted i{2} (MaurerConst.protocol G ys{2} (MaurerP.map unL cs{2})).`1 /\ (MaurerGate.valid_rands (MaurerGate.Const G) cs{2}) /\ MaurerWeakConst.corrupted_set i{1} ).
    progress. exists i{2} (MaurerGate.Const G) ys{2} => |>*. 
    progress. rewrite (_:W.P.protocol=MaurerGate.protocol). progress. rewrite gate_protocol_def => />. move :H1. rewrite /corrupted_set => />H1 H2. rewrite /corrupted /simulator => />*. rewrite -fmap_eqIn => />*. rewrite !fdom_map !fdom_ofset => />*. split. rewrite H /corrupted fdom_ofset => />. move => j. rewrite MaurerWeakConstProofs.dom_simulator => />Hi. rewrite map_some => />*. rewrite -!mem_fdom !MaurerWeakConstProofs.dom_simulator => />*. rewrite ofset_some => />*. rewrite !H => />. rewrite /corrupted => />*. rewrite !ofset_some /get => />. rewrite eq3 => />. rewrite (_:MaurerConst.protocol = MaurerWeakConstProofs.WG.G.protocol). progress. rewrite MaurerWeakConstProofs.g_protocol_def => />. have : 0 <= j < MaurerP.size. have : j \in MaurerWeakConst.P.ST.partyset. rewrite (in_subset i{2}) => />*. rewrite /ISet.iset iset_in_def => />. move => ip. rewrite !MaurerP.get_map => />. 
    inline *. wp. sp. rnd (MaurerP.map unL) (MaurerP.map L) => />. move => &1 &2 H H0. move:H H0. progress. move :H0. rewrite H H1 => />*. rewrite MaurerP.map_comp /(\o) => />*. rewrite MaurerP.map_id => />*. rewrite mu1_gen_rand_const => />*. rewrite unL_gen_rand_const => />*. rewrite (gen_rand_const_unL _ p0{2}) => />*. rewrite !MaurerP.map_comp /(\o) => />*. auto => />*. progress. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite mu1_gen_rand_const => />*. rewrite unL_gen_rand_const => />*. rewrite -(gen_rand_const_unL _ G) => />*. 
    transitivity{2}
      { vi <@ MaurerWeakConstProofs.WeakPrivacy.real(i,G,ys); }
      ( ={i, p, ys} /\ p{1} = MaurerGate.Const G /\ (MaurerWeakConst.corrupted_set i{1}) /\ (MaurerConst.valid_inputs G ys{1}) ==> ={vi, i, p, ys} /\ p{1} = MaurerGate.Const G /\ (MaurerWeakConst.corrupted_set i{1}) )
      ( ={i, p, ys} /\ p{1} = MaurerGate.Const G /\ (MaurerWeakConst.corrupted_set i{1}) /\ (MaurerConst.valid_inputs G ys{1}) ==> ={vi,i,p,ys} /\ p{1} = MaurerGate.Const G /\ vi{2} = (MaurerWeakConst.corrupted i{2} ((MaurerConst.protocol G ys{2} ((MaurerP.map unL cs{2})))).`1) /\ (MaurerGate.valid_rands (MaurerGate.Const G) cs{2}) ).
    progress. exists i{2} (MaurerGate.Const G) ys{2} => />*. 
    progress. 
    call MaurerWeakConstProofs.weak_privacy => />*. trivial.
    inline *. wp. sp. simplify. rnd (MaurerP.map L) (MaurerP.map unL) => />. move => &1 &2 H H0. move :H H0. progress. rewrite mu1_gen_rand_const => />*. congr. rewrite /gen_rand => />. congr. rewrite (gen_rand_const_unL _ p0{1}) => />*. rewrite !MaurerP.map_comp /(\o) => />*. rewrite L_gen_rand_const => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite valid_rands_const_L => />*. auto => />*. progress. rewrite -(gen_rand_const_unL _ G) => />*. rewrite mu1_gen_rand_const => />*. congr. rewrite /gen_rand => />. congr. rewrite -(gen_rand_const_unL _ G) => />*. rewrite L_gen_rand_const => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite valid_rands_const_L => />*. 
    (*Mul*)
    proc. sp. simplify. 
    alias{1} 1 t = 0. swap{1} 1 1. alias{1} 2 vi = MaurerWeakMul.simulator i G yi (MaurerP.map unR cs).
    alias{2} 1 t = 0. swap{2} 1 1. alias{2} 2 vi = MaurerWeakMul.corrupted i (MaurerMul.protocol G ys (MaurerP.map unR cs)).`1.
    transitivity{1}
      { vi <@ MaurerWeakMulProofs.WeakPrivacy.ideal(i,G,ys); }
      ( ={i,p,ys} /\ p{1}=MaurerGate.Mul G /\ yi{1} = (MaurerWeakGate.corrupted i{1} ys{1}) ==> ={vi,i,p,ys} /\ p{1}=MaurerGate.Mul G /\ yi{1} = (MaurerWeakGate.corrupted i{1} ys{1}) /\ vi{1}=MaurerWeakMul.simulator i{1} G yi{1} (MaurerP.map unR cs{1}) )
      ( ={i, p, ys} /\ p{1}=MaurerGate.Mul G /\ (MaurerWeakMul.corrupted_set i{1}) /\ (MaurerMul.valid_inputs G ys{1}) ==> ={vi,i,p,ys} /\ p{1}=MaurerGate.Mul G /\ vi{2}=MaurerWeakMul.corrupted i{2} (MaurerMul.protocol G ys{2} (MaurerP.map unR cs{2})).`1 /\ (MaurerGate.valid_rands (MaurerGate.Mul G) cs{2}) /\ MaurerWeakMul.corrupted_set i{1} ).
    progress. exists i{2} (MaurerGate.Mul G) ys{2} => |>*. 
    progress. rewrite (_:W.P.protocol=MaurerGate.protocol). progress. rewrite gate_protocol_def => />. move :H1. rewrite /corrupted_set => />H1 H2. rewrite /corrupted /simulator => />*. rewrite -fmap_eqIn => />*. rewrite !fdom_map !fdom_ofset => />*. split. rewrite H /corrupted fdom_ofset => />. move => j. rewrite MaurerWeakMulProofs.dom_simulator => />Hi. rewrite map_some => />*. rewrite -!mem_fdom !MaurerWeakMulProofs.dom_simulator => />*. rewrite ofset_some => />*. rewrite !H => />. rewrite /corrupted => />*. rewrite !ofset_some /get => />. rewrite eq3 => />. rewrite (_:MaurerMul.protocol = MaurerWeakMulProofs.WG.G.protocol). progress. rewrite MaurerWeakMulProofs.g_protocol_def => />. have : 0 <= j < MaurerP.size. have : j \in MaurerWeakMul.P.ST.partyset. rewrite (in_subset i{2}) => />*. rewrite /ISet.iset iset_in_def => />. move => ip. rewrite !MaurerP.get_map => />. 
    inline *. wp. sp. rnd (MaurerP.map unR) (MaurerP.map R) => />. move => &1 &2 H H0. move:H H0. progress. move :H0. rewrite H H1 => />*. rewrite MaurerP.map_comp /(\o) => />*. rewrite MaurerP.map_id => />*. rewrite mu1_gen_rand_mul => />*. rewrite unR_gen_rand_mul => />*. rewrite (gen_rand_mul_unR _ p0{2}) => />*. rewrite !MaurerP.map_comp /(\o) => />*. auto => />*. progress. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite mu1_gen_rand_mul => />*. rewrite unR_gen_rand_mul => />*. rewrite -(gen_rand_mul_unR _ G) => />*. 
    transitivity{2}
      { vi <@ MaurerWeakMulProofs.WeakPrivacy.real(i,G,ys); }
      ( ={i, p, ys} /\ p{1} = MaurerGate.Mul G /\ (MaurerWeakMul.corrupted_set i{1}) /\ (MaurerMul.valid_inputs G ys{1}) ==> ={vi, i, p, ys} /\ p{1} = MaurerGate.Mul G /\ (MaurerWeakMul.corrupted_set i{1}) )
      ( ={i, p, ys} /\ p{1} = MaurerGate.Mul G /\ (MaurerWeakMul.corrupted_set i{1}) /\ (MaurerMul.valid_inputs G ys{1}) ==> ={vi,i,p,ys} /\ p{1} =MaurerGate.Mul G /\ vi{2} = (MaurerWeakMul.corrupted i{2} ((MaurerMul.protocol G ys{2} ((MaurerP.map unR cs{2})))).`1) /\ (MaurerGate.valid_rands (MaurerGate.Mul G) cs{2}) ).
    progress. exists i{2} (MaurerGate.Mul G) ys{2} => />*. 
    progress. 
    call MaurerWeakMulProofs.weak_privacy => />*. trivial.
    inline *. wp. sp. simplify. rnd (MaurerP.map R) (MaurerP.map unR) => />. move => &1 &2 H H0. move :H H0. progress. rewrite mu1_gen_rand_mul => />*. congr. rewrite /gen_rand => />. congr. rewrite (gen_rand_mul_unR _ p0{1}) => />*. rewrite !MaurerP.map_comp /(\o) => />*. rewrite R_gen_rand_mul => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite valid_rands_mul_R => />*. auto => />*. progress. rewrite -(gen_rand_mul_unR _ G) => />*. rewrite mu1_gen_rand_mul => />*. congr. rewrite /gen_rand => />. congr. rewrite -(gen_rand_mul_unR _ G) => />*. rewrite R_gen_rand_mul => />*. rewrite !MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite MaurerP.map_comp /(\o) MaurerP.map_id => />*. rewrite valid_rands_mul_R => />*. 
    qed.

end MaurerWeakGateProofs.

lemma get_gate_protocol_wire i g (ws:MaurerGate.ST.local_input MaurerP.arrayN) r :
  i \in MaurerCircuit.ST.partyset =>
    (MaurerP.get (MaurerWeakGateProofs.WG.G.protocol g ws r).`2 i).`1.`1 = (MaurerP.get ws i).`1.`1 + 1.
  rewrite MaurerWeakGateProofs.g_protocol_def /g_protocol => />H. 
  have : 0 <= i && i < MaurerP.size. move :H. rewrite iset_in_def => />*. move => irng.
  rewrite !MaurerP.get_imap => />*. rewrite !MaurerP.get_zip !irng /send_messages => />*. rewrite /gate_send_messages /local_gate_start /local_gate_end => />*. case g => />*.
  rewrite /local_gate_end /add => />*. rewrite (prod_id ((MaurerP.get ws i)).`1) => />*.
  rewrite /local_gate_end /smul => />*. rewrite (prod_id ((MaurerP.get ws i)).`1) => />*.
  rewrite /local_gate_end /cnst => />*. rewrite (prod_id ((MaurerP.get ws i)).`1) => />*.
  rewrite /local_gate_end /mul_end => />*. rewrite (prod_id ((MaurerP.get ws i)).`1) => />*. qed.

lemma get_g_protocol_pubs i (g) (ws:MaurerCircuit.ST.local_input MaurerP.arrayN) r :
  i \in MaurerCircuit.ST.partyset =>
  MaurerCircuit.g_wire g = (MaurerP.get ws i).`1.`1 =>
    (MaurerP.get (MaurerWeakGateProofs.WG.G.protocol g ws r).`2 i).`2 = MaurerCircuit.g_pubs g (MaurerP.get ws i).`2.
  rewrite MaurerWeakGateProofs.g_protocol_def /g_protocol => />H.
  have : 0 <= i && i < MaurerP.size. move :H. rewrite iset_in_def /parties => />*. progress.
  rewrite !MaurerP.get_imap => />*. rewrite !MaurerP.get_zip !andabP !andaP => />*. rewrite /local_gate_end /send_messages => />*. rewrite /gate_send_messages => />. move :H0 H2. case g => />G H2 H3. rewrite /local_gate_end /get_wire_st_next /ISet.union => />. rewrite H3 => />*. qed.

lemma consistent_shares_step i j g ws r :
  i \in MaurerCircuit.ST.partyset => j \in MaurerCircuit.ST.partyset =>
  MaurerGate.consistent_inputs g i j (MaurerP.get ws i) (MaurerP.get ws j) =>
    MaurerAPI.consistent_shares i j (MaurerP.get (MaurerWeakGateProofs.WG.G.protocol g ws r).`2 i) (MaurerP.get (MaurerWeakGateProofs.WG.G.protocol g ws r).`2 j).
  rewrite /consistent_inputs /consistent_shares /get_wire_st_next /get_wire_st_fdom /get_wire_st_shr => |>H H0 H1. rewrite !get_gate_protocol_wire => |>. rewrite !MaurerWeakGateProofs.g_protocol_def => |>*. rewrite /g_protocol /local_gate_end /send_messages => |>*.
  have : 0 <= i && i < MaurerP.size. move :H. rewrite iset_in_def /parties => />*. move => irng.
  have : 0 <= j && j < MaurerP.size. move :H0. rewrite iset_in_def /parties => />*. move => jrng.
  rewrite !MaurerP.get_imap => |>. rewrite !MaurerP.get_zip !jrng => |>*. rewrite /all all_iseqE !allP => |>*. rewrite !dom_gate_end => |>*. rewrite !fsetallP. move :H1. case g => |>G.
  (*add*)
  rewrite /consistent_inputs /consistent_shares /add_valid_share /g_valid_share /get_wire_st_fdom /get_wire_st_next /get_wire_st_shr /ISet.subset /ISet.iset /ISet.mem /ISet.all /local_gate_end /add fsetallP all_iseqE !irng !allP => |>. move => H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17. rewrite !H2 !H8 -!H4 -!H10 => />. split. move => k Hk. have : k \in fdom (MaurerP.get ws i).`1.`2. rewrite (in_subset (MaurerP.get ws i).`2) => |>. rewrite H2 iset_in_def => |>Hk1 Hk2. rewrite (prod_id ((MaurerP.get ws i)).`1) (prod_id ((MaurerP.get ws j)).`1) => |>. rewrite !get_setE => />. rewrite -!H13. case (k=((MaurerP.get ws i)).`1.`1) => |>. have : MaurerAPI.consistent_pub_shares i j (oget (MaurerP.get ws i).`1.`2.[k]) (oget (MaurerP.get ws j).`1.`2.[k]). rewrite H16 => />. rewrite /consistent_pub_shares => />. move => x Hx. rewrite (prod_id ((MaurerP.get ws i)).`1) (prod_id ((MaurerP.get ws j)).`1) => |>. rewrite !get_setE => |>. rewrite -!H13. case (x=(MaurerP.get ws i).`1.`1) => />. rewrite consistent_raw_shares_conv. rewrite consistent_raw_shares_add_shr => />*. rewrite -consistent_raw_shares_conv. rewrite H17 => />. move :H5. rewrite H2 => />. rewrite !iset_in_def in_iseq => />. rewrite -consistent_raw_shares_conv. rewrite H17 => />. move :H6. rewrite H2 => />. rewrite !iset_in_def in_iseq => />. move => H18. rewrite H17 => />. move :Hx. rewrite H4 !in_iseq => />. smt(). 
  (*smul*)
  rewrite /consistent_inputs /consistent_shares /smul_valid_share /add_valid_share /g_valid_share /get_wire_st_fdom /get_wire_st_next /get_wire_st_shr /ISet.subset /ISet.iset /ISet.mem /ISet.all /local_gate_end /smul fsetallP all_iseqE !irng !allP => |>. move => H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19. rewrite (prod_id ((MaurerP.get ws i)).`1) (prod_id ((MaurerP.get ws j)).`1) => |>. rewrite -!H15 -!H16 => |>. split. move => k Hk. rewrite !get_set_neqE => />. have : k \in fdom (MaurerP.get ws i).`1.`2. rewrite (in_subset (MaurerP.get ws i).`2) => />. rewrite H2 iset_in_def => />. smt(). have : k \in fdom (MaurerP.get ws i).`1.`2. rewrite (in_subset (MaurerP.get ws i).`2) => />. rewrite H2 iset_in_def => />. smt().  have : MaurerAPI.consistent_pub_shares i j (oget (MaurerP.get ws i).`1.`2.[k]) (oget (MaurerP.get ws j).`1.`2.[k]). rewrite H18 => />. rewrite /consistent_pub_shares => />. move => x Hx. rewrite !get_setE => |>. case (x=(MaurerP.get ws i).`1.`1) => />. rewrite consistent_raw_shares_conv. rewrite consistent_raw_shares_smul => />*. have : MaurerAPI.consistent_pub_shares i j (oget (MaurerP.get ws i).`1.`2.[nth2_3 G]) (oget (MaurerP.get ws j).`1.`2.[nth2_3 G]). rewrite H18 => />. rewrite /consistent_pub_share /party_unpshare => />. rewrite -consistent_raw_shares_conv. rewrite H19 => />. move :H12. rewrite -H16 H2 iset_in_def in_iseq => />. move => H20. rewrite H19 => />. move :Hx. rewrite !in_iseq => />. smt(). 
  (*const*)
  rewrite /consistent_inputs /consistent_shares /const_valid_share /add_valid_share /g_valid_share /get_wire_st_fdom /get_wire_st_next /get_wire_st_shr /ISet.subset /ISet.iset /ISet.mem /ISet.all /local_gate_end /cnst fsetallP all_iseqE !irng !allP => |>. move => H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. rewrite (prod_id ((MaurerP.get ws i)).`1) (prod_id ((MaurerP.get ws j)).`1) => |>. rewrite -!H9 -!H10 /ISet.union /get_wire_st_next -H11 => |>. split. move => k Hk. rewrite !get_setE => |>. case (k = (MaurerP.get ws i).`1.`1) => |>. rewrite consistent_pub_shares_pshare => />. move => H14. rewrite H12 => />. move :Hk. rewrite in_fsetU in_fset1 H14 => />. move => x Hx. rewrite !get_setE => |>. case (x=(MaurerP.get ws i).`1.`1) => />. rewrite consistent_raw_shares_conv consistent_raw_shares_pshare => />*. move :H. rewrite iset_in_def => />. move :H0. rewrite iset_in_def => />. move => H14. rewrite H13 => />. move :Hx. rewrite !in_iseq => />. smt(). 
  (*mul*)
  rewrite /consistent_inputs /consistent_shares /mul_valid_share /add_valid_share /g_valid_share /get_wire_st_fdom /get_wire_st_next /get_wire_st_shr /ISet.subset /ISet.iset /ISet.mem /ISet.all /local_gate_end fsetallP all_iseqE !irng !allP => |>. move => H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17. rewrite !H2 !H8 -!H4 -!H10 => |>. split. move => k Hk. have : k \in fdom (MaurerP.get ws i).`1.`2. rewrite (in_subset (MaurerP.get ws i).`2) => |>. rewrite H2 iset_in_def => |>Hk1 Hk2. rewrite (prod_id ((MaurerP.get ws i)).`1) (prod_id ((MaurerP.get ws j)).`1) => |>. rewrite /mul_end => |>. rewrite !get_set_neqE => |>. smt(). smt(). have : MaurerAPI.consistent_pub_shares i j (oget (MaurerP.get ws i).`1.`2.[k]) (oget (MaurerP.get ws j).`1.`2.[k]). rewrite H16 => |>. rewrite /consistent_pub_shares => |>. move => x Hx. case (x=(MaurerP.get ws i).`1.`1) => |>. rewrite consistent_raw_shares_conv consistent_raw_shares_mul_end => |>. move => k Hk1 Hk2. rewrite /gate_send_messages => />. rewrite if_then => />. rewrite /all allP /local_gate_start => />. move => y Hy. rewrite MaurerP.get_imap => />. move :Hy. rewrite in_iseq => />. rewrite !MaurerP.get_map /send_messages => />. rewrite !MaurerP.get_init !irng !jrng => />. rewrite !Array5.initE !andabP !andaP => />. rewrite !MaurerP.get_map => />. rewrite !MaurerP.get_imap /local_gate_start /mul_start => />. rewrite /local_gate_start !MaurerP.get_zip /size !andabP !andaP /mul_start => />. rewrite (prod_id (MaurerP.get ws k).`1) => />. rewrite consistent_raw_shares_share => />. smt(). smt(). move => H18. rewrite consistent_raw_shares_conv consistent_raw_shares_mul_end_prefix => |>*. move :Hx. rewrite !iset_in_def in_iseq H4 => />. smt(). rewrite -consistent_raw_shares_conv H17 => />. move :Hx. rewrite !in_iseq H4 => />. smt(). qed.

lemma g_valid_share_step i g (ws:(MaurerAPI.wire_st * MaurerAPI.pub_st) MaurerP.arrayN) r :
  i \in MaurerCircuit.ST.partyset => 
  0 <= (MaurerP.get ws i).`1.`1 =>
  MaurerAPI.g_valid_share (MaurerP.get ws i) =>
    MaurerAPI.g_valid_share (MaurerP.get (MaurerWeakGateProofs.WG.G.protocol g ws r).`2 i).
  move => H. have : 0 <= i < MaurerP.size. move :H. rewrite iset_in_def => |>. 
  rewrite /g_valid_share /ISet.equal => |>H0 H1 H2. rewrite !MaurerWeakGateProofs.g_protocol_def. rewrite /g_protocol /get_wire_st_next /get_wire_st_fdom => |>. rewrite !MaurerP.get_imap => |>H3 H4 H5. rewrite !MaurerP.get_zip !andabP !andaP => |>. rewrite /local_gate_end /send_messages => |>*. rewrite gate_end_ge0 => />. rewrite /local_gate_end dom_gate_end. rewrite gate_end_wire => />. rewrite H4. rewrite /ISet.iset iset_succ => />. rewrite /local_gate_end dom_gate_end. rewrite gate_end_wire => />. rewrite H4. rewrite /ISet.iset iset_succ /ISet.subset => />.
  pose ins := (MaurerP.get
      (MaurerGate.send_messages
         (MaurerGate.GT.P.imap
            (fun (i0 : MaurerGate.GT.party) (wc : MaurerGate.share * MaurerGate.GT.local_rand) =>
               MaurerGate.local_gate_start i0 g wc.`1 wc.`2) (MaurerGate.GT.P.zip ws r))) i).
  have : (MaurerGate.gate_end i g (MaurerP.get ws i) ins).`2 \subset (MaurerP.get ws i).`2 `|` fset1 (MaurerP.get ws i).`1.`1. rewrite dom_gate_end_pub => />. move => H6. rewrite subsetP /(<=) => />x Hx. rewrite (in_subset_l _ ((MaurerP.get ws i)).`2) => />. move :H6. rewrite subsetP /(<=) => />H6. rewrite H6 => />. rewrite /ISet.subset H4 /ISet.iset in H5. rewrite H5 => />. qed.

lemma consistent_inputs_head i j g c wi wj :
    i \in MaurerCircuit.ST.partyset => j \in MaurerCircuit.ST.partyset =>
    MaurerCircuit.consistent_inputs (g::c) i j wi wj =>
      MaurerGate.consistent_inputs g i j wi wj.
   rewrite /consistent_inputs /consistent_shares /get_wire_st_next /get_wire_st_fdom => |>Hi Hj H H0 H1 H2 H3 H4 H5 H6. move :H. rewrite /valid_circuit /get_wire_st_next /get_wire_st_fdom => |>. move :H0 H1. rewrite /g_valid_share /get_wire_st_next /get_wire_st_fdom => |>. move => I1 I2 I3 I4 I5 I6 I7 I8. case g => />G.
   rewrite /get_wire_st_next /get_wire_st_fdom => />I9 I10 I11 I12 I13 I14. rewrite /ISet.mem !I2 !I5 /ISet.iset !iset_in_def => />. rewrite -!H2 => />. 
   rewrite /get_wire_st_next /get_wire_st_fdom => />I9 I10 I11 I12 I13 I14 I15. rewrite /ISet.mem !I2 !I5 /ISet.iset !iset_in_def => />. rewrite -!H2 -!H4 => />. 
   rewrite /get_wire_st_next /get_wire_st_fdom => />I9 I10. rewrite -!H2 => />. 
   rewrite /get_wire_st_next /get_wire_st_fdom => />I9 I10 I11 I12 I13 I14. rewrite /ISet.mem !I2 !I5 /ISet.iset !iset_in_def => />. rewrite -!H2 => />. qed.

theory MaurerWeakCircuitProofs.

  clone include WeakCircuitProofs with
    (*theory WGP = MaurerWeakGateProofs *) (*we don't clone this because of EC unification error, we instead clone MaurerWeakGate, since the proofs have been done above *)
    theory WGP.WG = MaurerWeakGate,
    op WC.B.consistent_inputs = MaurerCircuit.consistent_inputs
    proof valid_inputs_cons.
    realize valid_inputs_cons.
    rewrite !/valid_inputs => |>g c ws r H H0. split.
    move => i j Hi Hj.
    (*gate*)
    have : (WC.B.consistent_inputs (cons g c) i j ((WC.B.ST.P.get ws i)) ((WC.B.ST.P.get ws j))). rewrite H => |>*. clear H. rewrite /consistent_inputs => |>H. rewrite /get_wire_st_next /get_wire_st_fdom /get => |>. 
    have : (MaurerCircuit.valid_gate' (MaurerP.get ws i).`1.`1 g (MaurerP.get ws i).`2).`2. rewrite (valid_circuit_head g c _ _) => |>. clear H. move :H0. case g => |>G. 
    (*add*)
    rewrite /consistent_inputs /consistent_shares /add_valid_share /g_valid_share /get_wire_st_next /get_wire_st_fdom /ISet.mem => |>. progress. rewrite H6 iset_in_def => />. rewrite H6 iset_in_def => />. rewrite -H11 H0 => />. rewrite H9 iset_in_def => />. rewrite -H11 H2 => />. rewrite H9 iset_in_def => />. rewrite -H11 H4 => />. 
    (*smul*)
    rewrite /consistent_inputs /consistent_shares /smul_valid_share /add_valid_share /g_valid_share /get_wire_st_next /get_wire_st_fdom /ISet.mem => |>. progress. rewrite H7 iset_in_def => />. rewrite H7 iset_in_def => />. rewrite -H12 H0 => />. rewrite H10 iset_in_def => />. rewrite -H12 H2 => />. rewrite H10 iset_in_def => />. rewrite -H12 H4 => />. rewrite -H14 H5 => />.
    (*const*)
    rewrite /consistent_inputs /consistent_shares /const_valid_share /add_valid_share /g_valid_share /get_wire_st_next /get_wire_st_fdom /ISet.mem => |>. progress. rewrite -H7 H0 => />. 
    (*mul*)
    rewrite /consistent_inputs /consistent_shares /mul_valid_share /add_valid_share /g_valid_share /get_wire_st_next /get_wire_st_fdom /ISet.mem => |>. progress. rewrite H6 iset_in_def => />. rewrite H6 iset_in_def => />. rewrite -H11 H0 => />. rewrite H9 iset_in_def => />. rewrite -H11 H2 => />. rewrite H9 iset_in_def => />. rewrite -H11 H4 => />. 
    (*circuit*)
    move => i j Hi Hj. have : (WC.B.consistent_inputs (cons g c) i j ((WC.B.ST.P.get ws i)) ((WC.B.ST.P.get ws j))). rewrite H => />*. rewrite /consistent_inputs /get_wire_st_next /get_wire_st_fdom /get /ISet.subset /ISet.iset => |>. move => H1 H2 H3 H4.
    have : MaurerCircuit.g_wire g = ((MaurerP.get ws i)).`1.`1. move :H1. rewrite /valid_circuit => />H9 H10 H11 H12 H13. move :H H0 H12 H13. case g => />G. move => H9.
    rewrite (_:WC.WG.G.protocol=MaurerWeakGateProofs.WG.G.protocol). progress. rewrite get_gate_protocol_wire => |>. rewrite get_g_protocol_pubs => |>.  
    rewrite valid_circuit_behead => |>. rewrite consistent_shares_step => |>. apply/(consistent_inputs_head i j g c) => |>. have : WC.B.consistent_inputs (cons g c) i j (WC.B.ST.P.get ws i) (WC.B.ST.P.get ws j). rewrite H => />. rewrite /consistent_inputs => |>.
    rewrite !g_valid_share_step => />*. move :H2. rewrite /g_valid_share => />. move :H3. rewrite /g_valid_share => />. qed.

  lemma g_protocol_pubs g (ws:MaurerMPCReveal.P.ST.local_input MaurerP.arrayN) c i :
    i \in MaurerGate.ST.partyset =>
      MaurerCircuit.g_wire g = (MaurerP.get ws i).`1.`1 => 
      (MaurerP.get (MaurerGate.g_protocol g ws c).`2 i).`2 =
      (MaurerP.get ws i).`2 `|` MaurerCircuit.g_pubs g fset0.
    rewrite /g_protocol => />H H0. have : 0 <= i && i < MaurerP.size. move :H. rewrite iset_in_def => />*. move => irng.
    rewrite MaurerP.get_imap => />*. rewrite /local_gate_end MaurerP.get_zip /send_messages !irng /gate_send_messages => />*. move :H0. case g => />g Hg.
    rewrite /local_gate_end => />*. rewrite fsetU0 => />*.
    rewrite /local_gate_end => />*. rewrite fsetU0 => />*.
    rewrite /local_gate_end => />*. rewrite /ISet.union fset0U => />*. rewrite Hg => />*. 
    rewrite /local_gate_end => />*. rewrite fsetU0 => />*. qed.

  lemma rename_circ_protocol' :
    MaurerCircuit.circ_protocol' = WC.B.circ_protocol'.
    rewrite fun_ext => />c. rewrite fun_ext => />ws. rewrite fun_ext => />rs.
    elim c ws rs => |>. move => x l H ws rs.
    split.
    rewrite /ppcons /from_messages /send_messages /merge /pcons => |>. congr. rewrite fun_ext => />i. rewrite /merge /get /map /gate_send_messages => />. congr. rewrite fun_ext => />j. congr. congr. congr. rewrite /map /from_local_messages /send_messages /WC.B.stateful_protocol_round => />. congr. congr. congr. rewrite H => />. split.
    rewrite /pcons /map /merge => />. congr. rewrite fun_ext => />i. congr. congr. rewrite /map /WC.B.G.g_protocol => />. rewrite H => />. rewrite H => />. qed.

  lemma rename_circ_protocol :
    MaurerCircuit.circ_protocol = WC.B.circ_protocol. 
    rewrite fun_ext => />c. rewrite fun_ext => />ws. rewrite fun_ext => />rs.
    rewrite /circ_protocol => |>. rewrite MaurerP.tP => />. progress. rewrite !MaurerP.get_zip3 !andabP !andaP => />. rewrite !MaurerP.get_map => />. rewrite rename_circ_protocol' => />. rewrite rename_circ_protocol' => />. qed.

  lemma circ_protocol_pubs x (ws:MaurerMPCReveal.P.ST.local_input MaurerP.arrayN) cs i :
    i \in MaurerGate.ST.partyset =>
    MaurerCircuit.valid_rands x cs =>
    MaurerCircuit.check_c_wire x (MaurerP.get ws i).`1.`1 =>
      ((MaurerP.get ((MaurerCircuit.circ_protocol x ws cs)).`2 i)).`2 =
      (MaurerP.get ws i).`2 `|` MaurerCircuit.c_pubs x fset0.
    rewrite /circ_protocol => />H H0 H1. move :H0 H1. elim/last_ind x ws cs => />.
    move => ws cs H1. rewrite /c_pubs => />. rewrite fsetU0 => />*.
    move => s x H1 ws cs H2 H3. 
    rewrite rename_circ_protocol' circ_protocol_thr_rcons' => />*. rewrite (_:WC.WG.G.protocol=WGP.WG.G.protocol). progress. rewrite WGP.g_protocol_def => />. rewrite (_:WGP.WG.G.g_protocol=MaurerGate.g_protocol). progress. rewrite g_protocol_pubs => />*. rewrite (_:WC.B.circ_protocol'=MaurerCircuit.circ_protocol'). rewrite -rename_circ_protocol' //. rewrite circ_protocol_wire' => />*. move :H3. rewrite check_c_wire_rcons => />*. rewrite -rename_circ_protocol'. rewrite H1 => />. move :H2. rewrite (_:MaurerCircuit.valid_rands=WC.P.valid_rands). progress. rewrite valid_rands_rcons => />*. move :H3. rewrite check_c_wire_rcons => />*. rewrite c_pubs_rcons => />*. rewrite (g_pubs_acc x (MaurerCircuit.c_pubs s fset0)) => />*.
    rewrite (fsetUC (MaurerCircuit.g_pubs x fset0)). rewrite fsetUA => />*. qed.

end MaurerWeakCircuitProofs.

theory MaurerWeakRevealCircuitProofs.

  clone include WeakRevealProofs with
    theory WP.W = MaurerWeakCircuit.

end MaurerWeakRevealCircuitProofs.

theory MaurerMPCRevealProofs.

  lemma valid_wid i1 i2 x ys :
    i1 \in MaurerAdd.GT.partyset /\ i2 \in MaurerAdd.GT.partyset /\ MaurerMPCReveal.valid_outputs x ys =>
      ((MaurerP.get ys i1)).`1.`1 = ((MaurerP.get ys i2)).`1.`1.
    rewrite /valid_outputs => />Hi1 Hi2 H. have : MaurerMPCReveal.WR.mpc_consistent_outputs x i1 i2 (MaurerMPCReveal.WR.W.P.ST.P.get ys i1) (MaurerMPCReveal.WR.W.P.ST.P.get ys i2). rewrite H => />. rewrite /mpc_consistent_outputs => />. qed.

  lemma c_pubs_size wid n c ps :
    0 <= n => ps \subset iset n => MaurerCircuit.valid_circuit' n c ps => wid \in MaurerCircuit.c_pubs c ps => 
      0 <= wid < n + size c.
    pose sz := size c. have : size c <= sz. smt(). elim/last_ind:c sz => />.
    move => sz H H0 H1 H2. move :H2. rewrite /c_pubs => />*. have : wid \in iset n. rewrite (in_subset ps) => />*. rewrite iset_in_def => />*. smt().
    move => s x H sz H0 H1 H2 H3 H4.
    rewrite c_pubs_rcons in H4 => />*. move :H3. rewrite valid_circuit_rcons' => />H3 H5. move :H H0 H1 H2 H3 H4 H5. case x => />G.
    (*Add*)
   move => H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. rewrite size_rcons in H0 => />. have : 0 <= wid && wid < n + sz. rewrite H => />*. smt(). smt().  
    (*SMul*)
    move => H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. have : 0 <= wid && wid < n + sz. rewrite H => />*. rewrite size_rcons in H0 => />*. smt(). smt(). 
    (*Const*)
     move => H H0 H1 H2 H3 H4 H5. move :H4. rewrite in_fsetU in_fset1 H5 => />H4. rewrite size_rcons in H0 => />. case (wid=n+size s) => />. smt(size_ge0). move => H6. have : 0 <= wid && wid < n+sz. rewrite H => />. smt(). move :H4. rewrite H6 => />*. progress.
    (*Mul*)
    move => H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. rewrite size_rcons in H0 => />. have : 0 <= wid && wid < n + sz. rewrite H => />*. smt(). smt(). qed.

  lemma g_valid_share_protocol x (ws:(MaurerAPI.wire_st * MaurerAPI.pub_st) MaurerP.arrayN) cs i :
    i \in MaurerMPCReveal.WR.W.P.ST.partyset => 
    0 <= ((MaurerP.get ws i)).`1.`1 =>
    MaurerAPI.g_valid_share ((MaurerMPCReveal.P.ST.P.get ws i)) =>
    MaurerAPI.g_valid_share ((MaurerP.get ((MaurerCircuit.circ_protocol x ws cs)).`2 i)).
    rewrite /circ_protocol. elim x ws cs => |>.
    move => x l H ws cs. rewrite /get_wire_st_next /get_wire_st_fdom /get /ISet.iset /ISet.subset => |>H0 H1 H2. 
    rewrite H => |>. clear H. 
    rewrite (_:MaurerCircuit.G.g_protocol=MaurerWeakGateProofs.WG.G.g_protocol). progress. rewrite -MaurerWeakGateProofs.g_protocol_def => />*. rewrite MaurerWeakGateProofs.g_protocol_def => />. rewrite (_:MaurerWeakGateProofs.WG.G.g_protocol=MaurerGate.g_protocol). progress. rewrite g_protocol_wire => |>*. smt(). rewrite /get (_:MaurerCircuit.G.g_protocol=MaurerWeakGateProofs.WG.G.g_protocol). progress. rewrite -MaurerWeakGateProofs.g_protocol_def => |>*. rewrite g_valid_share_step => />*. qed.

  lemma consistent_shares_protocol i j x ws cs :
    i \in MaurerCircuit.ST.partyset => j \in MaurerCircuit.ST.partyset =>
    MaurerCircuit.consistent_inputs x i j ((MaurerP.get ws i)) ((MaurerP.get ws j)) => 
    MaurerAPI.consistent_shares i j ((MaurerP.get ((MaurerCircuit.circ_protocol x ws cs)).`2 i)) ((MaurerP.get ((MaurerCircuit.circ_protocol x ws cs)).`2 j)).
    rewrite /circ_protocol. elim x ws cs => |>.
    move => ws Hi Hj. rewrite /consistent_inputs => |>x l H. 
    move => x l H ws cs Hi Hj. rewrite /consistent_inputs => |> H0 H1 H2 H3.
    rewrite H => |>*. clear H. rewrite /consistent_inputs /get_wire_st_next /get_wire_st_fdom => |>.
    rewrite (_:MaurerCircuit.G.g_protocol=MaurerGate.g_protocol). progress.
    rewrite !g_protocol_wire => |>*. rewrite (_:MaurerGate.g_protocol=MaurerWeakGateProofs.WG.G.g_protocol). progress. rewrite -!MaurerWeakGateProofs.g_protocol_def => |>. rewrite !g_valid_share_step => |>*. move :H0. rewrite /valid_circuit => |>. move :H2. rewrite /g_valid_share => |>. 
    rewrite consistent_shares_step => |>. rewrite (consistent_inputs_head i j x l) => |>*. rewrite /consistent_inputs => |>. rewrite get_g_protocol_pubs => |>. have : (MaurerCircuit.valid_gate' ((MaurerP.get ws i)).`1.`1 x ((MaurerP.get ws i)).`2).`2. rewrite (valid_circuit_head x l _ ((MaurerP.get ws i)).`2) => |>. clear H0. case x => />. rewrite valid_circuit_behead => |>. qed.

  lemma reconstruct_rshr_unshare (i:int) (pid:pid) (cr:pid fset) (ss:shrs) :
    0 <= i < 6 =>
    0 <= pid < 5 =>
    MaurerWeakMul.corrupted_set cr =>
    (forall i j, 0 <= i < 5 => 0 <= j < 5 => MaurerAPI.consistent_raw_shares i j ss.[i] ss.[j] ) =>
    (Maurer5Spec.reconstruct_rshr (unshare ss) (ofset (fun pid => ss.[pid]) cr)).[nth witness (shr_idx pid) i] = (ss.[pid]).[i].
    rewrite /reconstruct_rshr => />H H0 H1 H2 H3 H4 H5. rewrite fdom_ofset => />. move :H4. rewrite (card2E cr) => />H4. move :H4. rewrite !oflist_cons !oflist_nil !fsetU0 => />H4.
    move :H4. rewrite /ISet.subset subsetP /(<=) => />H4. have : nth witness (elems cr) 0 \in MaurerMul.ST.partyset. rewrite H4 => />. rewrite in_fsetU !in_fset1 => />. move => dom0. have : nth witness (elems cr) 1 \in MaurerMul.ST.partyset. rewrite H4 => />. rewrite in_fsetU !in_fset1 => />. move => dom1. clear H4. rewrite !fold2 => />.     
    have : uniq (elems cr). rewrite uniq_elems => />. rewrite (size2E (elems cr)) => />. move :H3. rewrite /ISet.card cardE /corrupted_t => />. 
    move :dom0 dom1. rewrite !iset_in_def => />I1 I2 I3 I4.
    rewrite !ofset_some => />. rewrite in_fsetU !in_fset1 => />. rewrite in_fsetU !in_fset1 => />. 
    rewrite add_p_shr_swap => />. 
    have : uniq (elems cr). rewrite uniq_elems => />. rewrite (size2E (elems cr)) => />. move :H3. rewrite /ISet.card cardE /corrupted_t => />. 
    move => x1 x2 Hx11 Hx12 Hx21 Hx22. rewrite -consistent_raw_shares_conv H5 => />.
    rewrite !ofset_some => />. rewrite in_fsetU !in_fset1 => />. rewrite in_fsetU !in_fset1 => />.
    rewrite /fill_rshr => />. rewrite Array10.mapiE => />. have : 0 <= nth witness (shr_idx pid) i < 10. rewrite rng_shr_idx => />. move => H4. have : pid \in MaurerMul.ST.partyset. have : cr \subset MaurerMul.ST.partyset. rewrite (card2E cr) => />x. rewrite !oflist_cons !oflist_nil => />. rewrite fsetU0 in_fsetU !in_fset1 => />H6. case H6 => />. rewrite iset_in_def => />. smt(). 
    rewrite !get_add_p_shr => />. move :dom0. rewrite iset_in_def => />. move :dom1. rewrite iset_in_def => />. 
    move :dom0. rewrite iset_in_def => />. move :dom1. rewrite iset_in_def => />. move => I1 I2 I3 I4.
    case (nth witness (shr_idx pid) i \in shr_idx (nth witness (elems cr) 0)) => />I5. have :  (MaurerAPI.consistent_raw_shares (nth witness (elems cr) 0) pid ss.[nth witness (elems cr) 0] ss.[pid]). rewrite H5 => />. rewrite /consistent_raw_shares /all fallP /IMap.zip => />I6. have : (oget
         (fzip ((MaurerAPI.raw_shares (nth witness (elems cr) 0) ss.[nth witness (elems cr) 0]))
            ((MaurerAPI.raw_shares pid ss.[pid]))).[nth witness (shr_idx pid) i]).`1 =
      (oget
         (fzip ((MaurerAPI.raw_shares (nth witness (elems cr) 0) ss.[nth witness (elems cr) 0]))
            ((MaurerAPI.raw_shares pid ss.[pid]))).[nth witness (shr_idx pid) i]).`2. apply I6. rewrite fdom_fzip => |>. rewrite !raw_shares_conv !dom_raw_shares => />. rewrite in_fsetI !mem_oflist => />. rewrite nth_in => />I7. rewrite size_shr_idx => />. rewrite !fzip_some => />. rewrite in_fsetI !raw_shares_conv !dom_raw_shares => />. rewrite !mem_oflist !nth_in => />I7. rewrite size_shr_idx => />I7. rewrite !raw_shares_conv !get_raw_shares =>/>. rewrite I5 nth_in => />I7. rewrite size_shr_idx =>/>. rewrite I7 shr_idx_id => />*.
    case (nth witness (shr_idx pid) i \in shr_idx (nth witness (elems cr) 1)) => />I6. have :  (MaurerAPI.consistent_raw_shares (nth witness (elems cr) 1) pid ss.[nth witness (elems cr) 1] ss.[pid]). rewrite H5 => />. rewrite /consistent_raw_shares /all fallP /IMap.zip => />I7. have : (oget
         (fzip ((MaurerAPI.raw_shares (nth witness (elems cr) 1) ss.[nth witness (elems cr) 1]))
            ((MaurerAPI.raw_shares pid ss.[pid]))).[nth witness (shr_idx pid) i]).`1 =
      (oget
         (fzip ((MaurerAPI.raw_shares (nth witness (elems cr) 1) ss.[nth witness (elems cr) 1]))
            ((MaurerAPI.raw_shares pid ss.[pid]))).[nth witness (shr_idx pid) i]).`2. apply I7. rewrite fdom_fzip !raw_shares_conv !dom_raw_shares => />. rewrite in_fsetI !mem_oflist => />. rewrite nth_in => />. rewrite size_shr_idx => />. rewrite !fzip_some => />. rewrite in_fsetI !raw_shares_conv !dom_raw_shares => />. rewrite !mem_oflist !nth_in => />. rewrite size_shr_idx => />. rewrite !raw_shares_conv !get_raw_shares =>/>. rewrite I6 nth_in => />. rewrite size_shr_idx =>/>. move => I8. rewrite I8 shr_idx_id => />. rewrite Array10.createiE => />*. have : 0 <= nth witness (shr_idx pid) i < 10. rewrite rng_shr_idx => />*. smt(). 
    have : 0 <= nth witness (shr_idx pid) i && nth witness (shr_idx pid) i < 10. rewrite rng_shr_idx => />*. move => shr_rng.
    rewrite reconstruct_missing => />*. have : uniq (elems cr). rewrite uniq_elems => />*. rewrite (size2E (elems cr)) => />*. move :H3. rewrite /ISet.card cardE /corrupted_t => />*.
    rewrite -consistent_raw_shares_conv H5 => />.  
    move : I5 I6. rewrite (_: (
! (nth witness (shr_idx pid) i \in shr_idx (nth witness (elems cr) 0)) =>
! (nth witness (shr_idx pid) i \in shr_idx (nth witness (elems cr) 1)) =>
(unrshr ss).[cr_missing (cons (nth witness (elems cr) 0) (cons (nth witness (elems cr) 1) []))] = ss.[pid].[i]) = (fun cr => 
! (nth witness (shr_idx pid) i \in shr_idx (nth witness (cr) 0)) =>
! (nth witness (shr_idx pid) i \in shr_idx (nth witness (cr) 1)) =>
(unrshr ss).[cr_missing (cons (nth witness (cr) 0) (cons (nth witness (cr) 1) []))] = ss.[pid].[i]) (elems cr) ). progress. apply (cr_ind (elems cr)) => />. have : size (elems cr) = 2. move :H3. rewrite /ISet.card cardE => />*. rewrite uniq_elems => />. progress. move:H6. rewrite card2E => />. rewrite !oflist_cons !oflist_nil !fsetU0 => />H6. have : elems (fset1 (nth witness (elems cr) 0) `|` fset1 (nth witness (elems cr) 1)) = [(nth witness (elems cr) 0);(nth witness (elems cr) 1)] \/ elems (fset1 (nth witness (elems cr) 0) `|` fset1 (nth witness (elems cr) 1)) = [(nth witness (elems cr) 1);(nth witness (elems cr) 0)]. rewrite elems_fset1U => />*. have : uniq (elems cr). rewrite uniq_elems => />*. rewrite (size2E (elems cr)) => />*. move :H3. rewrite /ISet.card cardE /corrupted_t => />H7 H8. case H8 => />H8. move :H6. rewrite H8 => />H6. case H6 => />. rewrite in_iseq => />*. rewrite in_iseq => />*. move:H6. rewrite H8 => />H6. case H6 => />. rewrite in_iseq => />. rewrite in_iseq => />. 
    move => I5 I6. rewrite /unrshr cr_missing_01 => />*. move :I5. rewrite not_in_shr_idx_0 => />I5. move :I6. rewrite not_in_shr_idx_1 => />I6. have : nth witness (shr_idx pid) i = 0. smt(). rewrite nth_shr_idx_0 => />I7. case I7 => />I7. case I7 => />. rewrite (consistent_s21_s34 ss.[2] ss.[3]) => />. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*. rewrite (consistent_s21_s42 ss.[2] ss.[4]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*.
    move => I5 I6. rewrite /unrshr cr_missing_02 => />*. move :I5. rewrite not_in_shr_idx_0 => />I5. move :I6. rewrite not_in_shr_idx_2 => />I6. have : nth witness (shr_idx pid) i = 1. smt(). rewrite nth_shr_idx_1 => />I7. case I7 => />I7. case I7 => />. rewrite (consistent_s10_s35 ss.[1] ss.[3]) => />. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*. rewrite (consistent_s10_s43 ss.[1] ss.[4]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*.
    move => I5 I6. rewrite /unrshr cr_missing_03 => />*. move :I5. rewrite not_in_shr_idx_0 => />I5. move :I6. rewrite not_in_shr_idx_3 => />I6. have : nth witness (shr_idx pid) i = 2. smt(). rewrite nth_shr_idx_2 => />I7. case I7 => />I7. case I7 => />. rewrite (consistent_s11_s22 ss.[1] ss.[2]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*. rewrite (consistent_s11_s44 ss.[1] ss.[4]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*.
    move => I5 I6. rewrite /unrshr cr_missing_04 => />*. move :I5. rewrite not_in_shr_idx_0 => />I5. move :I6. rewrite not_in_shr_idx_4 => />I6. have : nth witness (shr_idx pid) i = 3. smt(). rewrite nth_shr_idx_3 => />I7. case I7 => />I7. case I7 => />. rewrite (consistent_s13_s25 ss.[1] ss.[2]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*. rewrite (consistent_s13_s30 ss.[1] ss.[3]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*.
    move => I5 I6. rewrite /unrshr cr_missing_12 => />*. move :I5. rewrite not_in_shr_idx_1 => />I5. move :I6. rewrite not_in_shr_idx_2 => />I6. have : nth witness (shr_idx pid) i = 4. smt(). rewrite nth_shr_idx_4 => />I7. case I7 => />I7. case I7 => />. rewrite (consistent_s04_s32 ss.[0] ss.[3]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*. rewrite (consistent_s04_s41 ss.[0] ss.[4]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*.
    move => I5 I6. rewrite /unrshr cr_missing_13 => />*. move :I5. rewrite not_in_shr_idx_1 => />I5. move :I6. rewrite not_in_shr_idx_3 => />I6. have : nth witness (shr_idx pid) i = 5. smt(). rewrite nth_shr_idx_5 => />I7. case I7 => />I7. case I7 => />. rewrite (consistent_s00_s23 ss.[0] ss.[2]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*. rewrite (consistent_s00_s45 ss.[0] ss.[4]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*.
    move => I5 I6. rewrite /unrshr cr_missing_14 => />*. move :I5. rewrite not_in_shr_idx_1 => />I5. move :I6. rewrite not_in_shr_idx_4 => />I6. have : nth witness (shr_idx pid) i = 6. smt(). rewrite nth_shr_idx_6 => />I7. case I7 => />I7. case I7 => />. rewrite (consistent_s05_s20 ss.[0] ss.[2]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*. rewrite (consistent_s05_s33 ss.[0] ss.[3]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*.
    move => I5 I6. rewrite /unrshr cr_missing_23 => />*. move :I5. rewrite not_in_shr_idx_2 => />I5. move :I6. rewrite not_in_shr_idx_3 => />i6. have : nth witness (shr_idx pid) i = 7. smt(). rewrite nth_shr_idx_7 => />I7. case I7 => />I7. case I7 => />. rewrite (consistent_s03_s15 ss.[0] ss.[1]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*. rewrite (consistent_s03_s40 ss.[0] ss.[4]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*.
    move => I5 I6. rewrite /unrshr cr_missing_24 => />*. move :I5. rewrite not_in_shr_idx_2 => />I5. move :I6. rewrite not_in_shr_idx_4 => />I6. have : nth witness (shr_idx pid) i = 8. smt(). rewrite nth_shr_idx_8 => />I7. case I7 => />I7. case I7 => />. rewrite (consistent_s02_s14 ss.[0] ss.[1]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*. rewrite (consistent_s02_s31 ss.[0] ss.[3]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*.
    move => I5 I6. rewrite /unrshr cr_missing_34 => />*. move :I5. rewrite not_in_shr_idx_3 => />I5. move :I6. rewrite not_in_shr_idx_4 => />I6. have : nth witness (shr_idx pid) i = 9. smt(). rewrite nth_shr_idx_9 => />I7. case I7 => />I7. case I7 => />. rewrite (consistent_s01_s12 ss.[0] ss.[1]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*. rewrite (consistent_s01_s24 ss.[0] ss.[2]) => />*. rewrite -consistent_raw_shares_conv => />. rewrite H5 => />*.
    move => x y Hxy Hx Hy.
    rewrite cr_missing_swap => />*. move :Hx. rewrite card2E => />. rewrite !oflist_cons !oflist_nil !fsetU0 => />Hx. have : elems (fset1 (nth witness (elems cr) 0) `|` fset1 (nth witness (elems cr) 1)) = [(nth witness (elems cr) 0);(nth witness (elems cr) 1)] \/ elems (fset1 (nth witness (elems cr) 0) `|` fset1 (nth witness (elems cr) 1)) = [(nth witness (elems cr) 1);(nth witness (elems cr) 0)]. apply elems_fset1U => />*. have : uniq (elems cr). rewrite uniq_elems => />*. rewrite (size2E (elems cr)) => />*. move :H3. rewrite /ISet.card cardE /corrupted_t => />*. move => H4. case H4 => />H4. move :Hx. rewrite H4 => />Hx. case Hx => />. move :Hx. rewrite H4 => />Hx. case Hx => />. 
    move :Hy. rewrite /ISet.card card2E => />. rewrite !oflist_cons !oflist_nil !fsetU0 => />Hy. have : elems (fset1 (nth witness (elems cr) 0) `|` fset1 (nth witness (elems cr) 1)) = [(nth witness (elems cr) 0);(nth witness (elems cr) 1)] \/ elems (fset1 (nth witness (elems cr) 0) `|` fset1 (nth witness (elems cr) 1)) = [(nth witness (elems cr) 1);(nth witness (elems cr) 0)]. apply elems_fset1U => />*. have : uniq (elems cr). rewrite uniq_elems => />*. rewrite (size2E (elems cr)) => />*. move :H3. rewrite /ISet.card cardE /corrupted_t => />*. move => H6. case H6 => />H6. move :Hy. rewrite H6 => />Hy. case Hy => />. move :Hy. rewrite H6 => />Hy. case Hy => />. 
    rewrite eq_logical => />*. progress. rewrite H4 => />*. rewrite H4 => />*. qed.

  clone include MPCRevealProofs with
    (* We do not unify MaurerWeakCircuitProofs because of EC error. We instead unify MaurerWeakCircuit, since the proofs have been done above *)
    theory WRP.WP.W = MaurerWeakCircuit,
    type WRP.WR.pub_input = MaurerWeakReveal.pub_input,
    op WRP.WR.pub_input_conv = MaurerWeakReveal.pub_input_conv,
    type WRP.WR.final_output = MaurerWeakReveal.final_output,
    op WRP.WR.weak_rounds = MaurerWeakReveal.weak_rounds,
    op WRP.WR.reveal_local_start = MaurerWeakReveal.reveal_local_start,
    op WRP.WR.reveal_local_end = MaurerWeakReveal.reveal_local_end,
    op WRP.WR.mpc_consistent_inputs = MaurerWeakReveal.mpc_consistent_inputs,
    op WRP.WR.mpc_consistent_outputs = MaurerWeakReveal.mpc_consistent_outputs,
    op WRP.WR.final_valid_local_messages = MaurerWeakReveal.final_valid_local_messages,
    op WRP.WR.final_valid_msg = MaurerWeakReveal.final_valid_msg,
    op MR.reveal_functionality = MaurerMPCReveal.reveal_functionality,
    op MR.reconstruct_final = MaurerMPCReveal.reconstruct_final,
    op MR.corrupted_t = 2
    proof reconstruct_final_messages, reveal_correctness, valid_execution, valid_inputs_start, MR.corrupted_le.
    realize MR.corrupted_le. rewrite /corrupted_t /parties => />. qed.
    realize reveal_correctness.
    rewrite /reveal_functionality /reveal_local_end /reveal_start /unshare_ouput /output_end => />i x ss H H0. rewrite /unshare_output /send_messages /reveal_local_start /gate_send_messages /get_wire_st_next => />. have : 0 <= i < MaurerP.size. move :H. rewrite /partyset /ISet.iset iset_in_def => />. move => Hi. rewrite if_then => />. rewrite /all allP => />y. rewrite in_iseq /size => />Hy1 Hy2. rewrite !MaurerP.get_map => />. rewrite /MaurerWeakCircuit.WG.unshare /MaurerWeakGate.unshare /MaurerAPI.g_unshare /IMap.get /IMap.ofset => />. rewrite ofset_some /get_wire_st_fdom /get_wire_st_next => />. 
    move :H0. rewrite /valid_outputs => />H0. have : MR.WR.mpc_consistent_outputs x 0 0 (MR.WR.W.P.ST.P.get ss 0) (MR.WR.W.P.ST.P.get ss 0). rewrite H0 => />. rewrite /ISet.mem /ISet.iset !iset_in_def => />. rewrite /mpc_consistent_outputs /get_wire_st_next /get_wire_st_fdom /ISet.intersect /ISet.subset /ISet.iset /get => />. rewrite /get_wire_st_fdom /get_wire_st_next => />. progress. rewrite H6 /ISet.iset iset_in_def => />. smt().
    rewrite /MaurerAPI.unshare /mk_shares . congr. rewrite Array5.tP => />j Hj1 Hj2. rewrite !Array5.initE !andabP !andaP => />. rewrite !MaurerP.get_map /get_wire_st_shr => />. rewrite /output_start => />. rewrite (prod_id (MaurerP.get ss j).`1) => />. rewrite /send_messages /get => />. rewrite !MaurerP.get_init Hi => />. rewrite !MaurerP.get_init Hi => />. rewrite !Array5.initE !andabP !andaP => />. rewrite !MaurerP.get_map => />. rewrite (prod_id (MaurerP.get ss j).`1) => />. rewrite !Array5.createE => />. rewrite !Array5.initE => />. move :Hi. rewrite /size => />. rewrite (valid_wid 0 j x) => />. rewrite !iset_in_def => />. qed.
    realize valid_execution.
    move => |> x ws cs H H0. move :H. rewrite /valid_inputs /valid_outputs => |>H i j Hi Hj. rewrite /mpc_consistent_outputs /get /get_wire_st_next /get_wire_st_fdom => |>. rewrite (_:MR.WR.W.P.stateful_protocol=MaurerWeakCircuitProofs.WC.B.stateful_protocol). progress. rewrite -MaurerWeakCircuitProofs.equiv_circ_protocol_stateful => |>. rewrite -MaurerWeakCircuitProofs.rename_circ_protocol. rewrite consistent_shares_protocol => |>. have : WRP.WR.consistent_inputs x i j (WRP.WR.ST.P.get ws i) (WRP.WR.ST.P.get ws j). rewrite H => />. rewrite /consistent_inputs => />.
    have : WRP.WR.consistent_inputs x i j (WRP.WR.ST.P.get ws i) (WRP.WR.ST.P.get ws j). rewrite H => |>. rewrite /consistent_inputs /mpc_consistent_inputs /consistent_inputs => |>H1 H2 H3 H4. rewrite !g_valid_share_protocol => |>. move :H2. rewrite /g_valid_share => />. move :H3. rewrite /g_valid_share => />.
    rewrite /valid_circuit => |>. rewrite circ_protocol_wire => |>. rewrite MaurerWeakCircuitProofs.circ_protocol_pubs => |>. rewrite (valid_circuit_check_c_wire _ _ ((MaurerP.get ws i)).`2) => |>*. move :H2 H3 H4. rewrite /g_valid_share /consistent_shares => |>. rewrite /get_wire_st_next /get_wire_st_fdom /ISet.all /ISet.subset all_iseqE /ISet.intersect /ISet.iset /pub_input_conv => |>H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. rewrite (_:(MaurerP.get ws i).`1.`1 + size x - size x = (MaurerP.get ws i).`1.`1). smt(size_ge0). split. progress. move :H1. rewrite /valid_circuit /get_wire_st_next /get => |>I1 I2 I3 I4. split. rewrite subsetIr => />. move :I4. rewrite /valid_circuit' => |>. move => I4.
   have : MaurerCircuit.c_pubs x fset0 `&` iset ((MaurerP.get ws i)).`1.`1 = fset0. rewrite (subset_l0 _ (iset' ((MaurerP.get ws i)).`1.`1 (size x))). rewrite (valid_circuit_c_pubs0 _ _ ((MaurerP.get ws i)).`2) => />*. rewrite fsetP => />*. rewrite !in_fsetI iset_in_def iset_in_def' !in_fset0 => />*. smt(). trivial. move => I5. rewrite fsetIUl => />. rewrite I5 => />. rewrite fsetU0. rewrite fsetIC subset_fsetI_id => |>. qed.
    realize valid_inputs_start.
    rewrite /valid_inputs => |>. move => x ws H i j Hi Hj. have : WRP.WR.consistent_inputs x i j (WRP.WR.ST.P.get ws i) (WRP.WR.ST.P.get ws j). rewrite H => />. rewrite /consistent_inputs /mpc_consistent_inputs /consistent_inputs => />. qed.
    realize reconstruct_final_messages.
    rewrite /reveal_functionality /unshare_output /reconstruct_final /reveal_start /reveal_local_start /valid_outputs => />i x s ss H H0. rewrite MaurerP.tP /get => y Hy. rewrite !MaurerP.get_init !Hy => />*. rewrite /output_start /init_sh => />*. rewrite (prod_id (MaurerP.get s y).`1) => />*. rewrite Array5.tP => j Hj. rewrite !Array5.createiE => />*. rewrite /MaurerWeakCircuit.WG.unshare /MaurerWeakGate.unshare !wire_g_unshare => />*. rewrite Array6.tP => k Hk. rewrite /get_shr /mk_shares /get_wire_st_next /get_wire_st_shr => />. rewrite Array5.initE Hj => />. rewrite !MaurerP.get_init /size Hj => />. rewrite /reconstruct_shrs /IMap.map /share_raw => />. rewrite Array5.initE /size Hy => />.
    rewrite /init_sh => />. rewrite get_of_list => />. rewrite (nth_map witness) => />*. rewrite size_shr_idx => />*. move :Hy. rewrite /size => />*. move :Hk. progress. rewrite /g_unshare => />. rewrite ofset_some => />. have : (MR.WR.mpc_consistent_outputs x 0 1 ((MR.WR.W.P.ST.P.get s 0)) ((MR.WR.W.P.ST.P.get s 1))). rewrite H0 => />*. rewrite /ISet.mem !iset_in_def => />*. rewrite /mpc_consistent_outputs /g_valid_share /consistent_shares /get_wire_st_fdom /get_wire_st_next /get => |>. progress. rewrite H3 /ISet.iset iset_in_def => />. move :H1. rewrite /valid_circuit => />. move => I1 I2 I3 I4. smt(size_ge0). 
    have : forall i, 0 <= i < 5 => (MaurerP.get s 0).`1.`1 = (MaurerP.get s i).`1.`1. move => i2 Hi2. have : (MR.WR.mpc_consistent_outputs x i2 0 ((MaurerP.get s i2)) ((MaurerP.get s 0))). rewrite H0 => />. rewrite /ISet.mem !iset_in_def /parties /size => />. move :Hi2. progress. rewrite /mpc_consistent_outputs /consistent_shares /get_wire_st_next => |>. progress. rewrite H4 => />. move => A.
    pose sss := ((Array5.init (fun (party : int) => oget ((MaurerP.get s party)).`1.`2.[((MaurerP.get s 0)).`1.`1 - 1]))).
    rewrite (_: (fmap (fun (wi : MaurerAdd.share) => oget wi.`1.`2.[wi.`1.`1 - 1]) ((MR.corrupted i s))) = (ofset (fun pid => sss.[pid]) i) ). rewrite -fmap_eqIn => />*. rewrite fdom_map !fdom_ofset => />n Hn. rewrite /sss ofset_some => />*. rewrite map_some => />*. rewrite /corrupted => />*. rewrite -mem_fdom fdom_ofset => />*. rewrite /corrupted Array5.initE => />*. rewrite !ofset_some => />*. have : 0 <= n < 5. have : n \in MaurerMul.ST.partyset. apply (in_subset i) => />*. rewrite iset_in_def => />*. move => H8. rewrite H8 => />*.
    congr. rewrite /get => />. congr. rewrite -A => />. 
    rewrite (_:(MaurerAPI.mk_shares (MaurerP.map (fun (x0 : MaurerAPI.wire_st * MaurerAPI.pub_st) => MaurerAPI.get_wire_st_shr x0.`1 ((MaurerP.get s 0).`1.`1 - 1)) s)) = sss). rewrite /mk_shares /sss => />. rewrite Array5.tP => l Hl. rewrite !Array5.initE => />. rewrite !MaurerP.get_map /size => />. 
    rewrite reconstruct_rshr_unshare => />. move :Hy. progress.
    move => i0 j0 Hi0_1 Hi0_2 Hj0_1 Hj0_2. have : (MR.WR.mpc_consistent_outputs x i0 j0 ((MR.WR.W.P.ST.P.get s i0)) ((MR.WR.W.P.ST.P.get s j0))). rewrite H0 => />*. rewrite /ISet.mem !iset_in_def => />*. rewrite /mpc_consistent_outputs /consistent_shares all_iseqE allP /get_wire_st_shr /get_wire_st_next /get => |>. move => I1 I2 I3 I4 I5 I6 I7 I8. rewrite /sss => |>. rewrite !Array5.initE !andabP !andaP => |>. rewrite I8 => />. rewrite in_iseq => />. rewrite !(A i0) => />.
    move :I1. rewrite /valid_circuit /ISet.iset /ISet.subset /ISet.intersect => />K1 K2 K3 K4. smt(size_ge0).
    rewrite /sss => />. rewrite Array5.initE /size Hy => />. rewrite (A y) => />. move :Hy. progress. qed.

end MaurerMPCRevealProofs.
