require import AllCore SmtMap ZModP List FSet Distr DList.
require import Array5 Array6 Array9 Array10.
require (****) PrimeField.

require import AuxList AuxFSet AuxSmtMap AuxArray.

theory Maurer5SS.

clone import ZModP.ZModField as PF
 rename "zmod" as "zp".

clear [PF.* PF.Sub.* PF.Sub.Lift.* PF.ZModule.* PF.ComRing.* PF.ZModpRing.*
       PF.ZModpRing.AddMonoid.* PF.ZModpRing.MulMonoid.*
       PF.DZmodP.* PF.DZmodP.Support.*
       PF.ZModpField.* PF.ZModpField.AddMonoid.* PF.ZModpField.MulMonoid.*].

(* wrappers to give a [FiniteField] view on the new [ZModP] deffinitions... *)
type t = PF.zp.
abbrev fadd = PF.(+).
abbrev fsub (x y:zp) = PF.(+) x (-y).
abbrev fumin (x: zp) = -x.
abbrev fmul = PF.( *).
abbrev fzero = PF.zero.


type rand = t Array9.t.
op sum_rand r = List.foldl fadd fzero (Array9.to_list r).

(*
Notes:
	- Wire Index starts at 1.
	- SharesPP 5: [[5,9,8,7,4,6],
                       [1,2,9,3,8,7],
                       [6,0,2,5,9,3],
                       [3,8,4,6,0,1],
                       [7,4,0,1,2,5]], nSharesPP = 6, nShares = 10

	- MultSum 5: [(0,0),(0,1),(0,2),(0,4),
                      (1,3),(1,4),(1,5),
                      (2,0),(2,2),(2,3),(2,4),
                      (3,0),(3,1),(3,2),(3,5),
                      (4,1),(4,2),(4,3),
                      (5,0),(5,3)]

*)
type pid = int.

op shr_idx (p : pid) : int list =
      if p = 0 then 5::9::8::7::4::6::[] else 
      if p = 1 then 1::2::9::3::8::7::[] else
      if p = 2 then 6::0::2::5::9::3::[] else
      if p = 3 then 3::8::4::6::0::1::[] else
      if p = 4 then 7::4::0::1::2::5::[] else
                    witness.

op shr_idxs = iseq 10.



type val = t.
type shr = t Array6.t.   (* a share *)
type rshr = t Array10.t. (* raw shares *)
type shrs = shr Array5.t.   (* all shares *)

op init_sh (p : pid, rs : rshr) : shr=
   Array6.of_list witness (map (fun i => rs.[i]) (shr_idx p)).

op rshare (s:val, r: rand) : rshr =
  Array10.init 
       (fun i => if i = 9
                 then fsub s  (sum_rand r)
                 else r.[i]).

op share(s : val, r : rand) : shrs =
    let rs = rshare s r in
       Array5.init (fun i => init_sh i rs).

op share_raw (rs:rshr) : shrs = Array5.init (fun i => init_sh i rs).

op pshare(s : val) : shrs = 
    let ms = fumin  s in
       Array5.init (fun i =>
         init_sh i 
          (Array10.of_list witness (ms::s::ms::s::ms::s::s::s::ms::fzero::[]))).

op runshare (ss:rshr) : val =
  List.foldl fadd fzero (Array10.to_list ss).

op unshare(ss : shrs) = 
       fadd ss.[0].[0] (* 5 *)
      (fadd ss.[0].[1] (* 9 *)
      (fadd ss.[0].[2] (* 8 *)
      (fadd ss.[0].[3] (* 7 *)
      (fadd ss.[0].[4] (* 4 *)
      (fadd ss.[0].[5] (* 6 *)
      (fadd ss.[1].[0] (* 1 *)
      (fadd ss.[1].[1] (* 2 *)
      (fadd ss.[1].[3] ss.[2].[1])))))))). (* 3 0 *)

op gen_raw : zp distr = PF.DZmodP.dunifin.
op gen_raw6 : (zp list) distr =
    dlist gen_raw 6.
op gen_raw9 : (zp list) distr =
    dlist gen_raw 9.
op gen_shr : shr distr =
    dapply (Array6.of_list witness) gen_raw6.
op gen_rand : rand distr =
    dapply (Array9.of_list witness) gen_raw9.

lemma gen_raw_ll :
  is_lossless gen_raw.
  rewrite /gen_raw => />*. rewrite DZmodP.dunifin_ll => />*. qed.
lemma gen_raw9_ll :
  is_lossless gen_raw9.
  rewrite /gen_raw9 => />*. rewrite dlist_ll. rewrite gen_raw_ll => />*. qed.
lemma gen_rand_ll :
    is_lossless gen_rand.
    rewrite /gen_rand => />*. rewrite dmap_ll. rewrite gen_raw9_ll. qed.

lemma gen_raw_uni :
  is_uniform gen_raw.
  rewrite /gen_raw. rewrite funi_uni. rewrite DZmodP.dunifin_funi => />*. qed.
lemma gen_raw9_uni :
  is_uniform gen_raw9.
  rewrite /gen_raw9 dlist_uni. apply gen_raw_uni => />*. qed.
lemma gen_rand_uni :
  is_uniform gen_rand.
  rewrite /gen_rand => x y dx dy />*. have : is_uniform (dmap gen_raw9 ((Array9.of_list witness))). rewrite (dmap_uni_in_inj) => x0 y0 dx0 dy0. move => H.
  have : size x0 = 9. move :dx0. rewrite /gen_raw9 supp_dlist. smt(). progress. move => H1.
  have : size y0 = 9. move :dy0. rewrite /gen_raw9 supp_dlist. smt(). progress. move => H2.
  have : Array9.to_list (Array9.of_list witness x0) = Array9.to_list (Array9.of_list witness y0). rewrite H => />*. rewrite !of_listK => />*. apply gen_raw9_uni => />*. smt(). qed.

lemma gen_raw_fu :
  is_full gen_raw.
 proof.
  rewrite /gen_raw => />*. rewrite DZmodP.dunifin_fu => />*.
 qed.
lemma gen_raw9_fu xs :
  size xs = 9 => xs \in gen_raw9.
 proof.
  move => H. rewrite /gen_raw9 -H. rewrite dlist_fu =>x H0. rewrite gen_raw_fu => />*.
 qed.
lemma gen_rand_fu :
 is_full gen_rand.
 proof.
  rewrite /gen_rand => x />*. rewrite supp_dmap => />*. exists (Array9.to_list x) => />*. rewrite gen_raw9_fu => />*. rewrite size_to_list => />*. rewrite to_listK => />*.
 qed.


op rshare_idx (j:int) (s:val) (r:rand) : rshr =
  Array10.init (fun i => if 0 <= i < j then r.[i]
                         else if i = j then fsub s (sum_rand r)
                         else r.[i-1]).

op del_rshr (j:int) (ss:rshr) : t Array9.t =
  Array9.of_list witness (del_index j (Array10.to_list ss)).

op swap_rshr i j s rs =
  del_rshr j (rshare_idx i s rs).

lemma rshare_rshare_idx s rs :
  rshare s rs = rshare_idx 9 s rs.
  rewrite /rshare /rshare_idx => />*. rewrite Array10.tP => i domi />*. rewrite !Array10.initE !domi => />*. case (i=9). progress. move => H. have : 0 <= i && i < 9. smt(). move => H1. rewrite H1 => />*. qed.

lemma runshare_rshare_idx i s r :
  0 <= i < 10 =>
  runshare (rshare_idx i s r) = s.
  rewrite /runshare /rshare_idx => />*. rewrite array10_to_list => />*. rewrite /sum_rand => />*. rewrite array9_to_list => />*. 
  case (i=0) => />*. algebra.
  case (i=1) => />*. algebra.
  case (i=2) => />*. algebra.
  case (i=3) => />*. algebra.
  case (i=4) => />*. algebra.
  case (i=5) => />*. algebra.
  case (i=6) => />*. algebra.
  case (i=7) => />*. algebra.
  case (i=8) => />*. algebra.
  case (i=9) => />*. algebra.
  have : false. smt(). progress. qed.

lemma del_rshare_idx_id i s ss :
  0 <= i < 10 =>
  runshare ss = s =>
  rshare_idx i s (del_rshr i ss) = ss.
  rewrite /runshare /rshare_idx /del_rshr => H1 H2 />*. rewrite Array10.tP => i0 domi0 />*. rewrite Array10.initE andabP andaP. move : domi0. progress. move :domi0. progress. case (i0 < i). move => H.
  rewrite Array9.initE => />*. have : 0 <= i0 && i0 < 9. smt(). move => H3. rewrite H3 => />*. rewrite /del_index nth_cat => />*. rewrite size_take => />*. move :H1. progress. rewrite Array10.size_to_list => />*. rewrite andabP H => />*. move :H3. progress. rewrite H0 => />*. rewrite nth_take => />*. move :H1. progress. move :H1. progress. rewrite H4 H => />*. 
  move => H3. case (i0=i). move => H4. rewrite -H2. rewrite array10_to_list /sum_rand array9_to_list => />*. move :domi0. progress. rewrite H H3 => />*. rewrite /del_index !nth_cat => />*. rewrite !H4.
  case (i=0) => />*. algebra.
  case (i=1) => />*. algebra.
  case (i=2) => />*. algebra.
  case (i=3) => />*. algebra.
  case (i=4) => />*. algebra.
  case (i=5) => />*. algebra.
  case (i=6) => />*. algebra.
  case (i=7) => />*. algebra.
  case (i=8) => />*. algebra.
  case (i=9) => />*. algebra.
  have : false. smt(). progress.
  move => H4. have : !(0 <= i0 && i0 < i). smt(). move => H5. rewrite H5 => />*. rewrite /del_index array10_to_list => />*. rewrite Array9.initiE => />*. smt().
  rewrite nth_cat => />*. 
  case (i=0) => />*. smt().
  case (i=1) => />*. smt().
  case (i=2) => />*. smt().
  case (i=3) => />*. smt(). 
  case (i=4) => />*. smt().
  case (i=5) => />*. smt().
  case (i=6) => />*. smt().
  case (i=7) => />*. smt().
  case (i=8) => />*. smt().
  case (i=9) => />*. smt().
  have : false. smt(). progress. qed.

lemma rshare_idx_del_id i s r :
  0 <= i < 10 =>
  del_rshr i (rshare_idx i s r) = r.
  rewrite /del_rshr /rshare_idx. progress. rewrite Array9.tP. progress. rewrite Array9.get_of_list /del_index. progress. rewrite nth_cat size_take. progress. rewrite Array10.size_to_list. rewrite H0 => />*. case (i0 < i). move => H3. rewrite nth_take => />*. rewrite Array10.initE andabP andaP. progress. smt(). simplify. rewrite andabP andaP => />*. move => H3. 
  rewrite nth_drop => />*. smt(). rewrite Array10.size_to_list => />*. smt().
  rewrite Array10.initE => />*. smt(). qed.

lemma swap_rshr_id i j s r :
  0 <= i < 10 =>
  0 <= j < 10 =>
  swap_rshr j i s (swap_rshr i j s r) = r.
  rewrite /swap_rshr => />*. rewrite del_rshare_idx_id => />*. rewrite runshare_rshare_idx => />*. rewrite rshare_idx_del_id => />*. qed.

module RawSecurity = {
  proc real(s:val,i j:int) = {
    var rs;
    rs <$ gen_rand;
    return swap_rshr i j s rs;
  }  
  proc ideal(s:val,i j:int) = {
    var rs;
    rs <$ gen_rand;
    return rs;
  }
}.

(* 9-out-of-10 security *)
lemma raw_security :
  equiv [RawSecurity.real ~ RawSecurity.ideal : 0 <= i{1} < 10 /\ 0 <= j{1} < 10 /\ ={s,i,j} ==> ={res} ].
  proc. simplify. wp. rnd (swap_rshr i{1} j{1} s{1}) (swap_rshr j{1} i{1} s{1}). auto. progress.
  rewrite swap_rshr_id => />*.
  apply gen_rand_uni => />*. 
  rewrite gen_rand_fu => />*. 
  rewrite gen_rand_fu => />*. 
  rewrite swap_rshr_id =>/>*. qed.

op cr_missings (cr:int list) : int fset =
  let idxs = foldr (fun i s => FSet.oflist (shr_idx i) `|` s) fset0 cr in
  FSet.oflist shr_idxs `\` idxs.

op cr_missing (cr:int list) : int =
  pick (cr_missings cr).

lemma size_shr_idx p :
  0 <= p < 5 => size (shr_idx p) = 6.
  rewrite /shr_idx => />*. case (p=0) => />*. case (p=1) => />*. case (p=2) => />*. case (p=3) => />*. case (p=4) => />*. have : false. smt() => />*. progress. qed.

lemma rng_shr_idx i p :
  (0 <= i < 6 /\ 0 <= p < 5) => 0 <= nth witness (shr_idx p) i < 10.
  rewrite /shr_idx => />*.
  case (p=0) => />*. case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. have : i=5. smt(). smt().
  case (p=1) => />*. case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. have : i=5. smt(). smt().
  case (p=2) => />*. case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. have : i=5. smt(). smt().
  case (p=3) => />*. case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. have : i=5. smt(). smt().
  have : p=4. smt(). case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. have : i=5. smt(). smt(). qed.

lemma shr_idx_nth_0 i :
  0 <= i < 5 => nth witness (shr_idx i) 0 = nth witness [5;1;6;3;7] i.
  rewrite /shr_idx => />*. case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. have : false. smt(). progress. qed.

lemma shr_idx_nth_1 i :
  0 <= i < 5 => nth witness (shr_idx i) 1 = nth witness [9;2;0;8;4] i.
  rewrite /shr_idx => />*. case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. have : false. smt(). progress. qed.

lemma shr_idx_nth_2 i :
  0 <= i < 5 => nth witness (shr_idx i) 2 = nth witness [8;9;2;4;0] i.
  rewrite /shr_idx => />*. case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. have : false. smt(). progress. qed.

lemma shr_idx_nth_3 i :
  0 <= i < 5 => nth witness (shr_idx i) 3 = nth witness [7;3;5;6;1] i.
  rewrite /shr_idx => />*. case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. have : false. smt(). progress. qed.

lemma shr_idx_nth_4 i :
  0 <= i < 5 => nth witness (shr_idx i) 4 = nth witness [4;8;9;0;2] i.
  rewrite /shr_idx => />*. case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. have : false. smt(). progress. qed.

lemma shr_idx_nth_5 i :
  0 <= i < 5 => nth witness (shr_idx i) 5 = nth witness [6;7;3;1;5] i.
  rewrite /shr_idx => />*. case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. have : false. smt(). progress. qed.

op pids = iseq 5.
op corrupted (cr : pid list) : bool = 
    size cr = 2 /\ uniq cr /\ (forall pid, pid \in cr => pid \in pids).

lemma cr_ind cr (P: int list -> bool) :
  corrupted cr =>
  P [0;1] =>
  P [0;2] =>
  P [0;3] =>
  P [0;4] =>
  P [1;2] =>
  P [1;3] =>
  P [1;4] =>
  P [2;3] =>
  P [2;4] =>
  P [3;4] =>
  (forall x y, x <> y => x \in cr => y \in cr => P[x;y] = P[y;x]) =>
  P cr.
  rewrite /corrupted /t. progress. move :H0 H1 H12. rewrite (size2E cr). progress.
  case (nth witness cr 0=0). move => cr00. progress.
  case (nth witness cr 1=1). move => cr11. progress. rewrite cr00 cr11 => />*.
  case (nth witness cr 1=2). move => cr12. progress. rewrite cr00 cr12 => />*. 
  case (nth witness cr 1=3). move => cr13. progress. rewrite cr00 cr13 => />*. 
  case (nth witness cr 1=4). move => cr14. progress. rewrite cr00 cr14 => />*. 
  progress. have : false. have : nth witness cr 1 \in pids. apply H1 => />*. rewrite in_iseq => />*. smt(). progress.
  case (nth witness cr 0=1). move => cr01. progress.
  case (nth witness cr 1=0). move => cr10. rewrite cr01 cr10 => />*. smt().
  case (nth witness cr 1=2). move => cr12. rewrite cr01 cr12 => />*.
  case (nth witness cr 1=3). move => cr13. rewrite cr01 cr13 => />*.
  case (nth witness cr 1=4). move => cr14. rewrite cr01 cr14 => />*.
  progress. have : false. have : nth witness cr 1 \in pids. apply H12 => />*. rewrite in_iseq => />*. smt(). progress.
  case (nth witness cr 0=2). move => cr02. progress. 
  case (nth witness cr 1=0). move => cr10. rewrite cr02 cr10 => />*. smt().
  case (nth witness cr 1=1). move => cr11. rewrite cr02 cr11 => />*. smt().
  case (nth witness cr 1=3). move => cr13. rewrite cr02 cr13 => />*.
  case (nth witness cr 1=4). move => cr14. rewrite cr02 cr14 => />*.
  progress. have : false. have : nth witness cr 1 \in pids. apply H13 => />*. rewrite in_iseq => />*. smt(). progress.
  case (nth witness cr 0=3). move => cr03. progress.
  case (nth witness cr 1=0). move => cr10. rewrite cr03 cr10 => />*. smt().
  case (nth witness cr 1=1). move => cr11. rewrite cr03 cr11 => />*. smt().
  case (nth witness cr 1=2). move => cr12. rewrite cr03 cr12 => />*. smt().
  case (nth witness cr 1=4). move => cr14. rewrite cr03 cr14 => />*.
  progress. have : false. have : nth witness cr 1 \in pids. apply H14 => />*. rewrite in_iseq => />*. smt(). progress.
  case (nth witness cr 0=4). move => cr04. progress.
  case (nth witness cr 1=0). move => cr10. rewrite cr04 cr10 => />*. smt().
  case (nth witness cr 1=1). move => cr11. rewrite cr04 cr11 => />*. smt().
  case (nth witness cr 1=2). move => cr12. rewrite cr04 cr12 => />*. smt().
  case (nth witness cr 1=3). move => cr13. rewrite cr04 cr13 => />*. smt().
  progress. have : false. have : nth witness cr 1 \in pids. apply H15 => />*. rewrite in_iseq => />*. smt(). progress.
  progress. have : false. have : nth witness cr 0 \in pids. apply H16 => />*. rewrite in_iseq => />*. smt(). progress. qed.

lemma cr_ind' cr (P: int list -> bool) :
  corrupted cr =>
  P [0;1] =>
  P [0;2] =>
  P [0;3] =>
  P [0;4] =>
  P [1;2] =>
  P [1;3] =>
  P [1;4] =>
  P [2;3] =>
  P [2;4] =>
  P [3;4] =>
  P [1;0] =>
  P [2;0] =>
  P [3;0] =>
  P [4;0] =>
  P [2;1] =>
  P [3;1] =>
  P [4;1] =>
  P [3;2] =>
  P [4;2] =>
  P [4;3] =>
  P cr.
  rewrite /corrupted /t. progress. move :H0 H1 H12. rewrite (size2E cr). progress.
  case (nth witness cr 0=0). move => cr00. progress.
  case (nth witness cr 1=1). move => cr11. progress. rewrite cr00 cr11 => />*.
  case (nth witness cr 1=2). move => cr12. progress. rewrite cr00 cr12 => />*. 
  case (nth witness cr 1=3). move => cr13. progress. rewrite cr00 cr13 => />*. 
  case (nth witness cr 1=4). move => cr14. progress. rewrite cr00 cr14 => />*. 
  progress. have : false. have : nth witness cr 1 \in pids. apply H1 => />*. rewrite in_iseq => />*. smt(). progress.
  case (nth witness cr 0=1). move => cr01. progress.
  case (nth witness cr 1=0). move => cr10. rewrite cr01 cr10 => />*. 
  case (nth witness cr 1=2). move => cr12. rewrite cr01 cr12 => />*.
  case (nth witness cr 1=3). move => cr13. rewrite cr01 cr13 => />*.
  case (nth witness cr 1=4). move => cr14. rewrite cr01 cr14 => />*.
  progress. have : false. have : nth witness cr 1 \in pids. apply H12 => />*. rewrite in_iseq => />*. smt(). progress.
  case (nth witness cr 0=2). move => cr02. progress. 
  case (nth witness cr 1=0). move => cr10. rewrite cr02 cr10 => />*. 
  case (nth witness cr 1=1). move => cr11. rewrite cr02 cr11 => />*. 
  case (nth witness cr 1=3). move => cr13. rewrite cr02 cr13 => />*.
  case (nth witness cr 1=4). move => cr14. rewrite cr02 cr14 => />*.
  progress. have : false. have : nth witness cr 1 \in pids. apply H22 => />*. rewrite in_iseq => />*. smt(). progress.
  case (nth witness cr 0=3). move => cr03. progress.
  case (nth witness cr 1=0). move => cr10. rewrite cr03 cr10 => />*. 
  case (nth witness cr 1=1). move => cr11. rewrite cr03 cr11 => />*. 
  case (nth witness cr 1=2). move => cr12. rewrite cr03 cr12 => />*. 
  case (nth witness cr 1=4). move => cr14. rewrite cr03 cr14 => />*.
  progress. have : false. have : nth witness cr 1 \in pids. apply H23 => />*. rewrite in_iseq => />*. smt(). progress.
  case (nth witness cr 0=4). move => cr04. progress.
  case (nth witness cr 1=0). move => cr10. rewrite cr04 cr10 => />*. 
  case (nth witness cr 1=1). move => cr11. rewrite cr04 cr11 => />*. 
  case (nth witness cr 1=2). move => cr12. rewrite cr04 cr12 => />*. 
  case (nth witness cr 1=3). move => cr13. rewrite cr04 cr13 => />*. 
  progress. have : false. have : nth witness cr 1 \in pids. apply H24 => />*. rewrite in_iseq => />*. smt(). progress.
  progress. have : false. have : nth witness cr 0 \in pids. apply H25 => />*. rewrite in_iseq => />*. smt(). progress. qed.

lemma cr_missings_ne0 cr :
  corrupted cr =>
  cr_missings cr <> fset0.
  move => ?. rewrite (_:(cr_missings cr <> fset0)=(fun cr => cr_missings cr <> fset0) cr). progress. apply cr_ind => />*.
  rewrite /cr_missings /shr_idxs /shr_idx iseq_10 => />*. rewrite !oflist_cons !oflist_nil => />*. rewrite !fsetU0 => />*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 => />*. smt(@FSet).
  rewrite /cr_missings /shr_idxs /shr_idx iseq_10 => />*. rewrite !oflist_cons !oflist_nil => />*. rewrite !fsetU0 => />*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 => />*. smt(@FSet).
  rewrite /cr_missings /shr_idxs /shr_idx iseq_10 => />*. rewrite !oflist_cons !oflist_nil => />*. rewrite !fsetU0 => />*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 => />*. smt(@FSet).
  rewrite /cr_missings /shr_idxs /shr_idx iseq_10 => />*. rewrite !oflist_cons !oflist_nil => />*. rewrite !fsetU0 => />*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 => />*. smt(@FSet).
  rewrite /cr_missings /shr_idxs /shr_idx iseq_10 => />*. rewrite !oflist_cons !oflist_nil => />*. rewrite !fsetU0 => />*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 => />*. smt(@FSet).
  rewrite /cr_missings /shr_idxs /shr_idx iseq_10 => />*. rewrite !oflist_cons !oflist_nil => />*. rewrite !fsetU0 => />*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 => />*. smt(@FSet).
  rewrite /cr_missings /shr_idxs /shr_idx iseq_10 => />*. rewrite !oflist_cons !oflist_nil => />*. rewrite !fsetU0 => />*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U => />*. smt(@FSet).
  rewrite /cr_missings /shr_idxs /shr_idx iseq_10 => />*. rewrite !oflist_cons !oflist_nil => />*. rewrite !fsetU0 => />*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U => />*. smt(@FSet).
  rewrite /cr_missings /shr_idxs /shr_idx iseq_10 => />*. rewrite !oflist_cons !oflist_nil => />*. rewrite !fsetU0 => />*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U => />*. smt(@FSet).
  rewrite /cr_missings /shr_idxs /shr_idx iseq_10 => />*. rewrite !oflist_cons !oflist_nil => />*. rewrite !fsetU0 => />*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U => />*. smt(@FSet).
  rewrite /cr_missings => />*. rewrite !fsetU0 => />*. rewrite fsetUC => />*. qed.
  
lemma dom_cr_missing cr :
  corrupted cr => 0 <= cr_missing cr < 10.
  rewrite /corrupted. move => H.
  have : cr_missing cr \in shr_idxs. rewrite /cr_missing. rewrite -mem_oflist. apply pick_subset.
  rewrite cr_missings_ne0. progress. progress. rewrite subsetP /(<=) => H2 H3. 
  rewrite mem_oflist. move :H3. rewrite /cr_missings. progress. move :H0. rewrite in_fsetD mem_oflist => />*. rewrite in_iseq => />*. qed.

module SSSecurity = {
  proc real(s:val,cr : int list) = {
    var r,ss,ssc;
    r <$ gen_rand;
    ss <- share s r;
    ssc <- map (fun pid => (pid,ss.[pid])) cr;
    return ssc;
  }
  proc ideal(s:val,cr: int list) = {
    var r,i,rs,ss,ssc;
    r <$ gen_rand;
    i <- cr_missing cr;
    rs <- rshare_idx i witness r;
    ss <- Array5.init (fun i => init_sh i rs);
    ssc <- map (fun pid => (pid,ss.[pid])) cr;
    return ssc;
  }
  proc ideal2(s:val,cr:int list) = {
    var rss, rs,ss,ssc;
    rss <@ RawSecurity.real(s,cr_missing cr,9);
    rs <- rshare_idx 9 s rss;
    ss <- Array5.init (transpose init_sh rs);
    ssc <- map (fun pid => (pid, ss.[pid])) cr;
    return ssc;
  }
}.

lemma init_sh_missing pid i s1 s2 r :
  0 <= pid < 5 =>
  0 <= i < 10 =>
  ! (i \in shr_idx pid) =>
  init_sh pid (rshare_idx i s1 r) = init_sh pid (rshare_idx i s2 r).
  rewrite /init_sh. progress. rewrite Array6.tP. progress. rewrite !Array6.get_of_list => />*. rewrite !(nth_map witness). rewrite size_shr_idx => />*. rewrite size_shr_idx => />*. 
  rewrite /rshare_idx => />*. rewrite !Array10.initE => />*. rewrite !rng_shr_idx => />*. 
  case (0 <= nth witness (shr_idx pid) i0 && nth witness (shr_idx pid) i0 < i). move => H6. progress.
  case (nth witness (shr_idx pid) i0 = i). progress.
  rewrite nth_in in H3 => />*. rewrite size_shr_idx => />*. progress. qed.

lemma shr_idx_missing (pid:int) (cr:int list) :
  corrupted cr =>
  pid \in cr =>
  ! (cr_missing cr \in shr_idx pid).
  rewrite /cr_missing. progress. have : pick (cr_missings cr) \in (oflist shr_idxs `\` foldr (fun (i : pid) (s : int fset) => oflist (shr_idx i) `|` s) fset0 cr). rewrite mem_pick => />*. have : cr_missings cr <> fset0. rewrite cr_missings_ne0 => />*. rewrite /cr_missings => />*.
  rewrite in_fsetD. move :H. rewrite /corrupted. progress. move :H0 H1 H2 H3 H4. rewrite (size2E cr). progress. progress. rewrite !in_fsetU in_fset0 in H4 => />*. rewrite !mem_oflist in H4 => />*. smt(). qed.

lemma ss_ideal :
  equiv [SSSecurity.ideal ~ SSSecurity.ideal : corrupted cr{1} /\ ={cr} ==> ={res} ].
  proc. simplify. wp. rnd => />*. auto => />*. qed.


(* security against 2 corrupted parties *)
lemma ss_security :
  equiv [SSSecurity.real ~ SSSecurity.ideal : corrupted cr{1} /\ ={s,cr} ==> ={res} ].
  proc. simplify.
  transitivity{2}
    { ssc <@ SSSecurity.ideal2(s,cr); }
    ( corrupted cr{1} /\ ={s, cr} ==> ={ssc} )
    ( corrupted cr{1} /\ ={s, cr} ==> ={ssc} ).
    progress. exists cr{2} s{2} => />*.
    progress.
  inline SSSecurity.ideal2. sp.
  seq 1 1 : (#pre /\ r{1}=rss{2}). symmetry.
  transitivity{2}
    { r <@ RawSecurity.ideal(s,cr_missing cr,9); }
    ( corrupted cr{1} /\ s0{1}=s{1} /\ cr0{1}=cr{1} /\ ={s,cr} ==> corrupted cr{1} /\ s0{1}=s{1} /\ cr0{1}=cr{1} /\ ={s,cr} /\ rss{1}=r{2} )
    ( corrupted cr{1} /\ ={s,cr} ==> corrupted cr{1} /\ ={s,cr,r} ).
    progress. exists cr{1} s{1} => />*.
    progress.
  call raw_security => />*. auto. move => &1 &2 H. have : 0 <= cr_missing cr{2} < 10. rewrite dom_cr_missing => />*. move :H. rewrite /corrupted => />*. smt(). 
  inline *. sp. wp. rnd => />*. auto => />*.
  wp. auto => />*. apply (eq_from_nth witness). rewrite !size_map => />*. rewrite !size_map => />*. rewrite !(nth_map witness) /share => />*. rewrite rshare_rshare_idx => />*. 
  inline *. sp. wp. rnd. auto. progress. move :H H0. rewrite H1. rewrite /corrupted. progress.
  apply (eq_from_nth witness). rewrite !size_map => />*. rewrite !size_map. progress. rewrite !(nth_map witness) /swap_rshr => />*. rewrite del_rshare_idx_id => />*. rewrite runshare_rshare_idx. rewrite dom_cr_missing => />*. trivial.
  rewrite !Array5.initE. progress. have : nth witness cr{2} i1 \in pids. rewrite H2 => />*. rewrite nth_in => />*. move => H5. have : 0 <= nth witness cr{2} i1 && nth witness cr{2} i1 < 5. move :H5. rewrite in_iseq => />*. move => H6. rewrite !H6 => />*. apply init_sh_missing. rewrite H6. rewrite dom_cr_missing => />*. rewrite shr_idx_missing => />*. rewrite nth_in => />*. qed.

(* raw shares *)

op raw_shares' (i:pid) (s:shr) (raws:(int,t) fmap) : (int,t) fmap =
  foldl_iseq (fun  (m:(int,t) fmap) k => let j = nth witness (shr_idx i) k in m.[j <- s.[k] ] ) raws 6.

op raw_shares (i:pid) (s:shr) : (int,t) fmap =
  raw_shares' i s empty.

op raws_shares (ss:shrs) : (int,t) fmap =
  foldl_iseq (fun raws i => raw_shares' i ss.[i] raws) empty 5.

op rand_shares (ss:shrs) : t Array9.t =
  Array9.of_list witness
    [ss.[2].[1] (*0*)
    ;ss.[1].[0] (*1*)
    ;ss.[1].[1] (*2*)
    ;ss.[1].[3] (*3*)
    ;ss.[0].[4] (*4*)
    ;ss.[0].[0] (*5*)
    ;ss.[0].[5] (*6*)
    ;ss.[0].[3] (*7*)
    ;ss.[0].[2] (*8*)
    ].

op consistent_raw_shares (i j:pid) (s1 s2 : shr) : bool =
  fall (fun _ (xy:_*_) => xy.`1 = xy.`2) (fzip (raw_shares i s1) (raw_shares j s2)).

lemma dom_raw_shares i ss :
  0 <= i < 5 =>
  fdom (raw_shares i ss) = oflist (shr_idx i).
  rewrite /raw_shares /raw_shares' foldl_iseqE !iseq_6 /shr_idx => |>H.
  case (i=0) => |>. rewrite !fdom_set !fdom_empty fset0U => |>. rewrite fsetP => |>x.
  rewrite !in_fsetU !in_fset1 !mem_oflist => |>. smt().
  case (i=1) => |>. rewrite !fdom_set !fdom_empty fset0U => |>. rewrite fsetP => |>x.
  rewrite !in_fsetU !in_fset1 !mem_oflist => |>*. smt().
  case (i=2) => |>. rewrite !fdom_set !fdom_empty fset0U => |>. rewrite fsetP => |>x.
  rewrite !in_fsetU !in_fset1 !mem_oflist => |>*. smt().
  case (i=3) => |>. rewrite !fdom_set !fdom_empty fset0U => |>. rewrite fsetP => |>x.
  rewrite !in_fsetU !in_fset1 !mem_oflist => |>*. smt().
  case (i=4) => |>. rewrite !fdom_set !fdom_empty fset0U => |>. rewrite fsetP => |>x.
  rewrite !in_fsetU !in_fset1 !mem_oflist => |>*. smt().
  progress. have : false. smt(). progress. qed.

op shr_idx_inv (p:pid) (idx:int) =
  oget (assoc (zip (Maurer5SS.shr_idx p) (iseq 6)) idx).

lemma raw_shares_inv i x a :
  0 <= i < 5 =>
  a \in shr_idx i =>
  oget (raw_shares i x).[a] = x.[shr_idx_inv i a].
  rewrite !/raw_shares /raw_shares' /shr_idx_inv /shr_idx foldl_iseqE !iseq_6 /parties. progress. move :H1. 
  case (i=0) => |>Hi0. rewrite /get_rshr !assoc_cons => |>. elim Hi0 => |>.  rewrite !get_setE => |>*. move => Hi0. elim Hi0 => |>. rewrite !get_setE => |>*. move => Hi0. elim Hi0 => |>. rewrite !get_setE => |>*. move => Hi0. elim Hi0 => |>. rewrite !get_setE => |>*. move => Hi0. elim Hi0 => |>. rewrite !get_setE => |>*. rewrite !get_setE => |>*.
  case (i=1) => |>Hi1. rewrite /get_rshr !assoc_cons => |>. elim Hi1 => |>.  rewrite !get_setE => |>*. move => Hi1. elim Hi1 => |>. rewrite !get_setE => |>*. move => Hi1. elim Hi1 => |>. rewrite !get_setE => |>*. move => Hi1. elim Hi1 => |>. rewrite !get_setE => |>*. move => Hi1. elim Hi1 => |>. rewrite !get_setE => |>*. rewrite !get_setE => |>*.
  case (i=2) => |>Hi2. rewrite /get_rshr !assoc_cons => |>. elim Hi2 => |>.  rewrite !get_setE => |>*. move => Hi2. elim Hi2 => |>. rewrite !get_setE => |>*. move => Hi2. elim Hi2 => |>. rewrite !get_setE => |>*. move => Hi2. elim Hi2 => |>. rewrite !get_setE => |>*. move => Hi2. elim Hi2 => |>. rewrite !get_setE => |>*. rewrite !get_setE => |>*.
  case (i=3) => |>Hi3. rewrite /get_rshr !assoc_cons => |>. elim Hi3 => |>.  rewrite !get_setE => |>*. move => Hi3. elim Hi3 => |>. rewrite !get_setE => |>*. move => Hi3. elim Hi3 => |>. rewrite !get_setE => |>*. move => Hi3. elim Hi3 => |>. rewrite !get_setE => |>*. move => Hi3. elim Hi3 => |>. rewrite !get_setE => |>*. rewrite !get_setE => |>*.
  case (i=4) => |>Hi4. rewrite /get_rshr !assoc_cons => |>. elim Hi4 => |>.  rewrite !get_setE => |>*. move => Hi4. elim Hi4 => |>. rewrite !get_setE => |>*. move => Hi4. elim Hi4 => |>. rewrite !get_setE => |>*. move => Hi4. elim Hi4 => |>. rewrite !get_setE => |>*. move => Hi4. elim Hi4 => |>. rewrite !get_setE => |>*. rewrite !get_setE => |>*.
  have : false. smt(). progress. qed.

lemma dom_shr_idx_inv i a :
  0 <= i < 5 =>
  a \in (shr_idx i) =>
  0 <= shr_idx_inv i a < 6.
  rewrite /shr_idx_inv /shr_idx !iseq_6 => H.
  case (i=0) => |>Hi0. rewrite !assoc_cons => |>. elim Hi0 => |>. move => Hi0. elim Hi0 => |>. move => Hi0. elim Hi0 => |>. move => Hi0. elim Hi0 => |>. move => Hi0. elim Hi0 => |>.
  case (i=1) => |>Hi1. rewrite !assoc_cons => |>. elim Hi1 => |>. move => Hi1. elim Hi1 => |>. move => Hi1. elim Hi1 => |>. move => Hi1. elim Hi1 => |>. move => Hi1. elim Hi1 => |>.
  case (i=2) => |>Hi2. rewrite !assoc_cons => |>. elim Hi2 => |>. move => Hi2. elim Hi2 => |>. move => Hi2. elim Hi2 => |>. move => Hi2. elim Hi2 => |>. move => Hi2. elim Hi2 => |>.
  case (i=3) => |>Hi3. rewrite !assoc_cons => |>. elim Hi3 => |>. move => Hi3. elim Hi3 => |>. move => Hi3. elim Hi3 => |>. move => Hi3. elim Hi3 => |>. move => Hi3. elim Hi3 => |>.
  case (i=4) => |>Hi4. rewrite !assoc_cons => |>. elim Hi4 => |>. move => Hi4. elim Hi4 => |>. move => Hi4. elim Hi4 => |>. move => Hi4. elim Hi4 => |>. move => Hi4. elim Hi4 => |>.
  have : false. smt(). progress. qed.

lemma nth_shr_idx_shr_idx_inv i a :
  0 <= i < 5 =>
  a \in shr_idx i => 
  (nth witness (shr_idx i) (shr_idx_inv i a)) = a.
  rewrite /shr_idx_inv !iseq_6 => |>. progress. move :H1. rewrite /shr_idx => |>H1.
  case (i=0) => |>*. move :H1. progress. case (a=5) => |>*. case (a=9) => |>*. case (a=8) => |>*. case (a=7) => |>*. case (a=4) => |>*. case (a=6) => |>*. have : false. smt(). progress.
  case (i=1) => |>*. move :H1. progress. case (a=1) => |>*. case (a=2) => |>*. case (a=9) => |>*. case (a=3) => |>*. case (a=8) => |>*. case (a=7) => |>*. have : false. smt(). progress.
  case (i=2) => |>*. move :H1. progress. case (a=6) => |>*. case (a=0) => |>*. case (a=2) => |>*. case (a=5) => |>*. case (a=9) => |>*. case (a=3) => |>*. have : false. smt(). progress.
  case (i=3) => |>*. move :H1. progress. case (a=3) => |>*. case (a=8) => |>*. case (a=4) => |>*. case (a=6) => |>*. case (a=0) => |>*. case (a=1) => |>*. have : false. smt(). progress.
  case (i=4) => |>*. move :H1. progress. case (a=7) => |>*. case (a=4) => |>*. case (a=0) => |>*. case (a=1) => |>*. case (a=2) => |>*. case (a=5) => |>*. have : false. smt(). progress.
  have : false. smt(). progress. qed.

lemma consistent_raw_shares_share i j v r :
  0 <= i < 5 => 0 <= j < 5 =>
  consistent_raw_shares i j (share v r).[i] (share v r).[j].
  rewrite /consistent_raw_shares fallP => |>. move => Hi1 Hi2 Hj1 Hj2 a. rewrite fdom_fzip in_fsetI !dom_raw_shares => |>. rewrite !mem_oflist => |>Hi Hj. rewrite !fzip_some => |>*. rewrite !dom_raw_shares => |>*. rewrite in_fsetI !mem_oflist => |>*. rewrite !raw_shares_inv /share => |>*.
  rewrite !Array5.initE /init_sh !andabP !andaP => |>*. rewrite !Array6.initE. rewrite !dom_shr_idx_inv => |>*. rewrite !(nth_map witness). rewrite size_shr_idx. rewrite andabP andaP => |>. rewrite dom_shr_idx_inv => |>*. rewrite size_shr_idx. rewrite andabP andaP => |>. rewrite dom_shr_idx_inv => |>*. 
  rewrite !nth_shr_idx_shr_idx_inv => |>*. qed.

lemma consistent_raw_shares_share' i j v r :
  0 <= i < 5 => 0 <= j < 5 =>
  consistent_raw_shares i j (init_sh i (rshare v r)) (init_sh j (rshare v r)).
  move => H1 H2. have : consistent_raw_shares i j (share v r).[i] (share v r).[j]. rewrite consistent_raw_shares_share => |>. rewrite /share => |>. rewrite !initE => |>. rewrite H1 H2 => |>. qed.

lemma dom_raw_shares_0_1 i s1 s2 :
    i \in fdom (fzip (raw_shares 0 s1) (raw_shares 1 s2)) = 7 <= i <= 9.
    rewrite fdom_fzip => />*. rewrite !/raw_shares /raw_shares' foldl_iseqE !iseq_6 /shr_idx => />*. rewrite !fdom_set => />*. rewrite !in_fsetI !in_fsetU !in_fset1 => />*. rewrite !fdom_empty !in_fset0 => />*. rewrite foldl_iseqE iseq_6 => />.
    rewrite /set /get_rshr !fdom_set !fdom_empty !in_fsetU !in_fset0 !in_fset1 !/shr_idx => />. rewrite /shr_idx =>/>. smt(). qed.

  lemma dom_raw_shares_0_2 i s0 s2 :
    i \in fdom (fzip (raw_shares 0 s0) (raw_shares 2 s2)) = (i=5 \/ i=6 \/ i=9).
    rewrite fdom_fzip => />*. rewrite !/raw_shares /raw_shares' foldl_iseqE !iseq_6 !/shr_idx => />*. rewrite !/set !/empty !fdom_set => />*. rewrite !in_fsetI !in_fsetU !in_fset1 => />*. rewrite !fdom_empty !in_fset0 => />*. rewrite foldl_iseqE iseq_6 => />. rewrite !/set !/get_rshr !fdom_set !fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite /shr_idx =>/>. smt(). qed.

  lemma dom_raw_shares_0_3 i s0 s3 :
    i \in fdom (fzip (raw_shares 0 s0) (raw_shares 3 s3)) = (i=4 \/ i=6 \/ i=8).
    rewrite fdom_fzip => />*. rewrite !/raw_shares /raw_shares' foldl_iseqE !iseq_6 !/shr_idx => />*. rewrite !/set !/empty !fdom_set => />*. rewrite !in_fsetI !in_fsetU !in_fset1 => />*. rewrite !fdom_empty !in_fset0 => />*. rewrite foldl_iseqE iseq_6 => />. rewrite !/set !/get_rshr !fdom_set !fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite /shr_idx =>/>. smt(). qed.

  lemma dom_raw_shares_0_4 i s0 s4 :
    i \in fdom (fzip (raw_shares 0 s0) (raw_shares 4 s4)) = (i=4 \/ i=5 \/ i=7).
    rewrite fdom_fzip => />*. rewrite !/raw_shares /raw_shares' foldl_iseqE !iseq_6 !/shr_idx => />*. rewrite !/set !/empty !fdom_set => />*. rewrite !in_fsetI !in_fsetU !in_fset1 => />*. rewrite !fdom_empty !in_fset0 => />*. rewrite foldl_iseqE iseq_6 => />. rewrite !/set !/get_rshr !fdom_set !fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite /shr_idx =>/>. smt(). qed.

  lemma dom_raw_shares_1_2 i s1 s2 :
    i \in fdom (fzip (raw_shares 1 s1) (raw_shares 2 s2)) = (i=2 \/ i=3 \/ i=9).
    rewrite fdom_fzip => />*. rewrite !/raw_shares /raw_shares' foldl_iseqE !iseq_6 !/shr_idx => />*. rewrite !/set !/empty !fdom_set => />*. rewrite !in_fsetI !in_fsetU !in_fset1 => />*. rewrite !fdom_empty !in_fset0 => />*. rewrite foldl_iseqE iseq_6 => />. rewrite !/set !/get_rshr !fdom_set !fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite /shr_idx =>/>. smt(). qed.

  lemma dom_raw_shares_1_3 i s1 s3 :
    i \in fdom (fzip (raw_shares 1 s1) (raw_shares 3 s3)) = (i=1 \/ i=3 \/ i=8).
    rewrite fdom_fzip => />*. rewrite !/raw_shares /raw_shares' foldl_iseqE !iseq_6 !/shr_idx => />*. rewrite !/set !/empty !fdom_set => />*. rewrite !in_fsetI !in_fsetU !in_fset1 => />*. rewrite !fdom_empty !in_fset0 => />*. rewrite foldl_iseqE iseq_6 => />. rewrite !/set !/get_rshr !fdom_set !fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite /shr_idx =>/>. smt(). qed.

  lemma dom_raw_shares_1_4 i s1 s4 :
    i \in fdom (fzip (raw_shares 1 s1) (raw_shares 4 s4)) = (i=1 \/ i=2 \/ i=7).
    rewrite fdom_fzip => />*. rewrite !/raw_shares /raw_shares' foldl_iseqE !iseq_6 !/shr_idx => />*. rewrite !/set !/empty !fdom_set => />*. rewrite !in_fsetI !in_fsetU !in_fset1 => />*. rewrite !fdom_empty !in_fset0 => />*. rewrite foldl_iseqE iseq_6 => />. rewrite !/set !/get_rshr !fdom_set !fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite /shr_idx =>/>. smt(). qed.

  lemma dom_raw_shares_2_3 i s2 s3 :
    i \in fdom (fzip (raw_shares 2 s2) (raw_shares 3 s3)) = (i=0 \/ i=3 \/ i=6).
    rewrite fdom_fzip => />*. rewrite !/raw_shares /raw_shares' foldl_iseqE !iseq_6 !/shr_idx => />*. rewrite !/set !/empty !fdom_set => />*. rewrite !in_fsetI !in_fsetU !in_fset1 => />*. rewrite !fdom_empty !in_fset0 => />*. rewrite foldl_iseqE iseq_6 => />. rewrite !/set !/get_rshr !fdom_set !fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite /shr_idx =>/>. smt(). qed.

  lemma dom_raw_shares_2_4 i s2 s4 :
    i \in fdom (fzip (raw_shares 2 s2) (raw_shares 4 s4)) = (i=0 \/ i=2 \/ i=5).
    rewrite fdom_fzip => />*. rewrite !/raw_shares /raw_shares' foldl_iseqE !iseq_6 !/shr_idx => />*. rewrite !/set !/empty !fdom_set => />*. rewrite !in_fsetI !in_fsetU !in_fset1 => />*. rewrite !fdom_empty !in_fset0 => />*. rewrite foldl_iseqE iseq_6 => />. rewrite !/set !/get_rshr !fdom_set !fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite /shr_idx =>/>. smt(). qed.

  lemma dom_raw_shares_3_4 i s3 s4 :
    i \in fdom (fzip (raw_shares 3 s3) (raw_shares 4 s4)) = (i=0 \/ i=1 \/ i=4).
    rewrite fdom_fzip => />*. rewrite !/raw_shares /raw_shares' foldl_iseqE !iseq_6 !/shr_idx => />*. rewrite !/set !/empty !fdom_set => />*. rewrite !in_fsetI !in_fsetU !in_fset1 => />*. rewrite !fdom_empty !in_fset0 => />*. rewrite foldl_iseqE iseq_6 => />. rewrite !/set !/get_rshr !fdom_set !fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite /shr_idx =>/>. smt(). qed.

lemma consistent_s00_s23 s0 s2 :
    consistent_raw_shares 0 2 s0 s2 =>
      s0.[0] = s2.[3].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 2 s2)).[5]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 2 s2)).[5]).`2. rewrite H => />. rewrite dom_raw_shares_0_2 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 !/shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s00_s45 s0 s4 :
    consistent_raw_shares 0 4 s0 s4 =>
      s0.[0] = s4.[5].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 4 s4)).[5]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 4 s4)).[5]).`2. rewrite H => />. rewrite dom_raw_shares_0_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s01_s12 s0 s1 :
    consistent_raw_shares 0 1 s0 s1 =>
      s0.[1] = s1.[2].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 1 s1)).[9]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 1 s1)).[9]).`2. rewrite H => />. rewrite dom_raw_shares_0_1 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s01_s24 s0 s2 :
    consistent_raw_shares 0 2 s0 s2 =>
      s0.[1] = s2.[4].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 2 s2)).[9]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 2 s2)).[9]).`2. rewrite H => />. rewrite dom_raw_shares_0_2 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s02_s14 s0 s1 :
    consistent_raw_shares 0 1 s0 s1 =>
      s0.[2] = s1.[4].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 1 s1)).[8]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 1 s1)).[8]).`2. rewrite H => />. rewrite dom_raw_shares_0_1 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s02_s31 s0 s3 :
    consistent_raw_shares 0 3 s0 s3 => 
      s0.[2] = s3.[1].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 3 s3)).[8]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 3 s3)).[8]).`2. rewrite H => />. rewrite dom_raw_shares_0_3 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s03_s15 s0 s1 :
    consistent_raw_shares 0 1 s0 s1 =>
      s0.[3] = s1.[5].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 1 s1)).[7]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 1 s1)).[7]).`2. rewrite H => />. rewrite dom_raw_shares_0_1 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s03_s40 s0 s4 :
    consistent_raw_shares 0 4 s0 s4 => 
      s0.[3] = s4.[0].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 4 s4)).[7]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 4 s4)).[7]).`2. rewrite H => />. rewrite  dom_raw_shares_0_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />.  rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s04_s32 s0 s3 :
    consistent_raw_shares 0 3 s0 s3 => 
      s0.[4] = s3.[2].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 3 s3)).[4]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 3 s3)).[4]).`2. rewrite H => />. rewrite dom_raw_shares_0_3 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s04_s41 s0 s4 :
    consistent_raw_shares 0 4 s0 s4 => 
      s0.[4] = s4.[1].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 4 s4)).[4]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 4 s4)).[4]).`2. rewrite H => />. rewrite dom_raw_shares_0_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s05_s20 s0 s2 :
    consistent_raw_shares 0 2 s0 s2 => 
      s0.[5] = s2.[0].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 2 s2)).[6]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 2 s2)).[6]).`2. rewrite H => />. rewrite dom_raw_shares_0_2 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s05_s33 s0 s3 :
    consistent_raw_shares 0 3 s0 s3 => 
      s0.[5] = s3.[3].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 0 s0) (raw_shares 3 s3)).[6]).`1 = (oget (fzip (raw_shares 0 s0) (raw_shares 3 s3)).[6]).`2. rewrite H => />. rewrite dom_raw_shares_0_3 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />.  rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s10_s35 s1 s3 :
    consistent_raw_shares 1 3 s1 s3 => 
      s1.[0] = s3.[5].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 1 s1) (raw_shares 3 s3)).[1]).`1 = (oget (fzip (raw_shares 1 s1) (raw_shares 3 s3)).[1]).`2. rewrite H => />*. rewrite dom_raw_shares_1_3 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s10_s43 s1 s4 :
    consistent_raw_shares 1 4 s1 s4 => 
      s1.[0] = s4.[3].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 1 s1) (raw_shares 4 s4)).[1]).`1 = (oget (fzip (raw_shares 1 s1) (raw_shares 4 s4)).[1]).`2. rewrite H => />*. rewrite dom_raw_shares_1_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s11_s22 s1 s2 :
    consistent_raw_shares 1 2 s1 s2 => 
      s1.[1] = s2.[2].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 1 s1) (raw_shares 2 s2)).[2]).`1 = (oget (fzip (raw_shares 1 s1) (raw_shares 2 s2)).[2]).`2. rewrite H => />*. rewrite dom_raw_shares_1_2 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />.  rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s12_s24 s1 s2 :
    consistent_raw_shares 1 2 s1 s2 => 
      s1.[2] = s2.[4].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 1 s1) (raw_shares 2 s2)).[9]).`1 = (oget (fzip (raw_shares 1 s1) (raw_shares 2 s2)).[9]).`2. rewrite H => />*. rewrite dom_raw_shares_1_2 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s11_s44 s1 s4 :
    consistent_raw_shares 1 4 s1 s4 => 
      s1.[1] = s4.[4].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 1 s1) (raw_shares 4 s4)).[2]).`1 = (oget (fzip (raw_shares 1 s1) (raw_shares 4 s4)).[2]).`2. rewrite H => />*. rewrite dom_raw_shares_1_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s13_s25 s1 s2 :
    consistent_raw_shares 1 2 s1 s2 => 
      s1.[3] = s2.[5].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 1 s1) (raw_shares 2 s2)).[3]).`1 = (oget (fzip (raw_shares 1 s1) (raw_shares 2 s2)).[3]).`2. rewrite H => />*. rewrite dom_raw_shares_1_2 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />.  rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s13_s30 s1 s3 :
    consistent_raw_shares 1 3 s1 s3 => 
      s1.[3] = s3.[0].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 1 s1) (raw_shares 3 s3)).[3]).`1 = (oget (fzip (raw_shares 1 s1) (raw_shares 3 s3)).[3]).`2. rewrite H => />*. rewrite dom_raw_shares_1_3 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s14_s31 s1 s3 :
    consistent_raw_shares 1 3 s1 s3 => 
      s1.[4] = s3.[1].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 1 s1) (raw_shares 3 s3)).[8]).`1 = (oget (fzip (raw_shares 1 s1) (raw_shares 3 s3)).[8]).`2. rewrite H => />*. rewrite dom_raw_shares_1_3 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s15_s40 s1 s4 :
    consistent_raw_shares 1 4 s1 s4 => 
      s1.[5] = s4.[0].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 1 s1) (raw_shares 4 s4)).[7]).`1 = (oget (fzip (raw_shares 1 s1) (raw_shares 4 s4)).[7]).`2. rewrite H => />*. rewrite dom_raw_shares_1_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s20_s33 s2 s3 :
    consistent_raw_shares 2 3 s2 s3 => 
      s2.[0] = s3.[3].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 2 s2) (raw_shares 3 s3)).[6]).`1 = (oget (fzip (raw_shares 2 s2) (raw_shares 3 s3)).[6]).`2. rewrite H => />*. rewrite dom_raw_shares_2_3 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s21_s34 s2 s3 :
    consistent_raw_shares 2 3 s2 s3 => 
      s2.[1] = s3.[4].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 2 s2) (raw_shares 3 s3)).[0]).`1 = (oget (fzip (raw_shares 2 s2) (raw_shares 3 s3)).[0]).`2. rewrite H => />*. rewrite dom_raw_shares_2_3 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s21_s42 s2 s4 :
    consistent_raw_shares 2 4 s2 s4 => 
      s2.[1] = s4.[2].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 2 s2) (raw_shares 4 s4)).[0]).`1 = (oget (fzip (raw_shares 2 s2) (raw_shares 4 s4)).[0]).`2. rewrite H => />*. rewrite dom_raw_shares_2_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s22_s44 s2 s4 :
    consistent_raw_shares 2 4 s2 s4 => 
      s2.[2] = s4.[4].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 2 s2) (raw_shares 4 s4)).[2]).`1 = (oget (fzip (raw_shares 2 s2) (raw_shares 4 s4)).[2]).`2. rewrite H => />*. rewrite dom_raw_shares_2_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s23_s45 s2 s4 :
    consistent_raw_shares 2 4 s2 s4 => 
      s2.[3] = s4.[5].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 2 s2) (raw_shares 4 s4)).[5]).`1 = (oget (fzip (raw_shares 2 s2) (raw_shares 4 s4)).[5]).`2. rewrite H => />*. rewrite dom_raw_shares_2_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s25_s30 s2 s3 :
    consistent_raw_shares 2 3 s2 s3 => 
      s2.[5] = s3.[0].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 2 s2) (raw_shares 3 s3)).[3]).`1 = (oget (fzip (raw_shares 2 s2) (raw_shares 3 s3)).[3]).`2. rewrite H => />*. rewrite dom_raw_shares_2_3 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s32_s41 s3 s4 :
    consistent_raw_shares 3 4 s3 s4 => 
      s3.[2] = s4.[1].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 3 s3) (raw_shares 4 s4)).[4]).`1 = (oget (fzip (raw_shares 3 s3) (raw_shares 4 s4)).[4]).`2. rewrite H => />*. rewrite dom_raw_shares_3_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/fzip !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s34_s42 s3 s4 :
    consistent_raw_shares 3 4 s3 s4 => 
      s3.[4] = s4.[2].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 3 s3) (raw_shares 4 s4)).[0]).`1 = (oget (fzip (raw_shares 3 s3) (raw_shares 4 s4)).[0]).`2. rewrite H => />*. rewrite dom_raw_shares_3_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_s35_s43 s3 s4 :
    consistent_raw_shares 3 4 s3 s4 => 
      s3.[5] = s4.[3].
    rewrite !/consistent_raw_shares fallP => />H. have : (oget (fzip (raw_shares 3 s3) (raw_shares 4 s4)).[1]).`1 = (oget (fzip (raw_shares 3 s3) (raw_shares 4 s4)).[1]).`2. rewrite H => />*. rewrite !/fzip dom_raw_shares_3_4 => />. rewrite !/raw_shares /raw_shares' !foldl_iseqE !iseq_6 /shr_idx => />H0. clear H. move :H0. rewrite !/set !/empty !/get_rshr !/shr_idx !fzip_some => />. rewrite in_fsetI !fdom_set fdom_empty !in_fsetU !in_fset0 !in_fset1 => />. rewrite get_set_eqE => />. rewrite get_set_neqE => />. rewrite get_set_neqE => />. rewrite get_set_eqE => />. qed.

  lemma consistent_raw_shares_pshare i j x :
  0 <= i < 5 => 0 <= j < 5 =>
  consistent_raw_shares i j (pshare x).[i] (pshare x).[j].
  move => /> Hi1 Hi2 Hj1 Hj2.
  rewrite /consistent_raw_shares fallP => |>. move => a. 
  rewrite fdom_fzip in_fsetI !dom_raw_shares => |>. rewrite !mem_oflist => |>H1 H2. 
  rewrite /pshare => |>*. rewrite !Array5.initE /init_sh !andabP !andaP => |>*. 
  rewrite !fzip_some => |>*. rewrite !dom_raw_shares => |>*. rewrite in_fsetI !mem_oflist => |>*. rewrite !raw_shares_inv => |>*.
  rewrite !Array6.initE => |>*. rewrite !dom_shr_idx_inv => |>*. rewrite !(nth_map witness). rewrite size_shr_idx. progress. rewrite dom_shr_idx_inv => |>*. rewrite size_shr_idx. progress. rewrite dom_shr_idx_inv => |>*. rewrite !Array10.get_of_list. rewrite rng_shr_idx. rewrite dom_shr_idx_inv => |>*. rewrite rng_shr_idx. rewrite dom_shr_idx_inv => |>*. 
  rewrite !nth_shr_idx_shr_idx_inv => |>*. qed.

end Maurer5SS.
