require import AllCore Int List FSet SmtMap Distr PrimeField Ring DMap DList.
require import Aux AuxList AuxFSet AuxSmtMap AuxArray.
require import Array5 Array6 Array9 Array10.
require import NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgCircuit.
require import NextMsgWeak NextMsgWeakCircuit NextMsgWeakCircuitProofs NextMsgMaurer NextMsgMaurerMPC NextMsgMaurerAuxProofs NextMsgMaurerAddProofs.

require import NextMsgISet NextMsgIMap NextMsgMaurerP NextMsgMaurerAPI.

require import Maurer5Spec.
import Maurer5Spec Maurer5SS.
import MaurerAPI.

op inner_mul_start(swi swj : shr, r : rand) : msgs =    
         Maurer5SS.share (cross swi swj) r.

op inner_mul_starts (swis swjs:shrs) (rs:rand Array5.t) =
    Array5.map (fun (x:_*_*_) => inner_mul_start x.`1 x.`2 x.`3) (array5_zip3 swis swjs rs).

op my_mul_start(wi wj : wid, wst : wire_st, r : rand) : msgs =      
     let w = wst.`1 in
     let wires = wst.`2 in
     let swi = oget wires.[wi] in
     let swj = oget wires.[wj] in
         inner_mul_start swi swj r.

lemma equiv_mul_start wi wj ms wst :
    Maurer5Spec.mul_start wi wj ms wst = my_mul_start wi wj  ms wst.
    rewrite /mul_start /my_mul_start /inner_mul_start => />*. rewrite (prod_id ms) => />*. qed.

op inner_mul_end (ms:msgs) : shr =
     let ss = add_shr ms.[0] ms.[1] in
     let ss = add_shr ss     ms.[2] in
     let ss = add_shr ss     ms.[3] in
     let ss = add_shr ss     ms.[4] in
     ss.

op inner_mul_ends (mss:msgs Array5.t) : shr Array5.t = 
    Array5.map inner_mul_end mss.

op my_mul_end(ms : msgs, wst : wire_st) : wire_st =
     let w = wst.`1 in 
     let wires = wst.`2 in
     (w + 1, wires.[w <- inner_mul_end ms ]).

lemma equiv_mul_end ms wst :
    Maurer5Spec.mul_end ms wst = my_mul_end ms wst.
    rewrite /mul_end /my_mul_end /inner_mul_end => />*. rewrite (prod_id wst) => />*. qed.

lemma dom_mul_end m st :
    fdom (Maurer5Spec.mul_end m st).`2 = fdom st.`2 `|` fset1 st.`1.
    rewrite /mul_end => />*. rewrite (prod_id st) => />*. rewrite fdom_set => />*. qed.

theory MaurerWeakMulProofs.

  lemma wire_unshare xs :
    (g_unshare xs).`1 = (MaurerP.get xs 0).`1.`1.
    rewrite /unshare /g_unshare => />*. qed.

  lemma valid_wire2 i g ws :
    i \in MaurerMul.GT.partyset /\ MaurerMul.valid_inputs g ws => g.`2.`1 \in fdom (MaurerP.get ws i).`1.`2.
    rewrite /valid_inputs => />H H0. have : (MaurerMul.consistent_inputs g i i ((MaurerP.get ws i)) ((MaurerP.get ws i))). rewrite H0 => />*. rewrite /consistent_inputs => />H1 H2. qed.

  lemma valid_wire3 i g ws :
    i \in MaurerMul.GT.partyset /\ MaurerMul.valid_inputs g ws => g.`2.`2 \in fdom (MaurerP.get ws i).`1.`2.
    rewrite /valid_inputs => />H H0. have : (MaurerMul.consistent_inputs g i i ((MaurerP.get ws i)) ((MaurerP.get ws i))). rewrite H0 => />*. rewrite /consistent_inputs => />H1 H2. qed.

  lemma valid_wid i1 i2 x ys :
    i1 \in MaurerMul.GT.partyset /\ i2 \in MaurerMul.GT.partyset /\ MaurerMul.valid_inputs x ys =>
      ((MaurerP.get ys i1)).`1.`1 = ((MaurerP.get ys i2)).`1.`1.
    rewrite /valid_inputs => />H H0 H1. have : (MaurerMul.consistent_inputs x i1 i2 ((MaurerP.get ys i1)) ((MaurerP.get ys i2))). rewrite H1 => />*. rewrite /consistent_inputs => />H2 H3 H4. qed.
 
  lemma dom_unshare xs :
    fdom (g_unshare xs).`2 = fdom (MaurerP.get xs 0).`1.`2.
    rewrite /unshare /g_unshare => />*. rewrite fdom_ofset => />*. qed.

  lemma unshare_share s1 r1 :
    Maurer5SS.unshare (Maurer5SS.share s1 r1) = s1.
    rewrite /unshare /share /init_sh => />*. rewrite !(nth_map witness) => />*. rewrite !Array10.initE => />*. rewrite /shr_idx => />*. rewrite /sum_rand => />*. rewrite array9_to_list => />*. algebra. qed.

  lemma mul_shr_commute (sh1 sh2 : shrs) rc0 rc1 rc2 rc3 rc4 : 
    valid_raw_shares sh1 => valid_raw_shares sh2 =>
    fmul (Maurer5SS.unshare sh1) (Maurer5SS.unshare sh2) =
      let cross0 = Maurer5SS.share (cross sh1.[0] sh2.[0]) rc0 in
      let cross1 = Maurer5SS.share (cross sh1.[1] sh2.[1]) rc1 in
      let cross2 = Maurer5SS.share (cross sh1.[2] sh2.[2]) rc2 in
      let cross3 = Maurer5SS.share (cross sh1.[3] sh2.[3]) rc3 in
      let cross4 = Maurer5SS.share (cross sh1.[4] sh2.[4]) rc4 in
      let add0 = add_shr cross0.[0] 
                (add_shr cross1.[0] 
                (add_shr cross2.[0] 
                (add_shr cross3.[0] cross4.[0]))) in
      let add1 = add_shr cross0.[1] 
                (add_shr cross1.[1] 
                (add_shr cross2.[1] 
                (add_shr cross3.[1] cross4.[1]))) in
      let add2 = add_shr cross0.[2] 
                (add_shr cross1.[2] 
                (add_shr cross2.[2] 
                (add_shr cross3.[2] cross4.[2]))) in
      let add3 = add_shr cross0.[3] 
                (add_shr cross1.[3] 
                (add_shr cross2.[3] 
                (add_shr cross3.[3] cross4.[3]))) in
      let add4 = add_shr cross0.[4] 
                (add_shr cross1.[4] 
                (add_shr cross2.[4] 
                (add_shr cross3.[4] cross4.[4]))) in
      let adds = Array5.of_list witness (add0::add1::add2::add3::add4::[]) in
      Maurer5SS.unshare adds.
    progress. rewrite /share /rshare /cross /add_shr /unshare /init_sh /shr_idx /sum_rand /to_list /mkseq /=. rewrite (_: iota_ 0 9 = 0::1::2::3::4::5::6::7::8::[]); first by smt(iotaS iota0). simplify. move :H H0. rewrite /valid_raw_shares. progress.
    (*shr1*)
    rewrite (_: sh1.[1].[2] = sh1.[0].[1] ). (* 9 *) rewrite (consistent_s01_s12 sh1.[0] sh1.[1]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.  
    rewrite (_: sh1.[1].[4] = sh1.[0].[2] ). (* 8 *) rewrite (consistent_s02_s14 sh1.[0] sh1.[1]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[1].[5] = sh1.[0].[3] ). (* 7 *) rewrite (consistent_s03_s15 sh1.[0] sh1.[1]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[2].[0] = sh1.[0].[5] ). (* 6 *) rewrite (consistent_s05_s20 sh1.[0] sh1.[2]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[2].[2] = sh1.[1].[1] ). (* 2 *) rewrite (consistent_s11_s22 sh1.[1] sh1.[2]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*. 
    rewrite (_: sh1.[2].[3] = sh1.[0].[0] ). (* 5 *) rewrite (consistent_s00_s23 sh1.[0] sh1.[2]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[2].[4] = sh1.[0].[1] ). (* 9 *) rewrite (consistent_s01_s24 sh1.[0] sh1.[2]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*. 
    rewrite (_: sh1.[2].[5] = sh1.[1].[3] ). (* 3 *) rewrite (consistent_s13_s25 sh1.[1] sh1.[2]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*. 
    rewrite (_: sh1.[3].[0] = sh1.[1].[3] ). (* 3 *) rewrite (consistent_s13_s30 sh1.[1] sh1.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*. 
    rewrite (_: sh1.[3].[1] = sh1.[0].[2] ). (* 8 *) rewrite (consistent_s02_s31 sh1.[0] sh1.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[3].[2] = sh1.[0].[4] ). (* 4 *) rewrite (consistent_s04_s32 sh1.[0] sh1.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[3].[3] = sh1.[0].[5] ). (* 6 *) rewrite (consistent_s05_s33 sh1.[0] sh1.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[3].[4] = sh1.[2].[1] ). (* 0 *) rewrite (consistent_s21_s34 sh1.[2] sh1.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[3].[5] = sh1.[1].[0] ). (* 1 *) rewrite (consistent_s10_s35 sh1.[1] sh1.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[4].[0] = sh1.[0].[3] ). (* 7 *) rewrite (consistent_s03_s40 sh1.[0] sh1.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[4].[1] = sh1.[0].[4] ). (* 4 *) rewrite (consistent_s04_s41 sh1.[0] sh1.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[4].[2] = sh1.[2].[1] ). (* 0 *) rewrite (consistent_s21_s42 sh1.[2] sh1.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[4].[3] = sh1.[1].[0] ). (* 1 *) rewrite (consistent_s10_s43 sh1.[1] sh1.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[4].[4] = sh1.[1].[1] ). (* 2 *) rewrite (consistent_s11_s44 sh1.[1] sh1.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    rewrite (_: sh1.[4].[5] = sh1.[0].[0] ). (* 5 *) rewrite (consistent_s00_s45 sh1.[0] sh1.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H => />*.
    (*shr2*)
    rewrite (_: sh2.[1].[2] = sh2.[0].[1] ). (* 9 *) rewrite (consistent_s01_s12 sh2.[0] sh2.[1]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.  
    rewrite (_: sh2.[1].[4] = sh2.[0].[2] ). (* 8 *) rewrite (consistent_s02_s14 sh2.[0] sh2.[1]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[1].[5] = sh2.[0].[3] ). (* 7 *) rewrite (consistent_s03_s15 sh2.[0] sh2.[1]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[2].[0] = sh2.[0].[5] ). (* 6 *) rewrite (consistent_s05_s20 sh2.[0] sh2.[2]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[2].[2] = sh2.[1].[1] ). (* 2 *) rewrite (consistent_s11_s22 sh2.[1] sh2.[2]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*. 
    rewrite (_: sh2.[2].[3] = sh2.[0].[0] ). (* 5 *) rewrite (consistent_s00_s23 sh2.[0] sh2.[2]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[2].[4] = sh2.[0].[1] ). (* 9 *) rewrite (consistent_s01_s24 sh2.[0] sh2.[2]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*. 
    rewrite (_: sh2.[2].[5] = sh2.[1].[3] ). (* 3 *) rewrite (consistent_s13_s25 sh2.[1] sh2.[2]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*. 
    rewrite (_: sh2.[3].[0] = sh2.[1].[3] ). (* 3 *) rewrite (consistent_s13_s30 sh2.[1] sh2.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*. 
    rewrite (_: sh2.[3].[1] = sh2.[0].[2] ). (* 8 *) rewrite (consistent_s02_s31 sh2.[0] sh2.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[3].[2] = sh2.[0].[4] ). (* 4 *) rewrite (consistent_s04_s32 sh2.[0] sh2.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[3].[3] = sh2.[0].[5] ). (* 6 *) rewrite (consistent_s05_s33 sh2.[0] sh2.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[3].[4] = sh2.[2].[1] ). (* 0 *) rewrite (consistent_s21_s34 sh2.[2] sh2.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[3].[5] = sh2.[1].[0] ). (* 1 *) rewrite (consistent_s10_s35 sh2.[1] sh2.[3]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[4].[0] = sh2.[0].[3] ). (* 7 *) rewrite (consistent_s03_s40 sh2.[0] sh2.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[4].[1] = sh2.[0].[4] ). (* 4 *) rewrite (consistent_s04_s41 sh2.[0] sh2.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[4].[2] = sh2.[2].[1] ). (* 0 *) rewrite (consistent_s21_s42 sh2.[2] sh2.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[4].[3] = sh2.[1].[0] ). (* 1 *) rewrite (consistent_s10_s43 sh2.[1] sh2.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[4].[4] = sh2.[1].[1] ). (* 2 *) rewrite (consistent_s11_s44 sh2.[1] sh2.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    rewrite (_: sh2.[4].[5] = sh2.[0].[0] ). (* 5 *) rewrite (consistent_s00_s45 sh2.[0] sh2.[4]) => />*. rewrite -consistent_raw_shares_conv. rewrite H0 => />*.
    ring. qed.

  lemma add_shr_sym s1 s2 :
    add_shr s1 s2 = add_shr s2 s1.
    rewrite /add_shr => />*. rewrite Array6.tP => />*. rewrite !Array6.map2iE => />*. algebra. qed.

  lemma add_shr_assoc s1 s2 s3 :
    add_shr s1 (add_shr s2 s3) = add_shr (add_shr s1 s2) s3.
    rewrite /add_shr => />*. rewrite Array6.tP => />*. rewrite !Array6.map2iE => />*. algebra. qed.
    
  lemma inner_mul_correctness sx sy r :
    valid_raw_shares sx => valid_raw_shares sy => 
    fmul (Maurer5SS.unshare sx) (Maurer5SS.unshare sy) =
      let outs = inner_mul_starts sx sy r in
      let ins = array5_send_messages outs in
      Maurer5SS.unshare (inner_mul_ends ins).
    move => H H0. rewrite (mul_shr_commute _ _ r.[0] r.[1] r.[2] r.[3] r.[4]) => />*. congr.
    rewrite /inner_mul_ends /inner_mul_starts /array5_send_messages Array5.tP => />i Hi1 Hi2. rewrite Array5.mapE => />*. rewrite !Array5.initE !andabP !andaP => />*. rewrite /array5_zip3 !Array5.initE !andabP !andaP => />. 
    (*p0*)
    case (i=0) => />*. rewrite /inner_mul_end /inner_mul_start /uncurry3 => />*.
    rewrite -!add_shr_assoc => />*. 
    (*p1*)
    case (i=1) => />*. rewrite /inner_mul_end /inner_mul_start /uncurry3 => />*.
    rewrite -!add_shr_assoc => />*.  
    (*p2*)
    case (i=2) => />*. rewrite /inner_mul_end /inner_mul_start /uncurry3 => />*.
    rewrite -!add_shr_assoc => />*.  
    (*p3*)
    case (i=3) => />*. rewrite /inner_mul_end /inner_mul_start /uncurry3 => />*.
    rewrite -!add_shr_assoc => />*.  
    (*p4*)
    case (i=4) => />*. rewrite /inner_mul_end /inner_mul_start /uncurry3 => />*.
    rewrite -!add_shr_assoc => />*. 
    have : false. smt(). progress. qed.

  module Rand = {
    proc gen_party_mul_coins() : rand = {
      var r;
      r <$ gen_rand;
      return r;
    }
    proc gen_mul_coins(g:MaurerMul.Gate) : rand MaurerP.arrayN = {
      var x0,x1,x2,x3,x4;
      x0 <@ gen_party_mul_coins();
      x1 <@ gen_party_mul_coins();
      x2 <@ gen_party_mul_coins();
      x3 <@ gen_party_mul_coins();
      x4 <@ gen_party_mul_coins();
      return MaurerP.of_list [x0;x1;x2;x3;x4];
    }
    proc gen_coins(g:MaurerMul.Gate) : rand MaurerP.arrayN = {
      var cs;
      cs <$ MaurerWeakMul.gen_rand g;
      return cs;
    }
  }.

  op def_rand : rand = Array9.create fzero.

  clone import DMapSampling as DMS with
    type t1 = (PF.zp Array9.t) list,
    type t2 = PF.zp Array9.t MaurerP.arrayN.

  clone import Program as DLS with
    type t = PF.zp Array9.t,
    op d = gen_rand.

  lemma sample_mul_coins : 
    equiv [ Rand.gen_coins ~ Rand.gen_mul_coins : true ==> ={res} ].
    proc. simplify. 
    transitivity{1}
      { cs <@ DMS.S.sample(gen_parties_rand,MaurerP.of_list); }
      ( true ==> ={cs} )
      ( true ==> cs{1} = MaurerP.of_list (cons x0{2} (cons x1{2} (cons x2{2} (cons x3{2} (cons x4{2} []))))) ).
      progress.
      progress. 
    inline *. wp. sp. auto => |>. 
    transitivity{1}
      { cs <@ DMS.S.map(gen_parties_rand,MaurerP.of_list); }
      ( true ==> ={cs} )
      ( true ==> cs{1} = MaurerP.of_list (cons x0{2} (cons x1{2} (cons x2{2} (cons x3{2} (cons x4{2} []))))) ).
      progress.
      progress. 
    call DMS.sample => |>. auto => |>. 
    inline *. wp. sp. 
    transitivity{1}
      { r1 <@ DLS.Sample.sample(5); }
      ( ={d,f} /\ d{1} = gen_parties_rand /\ f{1} = MaurerP.of_list ==> ={d,f,r1} )
      ( d{1} = gen_parties_rand /\ f{1} = MaurerP.of_list ==> f{1} r1{1} = MaurerP.of_list (cons x0{2} (cons x1{2} (cons x2{2} (cons x3{2} (cons r3{2} []))))) ).
      progress. exists gen_parties_rand MaurerP.of_list => |>. 
      progress.
    inline *. wp. sp. auto => |>. 
    transitivity{1}
      { r1 <@ DLS.LoopSnoc.sample(5); }
      ( ={d,f} /\ d{1} = gen_parties_rand /\ f{1} = MaurerP.of_list ==> ={d,f,r1} )
      ( d{1} = gen_parties_rand /\ f{1} = MaurerP.of_list ==> f{1} r1{1} = MaurerP.of_list (cons x0{2} (cons x1{2} (cons x2{2} (cons x3{2} (cons r3{2} []))))) ).
      progress. exists gen_parties_rand MaurerP.of_list => |>. 
      progress.
    call DLS.Sample_LoopSnoc_eq => |>. auto => |>.
    inline *. swap{2} 8 1. swap{2} 6 3. swap{2} 4 5. swap{2} 2 7. wp. sp.
    conseq (_: n{1} = 5 /\ i{1} = 0 /\ l{1} = [] ==> l{1} = (cons r{2} (cons r0{2} (cons r1{2} (cons r2{2} (cons r3{2} []))))) ).
    progress. progress. 
    unroll{1} 1. if{1}.  
    seq 1 1 : (#pre /\ ={r}). auto => |>. sp.
    conseq (_: n{1} = 5 /\ i{1}=1 /\ l{1} = [r{2}] ==> l{1} = cons r{2} (cons r0{2} (cons r1{2} (cons r2{2} (cons r3{2} [])))) ).
    progress. unroll{1} 1. if{1}. 
    seq 1 1 : (n{1} = 5 /\ i{1} = 1 /\ r{1}=r0{2} /\ l{1}=[r{2}] /\ i{1} < n{1}). rnd => |>. progress. sp. 
    conseq (_: n{1} = 5 /\ i{1}=2 /\ l{1} = [r{2};r0{2}] ==> l{1} = cons r{2} (cons r0{2} (cons r1{2} (cons r2{2} (cons r3{2} [])))) ).
    progress. unroll{1} 1. if{1}.
    seq 1 1 : (n{1} = 5 /\ i{1} = 2 /\ l{1} = [r{2};r0{2}] /\ r{1}=r1{2} /\ i{1} < n{1}). auto => |>. sp. 
    conseq (_: n{1} = 5 /\ i{1}=3 /\ l{1} = [r{2};r0{2};r1{2}] ==> l{1} = cons r{2} (cons r0{2} (cons r1{2} (cons r2{2} (cons r3{2} [])))) ).
    progress. unroll{1} 1. if{1}.
    seq 1 1 : (n{1} = 5 /\ i{1} = 3 /\ l{1} = [r{2};r0{2};r1{2}] /\ r{1}=r2{2} /\ i{1} < n{1}). auto => |>. sp. 
    conseq (_: n{1} = 5 /\ i{1}=4 /\ l{1} = [r{2};r0{2};r1{2};r2{2}] ==> l{1} = cons r{2} (cons r0{2} (cons r1{2} (cons r2{2} (cons r3{2} [])))) ).
    progress. unroll{1} 1. if{1}.
    seq 1 1 : (n{1} = 5 /\ i{1} = 4 /\ l{1} = [r{2};r0{2};r1{2};r2{2}] /\ r{1}=r3{2} /\ i{1} < n{1}). auto => |>. sp. 
    conseq (_: n{1} = 5 /\ i{1}=5 /\ l{1} = [r{2};r0{2};r1{2};r2{2};r3{2}] ==> l{1} = cons r{2} (cons r0{2} (cons r1{2} (cons r2{2} (cons r3{2} [])))) ).
    progress. rcondf{1} 1. progress. auto => |>. 
    exfalso. progress. smt().
    exfalso. progress. smt().
    exfalso. progress. smt().
    exfalso. progress. smt().
    exfalso. progress. smt(). qed.

  module Priv = {
    proc mul_share (is:int fset,s:val) = {
      var r,ss,ssc;
      r <@ Rand.gen_party_mul_coins();
      ss <- Maurer5SS.share s r;
      ssc <- ofset (fun i => ss.[i]) is;
      return ssc;
    }
    proc mul_share2 (is:int fset,s:val) = {
      var ssc,ssc';
      ssc <@ SSSecurity.real(s,elems is);
      ssc' <- ofassoc ssc;
      return ssc';
    }
    proc party_share (i:int,is:int fset,s:val) = {
      var r,ss,ssc;
      r <@ Rand.gen_party_mul_coins();
      ss <- Maurer5SS.share s r;
      ssc <- ofset (fun i => ss.[i]) is;
      return (ssc,(i \in is) ? r : def_rand);
    }
    proc mul_ideal (is:int fset,wij:MaurerMul.Gate,ws:MaurerMul.share MaurerP.arrayN) = {
      var r0,r1,r2,r3,r4,c0,c1,c2,c3,c4,out0,out1,out2,out3,out4,ins,ins0;
      c0 <- cross (oget (MaurerP.get ws 0).`1.`2.[wij.`2.`1]) (oget (MaurerP.get ws 0).`1.`2.[wij.`2.`2]);
      c1 <- cross (oget (MaurerP.get ws 1).`1.`2.[wij.`2.`1]) (oget (MaurerP.get ws 1).`1.`2.[wij.`2.`2]);
      c2 <- cross (oget (MaurerP.get ws 2).`1.`2.[wij.`2.`1]) (oget (MaurerP.get ws 2).`1.`2.[wij.`2.`2]);
      c3 <- cross (oget (MaurerP.get ws 3).`1.`2.[wij.`2.`1]) (oget (MaurerP.get ws 3).`1.`2.[wij.`2.`2]);
      c4 <- cross (oget (MaurerP.get ws 4).`1.`2.[wij.`2.`1]) (oget (MaurerP.get ws 4).`1.`2.[wij.`2.`2]);
      r0 <@ Rand.gen_party_mul_coins();
      r1 <@ Rand.gen_party_mul_coins();
      r2 <@ Rand.gen_party_mul_coins();
      r3 <@ Rand.gen_party_mul_coins();
      r4 <@ Rand.gen_party_mul_coins();
      out0 <- Maurer5SS.share (if 0 \in is then c0 else fzero) r0;
      out1 <- Maurer5SS.share (if 1 \in is then c1 else fzero) r1;
      out2 <- Maurer5SS.share (if 2 \in is then c2 else fzero) r2;
      out3 <- Maurer5SS.share (if 3 \in is then c3 else fzero) r3;
      out4 <- Maurer5SS.share (if 4 \in is then c4 else fzero) r4;
      ins <- MaurerMul.send_messages (MaurerP.of_list [out0;out1;out2;out3;out4]);
      ins0 <- ofset (fun i => MaurerMul.GT.pinit (fun j => Array.singl 0 ((MaurerP.get ins i).[j]))) is;
      return fzip3 (ofset (fun i => MaurerP.get ws i) is) ins0 (ofset (fun i => if i=0 then r0 else if i=1 then r1 else if i=2 then r2 else if i=3 then r3 else if i=4 then r4 else witness) is);
    }
    proc mul_real (is:int fset,wij:MaurerMul.Gate,ws:MaurerMul.share MaurerP.arrayN) = {
      var r0,r1,r2,r3,r4,c0,c1,c2,c3,c4,out0,out1,out2,out3,out4,ins,ins0;
      c0 <- cross (oget (MaurerP.get ws 0).`1.`2.[wij.`2.`1]) (oget (MaurerP.get ws 0).`1.`2.[wij.`2.`2]);
      c1 <- cross (oget (MaurerP.get ws 1).`1.`2.[wij.`2.`1]) (oget (MaurerP.get ws 1).`1.`2.[wij.`2.`2]);
      c2 <- cross (oget (MaurerP.get ws 2).`1.`2.[wij.`2.`1]) (oget (MaurerP.get ws 2).`1.`2.[wij.`2.`2]);
      c3 <- cross (oget (MaurerP.get ws 3).`1.`2.[wij.`2.`1]) (oget (MaurerP.get ws 3).`1.`2.[wij.`2.`2]);
      c4 <- cross (oget (MaurerP.get ws 4).`1.`2.[wij.`2.`1]) (oget (MaurerP.get ws 4).`1.`2.[wij.`2.`2]);
      r0 <@ Rand.gen_party_mul_coins();
      r1 <@ Rand.gen_party_mul_coins();
      r2 <@ Rand.gen_party_mul_coins();
      r3 <@ Rand.gen_party_mul_coins();
      r4 <@ Rand.gen_party_mul_coins();
      out0 <- Maurer5SS.share c0 r0;
      out1 <- Maurer5SS.share c1 r1;
      out2 <- Maurer5SS.share c2 r2;
      out3 <- Maurer5SS.share c3 r3;
      out4 <- Maurer5SS.share c4 r4;
      ins <- MaurerMul.send_messages (MaurerP.of_list [out0;out1;out2;out3;out4]);
      ins0 <- ofset (fun i => MaurerP.init (fun j => Array.singl 0 ((MaurerP.get ins i).[j]))) is;
      return fzip3 (ofset (fun i => MaurerP.get ws i) is) ins0 (ofset (fun i => if i=0 then r0 else if i=1 then r1 else if i=2 then r2 else if i=3 then r3 else if i=4 then r4 else witness) is);
    }
  }.

  lemma mul_share_privacy2 :
    equiv [ Priv.mul_share2 ~ Priv.mul_share2 : ={is} /\ MaurerWeakMul.corrupted_set is{1} ==> ={res} ].
    proc. simplify. wp. 
    transitivity{1}
      { ssc <@ SSSecurity.ideal(s,elems is); }
      ( ={is,s} /\ MaurerWeakMul.corrupted_set is{1} ==> ={ssc} )
      ( ={is} /\ MaurerWeakMul.corrupted_set is{1} ==> ofassoc ssc{1} = ofassoc ssc{2} ).
      progress. exists is{2} s{1} => />*.
      progress.
    call ss_security => />*. auto => />. progress. rewrite -cardE => />. rewrite uniq_elems => />*. rewrite -memE in H1. have : pid \in MaurerMul.ST.partyset. apply (in_subset is{2}) => />*. rewrite iset_in_def in_iseq => />*. 
    transitivity{2}
      { ssc <@ SSSecurity.ideal(s,elems is); }
      ( ={is} /\ MaurerWeakMul.corrupted_set is{1} ==> ofassoc ssc{1} = ofassoc ssc{2} )
      ( ={is,s} /\ MaurerWeakMul.corrupted_set is{1} ==> ={ssc} ).
      progress. exists is{2} s{2} => />*.
      progress.
    call ss_ideal => />*. auto => />. progress. rewrite -cardE => />. rewrite uniq_elems => />*. rewrite -memE in H1. have : pid \in MaurerMul.ST.partyset. apply (in_subset is{2}) => />*. rewrite iset_in_def in_iseq => />*. 
    symmetry.
    call ss_security => />*. auto => />. progress. rewrite -cardE => />. rewrite uniq_elems => />*. rewrite -memE in H1. have : pid \in MaurerMul.ST.partyset. apply (in_subset is{1}) => />*. rewrite iset_in_def in_iseq => />*. qed.

  lemma mul_share_privacy :
    equiv [ Priv.mul_share ~ Priv.mul_share : ={is} /\ MaurerWeakMul.corrupted_set is{1} ==> ={res} ].
    proc. simplify. 
    transitivity{1}
      { ssc <@ Priv.mul_share2(is,s); }
      ( ={is,s} /\ MaurerWeakMul.corrupted_set is{1} ==> ={ssc} )
      ( ={is} /\ MaurerWeakMul.corrupted_set is{1} ==> ={ssc} ).
      progress. exists is{2} s{1} => />*. 
      progress.
    inline *. sp. wp. rnd => />. progress. rewrite H0 => />*. 
    auto => />. progress. rewrite ofassoc_ofset => />*. 
    transitivity{2}
      { ssc <@ Priv.mul_share2(is,s); }
      ( ={is} /\ MaurerWeakMul.corrupted_set is{1} ==> ={ssc} )
      ( ={is,s} /\ MaurerWeakMul.corrupted_set is{1} ==> ={ssc} ).
      progress. exists is{2} s{2} => />*. 
      progress.
    call mul_share_privacy2 => />*. auto => />*.
    inline *. sp. wp. rnd => />. progress. rewrite H0 => />*. 
    auto => />. progress. rewrite ofassoc_ofset => />*. qed.

  lemma party_share_privacy :
    equiv [ Priv.party_share ~ Priv.party_share : ((i{1} \in is{1}) ? s{1}=s{2} : true) /\ ={i,is} /\ MaurerWeakMul.corrupted_set is{1} ==> ={res} ].
    proc. simplify. case (i{1} \in is{1}) => />*. 
    inline *. wp. auto => />. progress. have : s{1}=s{2}. rewrite H => />*. progress. 
    transitivity{1}
      { ssc <@ Priv.mul_share(is,s); }
      ( ={i,is,s} /\ MaurerWeakMul.corrupted_set is{1} ==> ={i,is,s,ssc}  )
      ( ={i,is} /\ MaurerWeakMul.corrupted_set is{1} ==> ={i,is,ssc} ).
      progress. exists i{2} is{2} s{1} => />*. 
      progress. 
    inline *. sp. wp. auto => />. progress. 
    transitivity{2}
      { ssc <@ Priv.mul_share(is,s); }
      ( ={i,is} /\ MaurerWeakMul.corrupted_set is{1} ==> ={i,is,ssc}  )
      ( ={i,is,s} /\ MaurerWeakMul.corrupted_set is{1} ==> ={i,is,s,ssc} ).
      progress. exists i{2} is{2} s{2} => />*. 
      progress.
    call mul_share_privacy => />*. auto => />. progress. 
    inline *. sp. wp. auto => />. qed.

  lemma mul_weak_privacy : 
    equiv [ Priv.mul_ideal ~ Priv.mul_real : ={is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ MaurerMul.valid_inputs wij{1} ws{1} ==> ={res} ].
    proc. simplify. sp.  
    swap{1} 6 -4. swap{2} 6 -4. seq 2 2 : ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ MaurerMul.valid_inputs wij{1} ws{1} /\  ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) ). 
    alias{1} 2 t = 0. swap{1} 2 1. alias{1} 3 inr0 = (ofset (fun i => out0.[i]) is,(0 \in is) ? r0 : def_rand).
    alias{2} 2 t = 0. swap{2} 2 1. alias{2} 3 inr0 = (ofset (fun i => out0.[i]) is,(0 \in is) ? r0 : def_rand).
    transitivity{1}
      { inr0 <@ Priv.party_share(0,is,(if 0 \in is then c0 else fzero)); }
      ( ={c0,c1,c2,c3,c4,is,wij,ws} ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr0} /\ inr0{1} = (ofset (fun i => out0{1}.[i]) is{1},(0 \in is{1}) ? r0{1} : def_rand) )
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr0} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ inr0{2} = (ofset (fun i => out0{2}.[i]) is{2},(0 \in is{2}) ? r0{2} : def_rand) ).
      progress. exists
      (cross (oget ((MaurerP.get ws{2} 0)).`1.`2.[wij{2}.`2.`1]) (oget ((MaurerP.get ws{2} 0)).`1.`2.[wij{2}.`2.`2]))
      (cross (oget ((MaurerP.get ws{2} 1)).`1.`2.[wij{2}.`2.`1]) (oget ((MaurerP.get ws{2} 1)).`1.`2.[wij{2}.`2.`2]))
      (cross (oget ((MaurerP.get ws{2} 2)).`1.`2.[wij{2}.`2.`1]) (oget ((MaurerP.get ws{2} 2)).`1.`2.[wij{2}.`2.`2]))
      (cross (oget ((MaurerP.get ws{2} 3)).`1.`2.[wij{2}.`2.`1]) (oget ((MaurerP.get ws{2} 3)).`1.`2.[wij{2}.`2.`2]))
      (cross (oget ((MaurerP.get ws{2} 4)).`1.`2.[wij{2}.`2.`1]) (oget ((MaurerP.get ws{2} 4)).`1.`2.[wij{2}.`2.`2]))
      is{2} wij{2} ws{2} => />*.
      progress. move :H2. rewrite H3 => />*. 
    inline *. auto => />*.
    transitivity{2}
      { inr0 <@ Priv.party_share(0,is,c0); }
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr0} /\ MaurerWeakMul.corrupted_set is{1})
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr0} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ inr0{2} = (ofset (fun i => out0{2}.[i]) is{2},(0 \in is{2}) ? r0{2} : def_rand) ).
      progress. exists c0{2} c1{2} c2{2} c3{2} c4{2} is{2} wij{2} ws{2} => />*.
      progress.
    call party_share_privacy => />*. auto => />*.
    inline *. auto => />*. 
    swap{1} 5 -3. swap{2} 5 -3. seq 2 2 : ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ MaurerMul.valid_inputs wij{1} ws{1} /\ ofset (fun (i : int) => out0{1}.[i]) is{1} = ofset (fun (i : int) => out0{2}.[i]) is{2} /\ ofset (fun (i : int) => out1{1}.[i]) is{1} = ofset (fun (i : int) => out1{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) ). 
    alias{1} 2 t = 0. swap{1} 2 1. alias{1} 3 inr1 = (ofset (fun i => out1.[i]) is,(1 \in is) ? r1 : def_rand).
    alias{2} 2 t = 0. swap{2} 2 1. alias{2} 3 inr1 = (ofset (fun i => out1.[i]) is,(1 \in is) ? r1 : def_rand).
    transitivity{1}
      { inr1 <@ Priv.party_share(1,is,(if 1 \in is then c1 else fzero)); }
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ ofset (fun (i : int) => out0{1}.[i]) is{1} = ofset (fun (i : int) => out0{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr1} /\ inr1{1} = (ofset (fun i => out1{1}.[i]) is{1},(1 \in is{1}) ? r1{1} : def_rand) /\ ofset (fun (i : int) => out0{1}.[i]) is{1} = ofset (fun (i : int) => out0{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) )
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun (i : int) => out0{1}.[i]) is{1} = ofset (fun (i : int) => out0{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr1} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ inr1{2} = (ofset (fun i => out1{2}.[i]) is{2},(1 \in is{2}) ? r1{2} : def_rand) /\ ofset (fun (i : int) => out0{1}.[i]) is{1} = ofset (fun (i : int) => out0{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) ).
      progress. exists c0{2} c1{2} c2{2} c3{2} c4{2} is{2} out0{1} r0{2} wij{2} ws{2} => />*.
      progress. smt(). smt(). smt(). 
    inline *. auto => />*.
    transitivity{2}
      { inr1 <@ Priv.party_share(1,is,c1); }
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ ofset (fun (i : int) => out0{1}.[i]) is{1} = ofset (fun (i : int) => out0{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr1} /\ MaurerWeakMul.corrupted_set is{1} /\ ofset (fun (i : int) => out0{1}.[i]) is{1} = ofset (fun (i : int) => out0{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) )
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun (i : int) => out0{1}.[i]) is{1} = ofset (fun (i : int) => out0{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr1} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ inr1{2} = (ofset (fun i => out1{2}.[i]) is{2},(1 \in is{2}) ? r1{2} : def_rand) /\ ofset (fun (i : int) => out0{1}.[i]) is{1} = ofset (fun (i : int) => out0{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) ).
      progress. exists c0{2} c1{2} c2{2} c3{2} c4{2} is{2} out0{1} r0{2} wij{2} ws{2} => />*.
      progress. smt(). smt(). 
    call party_share_privacy => />*. auto => />*.
    inline *. auto => />*. 
    swap{1} 4 -2. swap{2} 4 -2. seq 2 2 : ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ MaurerMul.valid_inputs wij{1} ws{1} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun i => out2{1}.[i]) is{1} = ofset (fun i => out2{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) ). 
    alias{1} 2 t = 0. swap{1} 2 1. alias{1} 3 inr2 = (ofset (fun i => out2.[i]) is,(2 \in is) ? r2 : def_rand).
    alias{2} 2 t = 0. swap{2} 2 1. alias{2} 3 inr2 = (ofset (fun i => out2.[i]) is,(2 \in is) ? r2 : def_rand).
    transitivity{1}
      { inr2 <@ Priv.party_share(2,is,if 2 \in is then c2 else fzero); }
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr2} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ inr2{1} = (ofset (fun i => out2{1}.[i]) is{1},(2 \in is{1}) ? r2{1} : def_rand) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) )
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr2} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ inr2{2} = (ofset (fun i => out2{2}.[i]) is{2},(2 \in is{2}) ? r2{2} : def_rand) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) ).
      progress. exists c0{2} c1{2} c2{2} c3{2} c4{2} is{2} out0{1} out1{1} r0{1} r1{1} wij{2} ws{2} => />*.
      progress. smt(). smt(). smt(). smt(). smt().
    inline *. auto => />*.
    transitivity{2}
      { inr2 <@ Priv.party_share(2,is,c2); }
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr2} /\ MaurerWeakMul.corrupted_set is{1} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) )
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr2} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ inr2{2} = (ofset (fun i => out2{2}.[i]) is{2},(2 \in is{2}) ? r2{2} : def_rand) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) ).
      progress. exists c0{2} c1{2} c2{2} c3{2} c4{2} is{2} out0{1} out1{1} r0{2} r1{2} wij{2} ws{2} => />*.
      progress. smt(). smt(). smt(). smt().
    call party_share_privacy => />*. auto => />*.
    inline *. auto => />*. 
    swap{1} 3 -1. swap{2} 3 -1. seq 2 2 : ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ MaurerMul.valid_inputs wij{1} ws{1} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun i => out2{1}.[i]) is{1} = ofset (fun i => out2{2}.[i]) is{2} /\ ofset (fun i => out3{1}.[i]) is{1} = ofset (fun i => out3{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) /\ (3 \in is{1} => ={r3}) ). 
    alias{1} 2 t = 0. swap{1} 2 1. alias{1} 3 inr3 = (ofset (fun i => out3.[i]) is,(3 \in is) ? r3 : def_rand).
    alias{2} 2 t = 0. swap{2} 2 1. alias{2} 3 inr3 = (ofset (fun i => out3.[i]) is,(3 \in is) ? r3 : def_rand).
    transitivity{1}
      { inr3 <@ Priv.party_share(3,is,if 3 \in is then c3 else fzero); }
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr3} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ inr3{1} = (ofset (fun i => out3{1}.[i]) is{1},(3 \in is{1}) ? r3{1} : def_rand) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) )
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr3} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ inr3{2} = (ofset (fun i => out3{2}.[i]) is{2},(3 \in is{2}) ? r3{2} : def_rand) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) ).
      progress. exists c0{2} c1{2} c2{2} c3{2} c4{2} is{2} out0{1} out1{1} out2{1} r0{1} r1{1} r2{1} wij{2} ws{2} => />*.
      progress. smt(). smt(). smt(). smt(). smt(). smt(). smt(). 
    inline *. auto => />*.
    transitivity{2}
      { inr3 <@ Priv.party_share(3,is,c3); }
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr3} /\ MaurerWeakMul.corrupted_set is{1} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) )
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr3} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ inr3{2} = (ofset (fun i => out3{2}.[i]) is{2},(3 \in is{2}) ? r3{2} : def_rand) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) ).
      progress. exists c0{2} c1{2} c2{2} c3{2} c4{2} is{2} out0{1} out1{1} out2{1} r0{2} r1{2} r2{2} wij{2} ws{2} => />*.
      smt().
    call party_share_privacy => />*. auto => />*.
    inline *. auto => />*. 
    seq 2 2 : ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ MaurerMul.valid_inputs wij{1} ws{1} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun i => out2{1}.[i]) is{1} = ofset (fun i => out2{2}.[i]) is{2} /\ ofset (fun i => out3{1}.[i]) is{1} = ofset (fun i => out3{2}.[i]) is{2} /\ ofset (fun i => out4{1}.[i]) is{1} = ofset (fun i => out4{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) /\ (3 \in is{1} => ={r3}) /\ (4 \in is{1} => ={r4}) ). 
    alias{1} 2 t = 0. swap{1} 2 1. alias{1} 3 inr4 = (ofset (fun i => out4.[i]) is,(4 \in is) ? r4 : def_rand).
    alias{2} 2 t = 0. swap{2} 2 1. alias{2} 3 inr4 = (ofset (fun i => out4.[i]) is,(4 \in is) ? r4 : def_rand).
    transitivity{1}
      { inr4 <@ Priv.party_share(4,is,if 4 \in is then c4 else fzero); }
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ ofset (fun (i : int) => out3{1}.[i]) is{1} = ofset (fun (i : int) => out3{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) /\ (3 \in is{1} => ={r3}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr4} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ ofset (fun (i : int) => out3{1}.[i]) is{1} = ofset (fun (i : int) => out3{2}.[i]) is{2} /\ inr4{1} = (ofset (fun i => out4{1}.[i]) is{1},(4 \in is{1}) ? r4{1} : def_rand) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) /\ (3 \in is{1} => ={r3}) )
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ ofset (fun (i : int) => out3{1}.[i]) is{1} = ofset (fun (i : int) => out3{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) /\ (3 \in is{1} => ={r3}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr4} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ ofset (fun (i : int) => out3{1}.[i]) is{1} = ofset (fun (i : int) => out3{2}.[i]) is{2} /\ inr4{2} = (ofset (fun i => out4{2}.[i]) is{2},(4 \in is{2}) ? r4{2} : def_rand) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) /\ (3 \in is{1} => ={r3}) ).
      progress. exists c0{2} c1{2} c2{2} c3{2} c4{2} is{2} out0{1} out1{1} out2{1} out3{1} r0{1} r1{1} r2{1} r3{1} wij{2} ws{2} => />*.
      progress. smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). 
    inline *. auto => />*.
    transitivity{2}
      { inr4 <@ Priv.party_share(4,is,c4); }
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ ofset (fun (i : int) => out3{1}.[i]) is{1} = ofset (fun (i : int) => out3{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) /\ (3 \in is{1} => ={r3}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr4} /\ MaurerWeakMul.corrupted_set is{1} /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ ofset (fun (i : int) => out3{1}.[i]) is{1} = ofset (fun (i : int) => out3{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) /\ (3 \in is{1} => ={r3}) )
      ( ={c0,c1,c2,c3,c4,is,wij,ws} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ ofset (fun (i : int) => out3{1}.[i]) is{1} = ofset (fun (i : int) => out3{2}.[i]) is{2} /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) /\ (3 \in is{1} => ={r3}) ==> ={c0,c1,c2,c3,c4,is,wij,ws,inr4} /\ MaurerWeakMul.corrupted_set is{1} /\ (MaurerMul.valid_inputs wij{1} ws{1}) /\ ofset (fun i => out0{1}.[i]) is{1} = ofset (fun i => out0{2}.[i]) is{2} /\ ofset (fun i => out1{1}.[i]) is{1} = ofset (fun i => out1{2}.[i]) is{2} /\ ofset (fun (i : int) => out2{1}.[i]) is{1} = ofset (fun (i : int) => out2{2}.[i]) is{2} /\ ofset (fun (i : int) => out3{1}.[i]) is{1} = ofset (fun (i : int) => out3{2}.[i]) is{2} /\ inr4{2} = (ofset (fun i => out4{2}.[i]) is{2},(4 \in is{2}) ? r4{2} : def_rand) /\ (0 \in is{1} => ={r0}) /\ (1 \in is{1} => ={r1}) /\ (2 \in is{1} => ={r2}) /\ (3 \in is{1} => ={r3}) ).
      progress. exists c0{2} c1{2} c2{2} c3{2} c4{2} is{2} out0{1} out1{1} out2{1} out3{1} r0{1} r1{1} r2{2} r3{1} wij{2} ws{2} => />*.
      progress. smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). 
    call party_share_privacy => />*. auto => />*.
    inline *. auto => />*. 
    wp. auto => />. progress. move :H2 H3 H4 H5 H6. rewrite -!fmap_eqIn !fdom_fzip !fdom_ofset !fsetIid => />. progress. 
    rewrite !fzip_some => />. rewrite !fdom_ofset !fdom_fzip !fdom_ofset => />*. rewrite !fsetIid => />*. rewrite !fdom_ofset => />*. rewrite !fsetIid => />*. rewrite !fdom_fzip !fdom_ofset => />. rewrite !fsetIid => />. rewrite !fdom_ofset => />. rewrite !fsetIid => />. rewrite !ofset_some /pinit => />*. 
    rewrite MaurerP.tP => />*. progress. 
    have : 0 <= i < 5. have : i \in MaurerWeakMul.P.ST.partyset. rewrite (in_subset is{2}) => />. rewrite iset_in_def => />. progress. 
    rewrite !MaurerP.get_init !andabP !andaP => />*. 
    congr. rewrite /send_messages => />. rewrite !Array5.initE !andabP !andaP => />*. rewrite /of_list !MaurerP.get_init !andabP !andaP =>/>. 
    case (i0=0) => />*. have : (ofset ("_.[_]" out0{1}) is{2}).[i] = (ofset ("_.[_]" out0{2}) is{2}).[i]. rewrite H2 => />*. rewrite !ofset_some => />*.
    case (i0=1) => />*. have : (ofset ("_.[_]" out1{1}) is{2}).[i] = (ofset ("_.[_]" out1{2}) is{2}).[i]. rewrite H3 => />*. rewrite !ofset_some => />*.
    case (i0=2) => />*. have : (ofset ("_.[_]" out2{1}) is{2}).[i] = (ofset ("_.[_]" out2{2}) is{2}).[i]. rewrite H4 => />*. rewrite !ofset_some => />*.
    case (i0=3) => />*. have : (ofset ("_.[_]" out3{1}) is{2}).[i] = (ofset ("_.[_]" out3{2}) is{2}).[i]. rewrite H5 => />*. rewrite !ofset_some => />*.
    have : i0=4. smt(). progress. have : (ofset ("_.[_]" out4{1}) is{2}).[i] = (ofset ("_.[_]" out4{2}) is{2}).[i]. rewrite H6 => />*. rewrite !ofset_some => />*.
    case (i=0) => />*. rewrite H7 => />*.
    case (i=1) => />*. rewrite H8 => />*.
    case (i=2) => />*. rewrite H9 => />*.
    case (i=3) => />*. rewrite H10 => />*.
    case (i=4) => />*. rewrite H11 => />*.
    qed.

  lemma valid_inputs_raw i j x ys wid :
    i \in MaurerMul.GT.partyset => j \in MaurerMul.GT.partyset =>
    MaurerMul.valid_inputs x ys =>
    wid \in fdom (MaurerP.get ys i).`1.`2 =>
      Maurer5SS.consistent_raw_shares i j (oget (MaurerP.get ys i).`1.`2.[wid]) (oget (MaurerP.get ys j).`1.`2.[wid]).
    rewrite /valid_inputs => |>. progress. have : (MaurerMul.consistent_inputs x i j ((MaurerP.get ys i)) ((MaurerP.get ys j))). rewrite H1 => />*. clear H1. rewrite /consistent_inputs => |>. progress. move :H4. rewrite /consistent_shares => />. progress. move :H8. rewrite all_iseqE allP /get_wire_st_shr => |>. progress. have : Maurer5SS.consistent_raw_shares i j (oget (fzip ((MaurerP.get ys i)).`1.`2 ((MaurerP.get ys j)).`1.`2).[wid]).`1 (oget (fzip ((MaurerP.get ys i)).`1.`2 ((MaurerP.get ys j)).`1.`2).[wid]).`2. rewrite !fzip_some => |>. rewrite in_fsetI => |>. move :H4 H5. rewrite /get_wire_st_next /get_wire_st_fdom => |>H4 H5. rewrite -H5 => |>. rewrite -consistent_raw_shares_conv. rewrite H8 => |>*. rewrite in_iseq /get_wire_st_next => |>. move :H4 H5. rewrite /get_wire_st_next /get_wire_st_fdom => |>H4 H5. move :H1 H3. rewrite !/add_valid_share /ISet.mem /get_wire_st_next /get_wire_st_fdom !/g_valid_share /ISet_subset /get_wire_st_fdom => |>. move => K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12. move :H2. rewrite K2 /ISet.iset /get_wire_st_next iset_in_def => |>. rewrite !fzip_some => |>. move : H1 H3. rewrite !/add_valid_share !/g_valid_share => |>. rewrite /get_wire_st_fdom /get_wire_st_next /ISet.mem /ISet.iset => |>. progress. rewrite in_fsetI => |>. rewrite H14 mem_oflist in_iseq => |>. move :H2. move :H4 H5. rewrite /get_wire_st_next /get_wire_st_fdom => |>H4 H5. rewrite H5 H14 mem_oflist in_iseq => |>. qed.

  clone include WeakGateProofs with
    theory WG = MaurerWeakMul
    proof *.
    realize weak_correctness.
    rewrite /functionality => |>. progress.
    have : MaurerMul.valid_inputs x ys. move :H. rewrite !/valid_inputs => />. move => Hv.
    rewrite /unshare_input /unshare_output /unshare /g_unshare /protocol /protocol_end /local_protocol_end /mk_shares /get_wire_st_next /mul_val => />*. rewrite /get !MaurerP.get_imap => />*. rewrite /stateful_local_protocol /get_local_state /get_local_state' /rounds => />. rewrite !MaurerP.get_zip3 => />. rewrite !iseq_1 /stateful_local_protocol_end /init_local_state /update_local_state /local_gate_end => />. rewrite /MaurerAPI.mul_end /get_wire_st_fdom => />*. rewrite /IMap.set /IMap.ofset /IMap.get => />. rewrite /MaurerP.size => />.
    rewrite -fmap_eqIn => />*. rewrite !fdom_set !fdom_ofset => />*. rewrite dom_mul_end => />. rewrite equiv_mul_end /my_mul_end /mk_shares /protocol' => />. progress. rewrite !get_ofset => />. move :H. rewrite /valid_inputs => />H. have : MaurerMul.consistent_inputs x 0 0 (MaurerP.get ys 0) (MaurerP.get ys 0). rewrite H => />. rewrite /ISet.mem !iset_in_def => />. rewrite /consistent_inputs => />. rewrite !/add_valid_share !/g_valid_share /get_wire_st_next /get_wire_st_fdom /ISet.mem => |>. progress. rewrite H1 /get_wire_st_shr => />. move :H8 H9. rewrite /consistent_shares all_iseqE allP => />H8 H9.
    rewrite (inner_mul_correctness _ _ (Array5.init (fun i => MaurerP.get cs i))) => />. progress. rewrite /valid_raw_shares => />. progress. rewrite /get_shr !Array5.initE !andabP !andaP => />. rewrite !MaurerP.get_map => />. rewrite consistent_raw_shares_conv. rewrite (valid_inputs_raw i0 j x ys (snd3 x)) => />*. rewrite iset_in_def => />. rewrite iset_in_def => />. rewrite valid_wire2 => />. rewrite iset_in_def => />. rewrite /valid_raw_shares => />. progress. rewrite /get_shr !Array5.initE !andabP !andaP => />. rewrite !MaurerP.get_map => />. rewrite consistent_raw_shares_conv. rewrite (valid_inputs_raw i0 j x ys (thr3 x)) => />*. rewrite iset_in_def => />. rewrite iset_in_def => />. rewrite valid_wire3 => />. rewrite iset_in_def => />.
    rewrite /inner_mul_ends /array5_send_messages /inner_mul_starts => />*. 
    case (i = ((MaurerP.get ys 0)).`1.`1) => />. rewrite !get_set_eqE /MaurerAPI.unshare => />*. congr. rewrite Array5.tP => />. progress. rewrite !Array5.mapE => />*. rewrite !Array5.initE !andabP !andaP => />*. rewrite /uncurry3 /array5_zip3 /inner_mul_start /mul_end !Array5.initE !andabP !andaP => />*. rewrite /inner_mul_end => />*. rewrite !MaurerP.get_map => />. rewrite !MaurerP.get_zip3 /protocol'' /rounds !iseq_1 !andabP !andaP => />. rewrite (prod_id (MaurerP.get ys i0).`1) => />. rewrite get_set_eqE => />*. rewrite (valid_wid 0 i0 x ys) => />*. rewrite !iset_in_def /parties => />*. rewrite /prset /ppswap /prget !MaurerP.get_init => />. rewrite /size !andabP !andaP => />. rewrite /to_local_messages /mk_shares /mk_msgs => />. rewrite /get /merge !MaurerP.get_init /size !andabP !andaP => />. rewrite !MaurerP.get_init /size !andabP !andaP => />. rewrite !MaurerP.get_init /size !andabP !andaP => />. rewrite /protocol_round /pprempty /ppinit /pinit => />. rewrite !MaurerP.get_init /size !andabP !andaP => />. rewrite !MaurerP.get_zip3 /from_local_messages /local_protocol_round /stateful_local_protocol_round /get_local_state /get_local_state' => />. rewrite /from_local_messages /local_gate_start !MaurerP.get_init /get_shr /get_msg /local_gate_start /update_local_state /mk_shares /mk_msgs /size !andabP !andaP => />. rewrite !iseq_nil => />. rewrite /mul_start /init_local_state => />. rewrite (prod_id (MaurerP.get ys 4).`1) => />. rewrite (prod_id (MaurerP.get ys 3).`1) => />. rewrite (prod_id (MaurerP.get ys 2).`1) => />. rewrite (prod_id (MaurerP.get ys 1).`1) => />. rewrite (prod_id (MaurerP.get ys 0).`1) => />. 
    rewrite !Array.get_set_eqE => />. rewrite Array.size_init => />. rewrite Array.size_init => />. rewrite Array.size_init => />. rewrite Array.size_init => />. rewrite Array.size_init => />. 
    move => Hi0. rewrite !get_set_neqE => />. rewrite ofset_some => />*. rewrite in_fsetU in_fset1 in H1 => />*. move :H1. rewrite Hi0 => />*. congr. rewrite Array5.tP => />. progress. rewrite !Array5.initE !andabP !andaP => />*. rewrite !MaurerP.get_map => />. rewrite equiv_mul_end /my_mul_end /inner_mul_end => />*. rewrite get_set_neqE => />*. rewrite !MaurerP.get_zip3 /protocol'' !andabP !andaP /rounds => />. have : ((MaurerP.get ys 0)).`1.`1 = ((MaurerP.get ys i0)).`1.`1. rewrite (valid_wid 0 i0 x) => />*. rewrite !iset_in_def /parties => />*. move => H12. rewrite -H12 => />*. rewrite !MaurerP.get_zip3 !andabP !andaP => />. qed.
    realize weak_privacy.
    proc. sp. simplify. 
    (* change randomness *)
    transitivity{1}
      { cs <@ Rand.gen_mul_coins(p); }
      (={i,p,yi,ys} ==> ={i,p,cs,yi})
      ((MaurerWeakMul.corrupted_set i{1}) /\ MaurerMul.valid_inputs p{1} ys{1} /\ yi{1} = (MaurerWeakMul.corrupted i{1} ys{1}) /\ ={i,p,ys} ==> ={i,p} /\ (MaurerWeakMul.simulator i{1} p{1} yi{1} cs{1}) = (MaurerWeakMul.corrupted i{2} ((MaurerMul.protocol p{2} ys{2} cs{2})).`1) ).
      progress. exists (i{2}) p{2} ((MaurerWeakMul.corrupted i{2} ys{2})) ys{2} => />*. move :H H0. rewrite /corrupted_set /valid_inputs /ISet.card /corrupted_t /ISet.subset /corrupted_t => />H H0 H1 k1 k2 Hk1 Hk2. 
      progress. 
    transitivity{1}
      { cs <@ Rand.gen_coins(p); }
      (={i,p,yi,ys} ==> ={i,p,cs,yi})
      (={i,p,yi,ys} ==> ={i,p,cs,yi}).
      progress. exists i{2} p{2} yi{2} ys{2} => />*.
      progress.
    inline *. wp. sp. auto => />*.
    call sample_mul_coins => />*. trivial.
    transitivity{2}
      { cs <@ Rand.gen_mul_coins(p); }
      (MaurerMul.valid_inputs p{1} ys{1} /\ yi{1} = (MaurerWeakMul.corrupted i{1} ys{1}) /\ ={i,p,ys} /\ (MaurerWeakMul.corrupted_set i{1}) /\ (MaurerMul.valid_inputs p{1} ys{1}) ==> ={i,p} /\ (MaurerWeakMul.simulator i{1} p{1} yi{1} cs{1}) = (MaurerWeakMul.corrupted i{2} ((MaurerMul.protocol p{2} ys{2} cs{2})).`1) )
      (={i,p,ys} ==> ={i,p,cs,ys}).
      progress. exists i{2} p{2} ys{2} => />*.
      progress.
      alias{1} 1 t = 0. swap{1} 1 1. alias{1} 2 cvs = MaurerWeakMul.simulator i p yi cs.
      alias{2} 1 t = 0. swap{2} 1 1. alias{2} 2 cvs = (MaurerWeakMul.corrupted i ((MaurerMul.protocol p ys cs)).`1).
      transitivity{1}
        { cvs <@ Priv.mul_ideal(i,p,ys); }
        ( ={i,p,ys,yi} /\ (MaurerWeakMul.corrupted_set i{1}) /\ yi{1} = (MaurerWeakMul.corrupted i{1} ys{1}) ==> ={i,p,ys,yi,cvs} /\ yi{1} = (MaurerWeakMul.corrupted i{1} ys{1}) /\ cvs{1}=(MaurerWeakMul.simulator i{1} p{1} yi{1} cs{1}) )
        (MaurerMul.valid_inputs p{1} ys{1} /\ (MaurerWeakMul.corrupted_set i{1}) /\ yi{1} = (MaurerWeakMul.corrupted i{1} ys{1}) /\ ={i,p,ys} ==> ={i, p} /\ cvs{1} = (MaurerWeakMul.corrupted i{2} ((MaurerMul.protocol p{2} ys{2} cs{2})).`1) ).
      progress. exists i{2} p{2} (MaurerWeakMul.corrupted i{2} ys{2}) ys{2} => />*.
      progress. 
      inline *. auto => />. progress. rewrite /simulator => |>*. progress. rewrite /fredom -fmap_eqIn => |>. rewrite !fdom_fzip !fdom_ofset !fsetIid => |>i0 Hi0. rewrite !fzip_some => |>*. rewrite !fdom_fzip !fdom_ofset !fsetIid => |>*. rewrite !fdom_ofset !fsetIid => |>*. rewrite !fdom_fzip !fdom_ofset !fsetIid => |>. rewrite !fdom_ofset !fsetIid => |>. rewrite !ofset_some => |>*. rewrite /IMap.get /corrupted !ofset_some => |>*. rewrite MaurerP.tP => |>. progress. have : 0 <= i0 < 5. have : i0 \in MaurerWeakMul.P.ST.partyset. apply (in_subset i{2}) => />. rewrite iset_in_def => />. progress. rewrite !MaurerP.get_init !andabP !andaP /get_shr /get_msg /singl /send_messages /mul_start /IMap.ofset => |>. rewrite Array.tP => />. rewrite !Array.size_init => />. progress. rewrite !Array.get_init => />. have : 0 <= i2 < 1. smt(). move => Hi2. rewrite !Hi2 => />. rewrite !Array5.initE !andabP !andaP => />. case (i2 = 0) => />. rewrite !MaurerP.get_init !andabP !andaP => />. rewrite (prod_id (oget (ofset (MaurerWeakMul.P.ST.P.get ys{2}) i{2}).[i1]).`1) => />. rewrite /get /of_list !MaurerP.get_init !andabP !andaP => />. rewrite /ISet.mem => />. rewrite shrs_to_msgs_id => />.
    case (i1 \in i{2}) => />Hi1. rewrite !ofset_some => />*. case (i1=0) => />*. rewrite Hi1 => />*. case (i1=1) => />*. rewrite Hi1 => />*. case (i1=2) => />*. rewrite Hi1 => />*. case (i1=3) => />*. rewrite Hi1 => />*. have : i1=4. smt(). progress. rewrite Hi1 => />*.
      case (i1=0) => />*. rewrite Hi1 => />*. case (i1=1) => />*. rewrite Hi1 => />*. case (i1=2) => />*. rewrite Hi1 => />*. case (i1=3) => />*. rewrite Hi1 => />*. have : i1=4. smt(). progress. rewrite Hi1 => />*.
    rewrite /get /of_list MaurerP.get_init => />*. have : 0 <= i0 && i0 < 5. have : i0 \in MaurerWeakMul.P.ST.partyset. apply (in_subset i{2}) => />*. rewrite iset_in_def => />*. progress. rewrite andabP andaP => />*. smt().
    transitivity{2}
      { cvs <@ Priv.mul_real(i,p,ys); }
      (yi{1} = (MaurerWeakMul.corrupted i{1} ys{1}) /\ (MaurerMul.valid_inputs p{1} ys{1}) /\ MaurerWeakMul.corrupted_set i{1} /\ yi{1} = (MaurerWeakMul.corrupted i{1} ys{1}) /\ ={i,p,ys} ==> ={i,p,ys,cvs} )
      ( MaurerWeakMul.corrupted_set i{1} /\ ={i,p,ys} ==> ={i,p,ys,cvs} /\ cvs{2}=MaurerWeakMul.corrupted i{2} (MaurerMul.protocol p{2} ys{2} cs{2}).`1 ).
      progress. exists i{2} p{2} ys{2} => />*.
      progress.
    call mul_weak_privacy => />*. trivial.
    inline *. auto => />. progress. rewrite /corrupted /protocol => />. rewrite -fmap_eqIn => />. rewrite !fdom_fzip !fdom_ofset => />. rewrite !fsetIid => />. progress. rewrite !fzip_some => />. rewrite !fdom_fzip !fdom_ofset !fsetIid => />. rewrite !fdom_ofset fsetIid => />. rewrite !ofset_some => />. rewrite /get /of_list /send_messages MaurerP.get_zip3 => />*. have : 0 <= i0 < 5. have : i0 \in MaurerWeakMul.P.ST.partyset. apply (in_subset i{2}) => />. rewrite iset_in_def => />. move => domi0. rewrite !domi0 /protocol' => />*. rewrite /protocol'' iseq_1 => />*. rewrite /protocol_round /of_list !MaurerP.get_init /size !domi0 => />*. rewrite !MaurerP.get_init /size !domi0 => />. rewrite MaurerMul.ST.pmap_eqP => />*. progress. rewrite /get !MaurerP.get_init /size => />*. have : 0 <= x && x < 5. move :H7. rewrite /ISet.mem iset_in_def => />*. move => domx. rewrite !domx => />*. rewrite !MaurerP.get_init /size !domx => />. rewrite !MaurerP.get_imap /size => />. rewrite /local_protocol_round /stateful_local_protocol_round /from_local_messages !MaurerP.get_zip3 /size !domx => />. rewrite !MaurerP.get_init /size !domi0 !domx => />*. rewrite /singl Array.tP => />. rewrite !Array.size_set !Array.size_init => />. progress. rewrite !Array.get_init => />*. have : 0 <= i1 < 1. smt(). move => Hi1. rewrite !Hi1 => />. case (i1=0) => />. rewrite Array.get_set_eqE => />*. rewrite Array.size_init => />.
    rewrite /rounds /pinit /local_gate_start /get_local_state /get_local_state' /get_shr /to_local_messages /update_local_state !iseq_nil => />. rewrite /mul_start /init_local_state => />. rewrite (prod_id (MaurerP.get ys{2} x).`1) => />. rewrite !Array5.initE !domx => />. rewrite !MaurerP.get_init /size !domx => />. 
    case (x=0) => />. case (x=1) => />. case (x=2) => />. case (x=3) => />. progress. have : x=4. smt(). progress.
    move => Hi10. rewrite Array.get_set_neqE => />*. rewrite Array.get_init Hi1 => />*. smt(). 
    symmetry.
    transitivity{1}
      { cs <@ Rand.gen_coins(p); }
      (={i,p,ys} ==> ={i,p,cs,ys})
      (={i,p,ys} ==> ={i,p,cs,ys}).
      progress. exists i{1} p{1} ys{1} => />*.
      progress.
    inline *. wp. sp. auto => />*.
    call sample_mul_coins => />*. trivial. qed.
    realize gen_rand_ll.
    have : is_lossless gen_raw9. rewrite gen_raw9_ll => />*. progress.
    rewrite /gen_rand => />*. rewrite dmap_ll /gen_parties_rand. rewrite dlist_ll => |>. rewrite /gen_party_rand => />. rewrite gen_rand_ll => />. qed.
    realize valid_gen_rand.
    rewrite /gen_rand => />x rs H. qed.
    realize dom_simulator.
    rewrite /simulator /fredom => />*. rewrite /IMap.dom /IMap.zip !fdom_fzip !fdom_ofset !fsetIid => />*. qed.

end MaurerWeakMulProofs.
