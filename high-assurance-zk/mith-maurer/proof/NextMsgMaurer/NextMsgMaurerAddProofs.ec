require import AllCore Int List FSet SmtMap Distr PrimeField Ring.
require import Aux AuxList AuxFSet AuxSmtMap.
require import Array5 Array6 Array9.
require import NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgCircuit.
require import NextMsgWeak NextMsgWeakCircuit NextMsgWeakCircuitProofs NextMsgMaurer NextMsgMaurerMPC NextMsgMaurerAuxProofs.
require import NextMsgISet NextMsgIMap NextMsgMaurerP NextMsgMaurerAPI.

require import Maurer5Spec.
import Maurer5Spec Maurer5SS.
import MaurerAPI.

op add_shrs (sh1 sh2 : shrs) =
    let add0 = Maurer5Spec.add_shr sh1.[0] sh2.[0] in
    let add1 = Maurer5Spec.add_shr sh1.[1] sh2.[1] in
    let add2 = Maurer5Spec.add_shr sh1.[2] sh2.[2] in
    let add3 = Maurer5Spec.add_shr sh1.[3] sh2.[3] in
    let add4 = Maurer5Spec.add_shr sh1.[4] sh2.[4] in
    let adds = Array5.of_list witness (add0::add1::add2::add3::add4::[]) in
    adds.

lemma add_shr_strong (sh1 sh2 : shrs) : 
    fadd (Maurer5SS.unshare sh1) (Maurer5SS.unshare sh2) = Maurer5SS.unshare (add_shrs sh1 sh2).
  rewrite /add_shrs /add_shr /unshare /init_sh /shr_idx /sum_rand /to_list /mkseq /=.
  by simplify;ring. qed.

theory MaurerWeakAddProofs.

  lemma get_p (xs:'a MaurerP.arrayN) i :
    MaurerP.get xs i = MaurerP.get xs i. progress. qed.

  lemma dom_add wi wj st :
    fdom (Maurer5Spec.add wi wj st).`2 = fdom st.`2 `|` fset1 st.`1.
    rewrite /add => />*. rewrite (prod_id st) => />*. rewrite fdom_set => />*. qed.

  lemma dom_unshare xs :
    fdom (g_unshare xs).`2 = fdom (MaurerP.get xs 0).`1.`2.
    rewrite /unshare => />*. rewrite dom_g_unshare => />*. qed.

  lemma wire_unshare xs :
    (g_unshare xs).`1 = (MaurerP.get xs 0).`1.`1.
    rewrite /unshare => />*. qed.

   lemma valid_wire2 i g ws :
    i \in MaurerAdd.GT.partyset /\ MaurerAdd.valid_inputs g ws => g.`2.`1 \in fdom (MaurerP.get ws i).`1.`2.
    rewrite /MaurerAdd.valid_inputs => />H H0. have : (MaurerAdd.consistent_inputs g i i ((MaurerP.get ws i)) ((MaurerP.get ws i))). rewrite H0 => />*. rewrite /consistent_inputs => />H1 H2.  qed.

  lemma valid_wire3 i g ws :
    i \in MaurerAdd.GT.partyset /\ MaurerAdd.valid_inputs g ws => g.`2.`2 \in fdom (MaurerP.get ws i).`1.`2.
    rewrite /MaurerAdd.valid_inputs => />H H0. have : (MaurerAdd.consistent_inputs g i i ((MaurerP.get ws i)) ((MaurerP.get ws i))). rewrite H0 => />*. rewrite /consistent_inputs => />H1 H2.  qed.

  lemma valid_wid i1 i2 x ys :
    i1 \in MaurerAdd.GT.partyset /\ i2 \in MaurerAdd.GT.partyset /\ MaurerAdd.valid_inputs x ys =>
      ((MaurerP.get ys i1)).`1.`1 = ((MaurerP.get ys i2)).`1.`1.
    rewrite /MaurerAdd.valid_inputs => />H H0 H1. have : (MaurerAdd.consistent_inputs x i1 i2 ((MaurerP.get ys i1)) ((MaurerP.get ys i2))). rewrite H1 => />*. rewrite /consistent_inputs => />H2 H3 H4. qed.

  clone include WeakGateProofs with
    theory WG = MaurerWeakAdd
    proof *.
    realize weak_correctness.
    progress. rewrite !/functionality /unshare_output /unshare_input /unshare /g_unshare !/protocol => |>*. rewrite /functionality /get_wire_st_next /IMap.ofset /protocol_end /mk_shares => |>*. rewrite !MaurerP.get_imap => |>*. rewrite /local_protocol_end /stateful_local_protocol_end !MaurerP.get_zip3 /local_gate_end /add => |>*. rewrite (prod_id (W.P.get_local_state 0 (W.P.ST.rounds x) x (MaurerP.get ys 0) (MaurerP.get cs 0) (MaurerP.get (W.P.protocol' x ys cs) 0)).`1.`1) => |>*. rewrite /get_local_state /get_local_state' /rounds /add => |>*. rewrite !iseq_1 /IMap.set /IMap.get => |>*. 
    rewrite -fmap_eqIn => |>*. rewrite !fdom_set => |>*. rewrite !fdom_ofset => |>*. rewrite /get_wire_st_fdom /update_local_state /to_local_messages /init_local_state => |>*. rewrite !fdom_set => |>. move => i H1. rewrite !get_ofset => |>*. rewrite H1 => |>*. 
    case (i = ((MaurerP.get ys 0)).`1.`1) => |>. rewrite !get_set_eqE => |>*. move :H. rewrite /valid_inputs => |>H. have : MaurerAdd.consistent_inputs x 0 0 (MaurerP.get ys 0) (MaurerP.get ys 0). rewrite H => |>*. rewrite /ISet.mem !iset_in_def /parties => |>*. rewrite /consistent_inputs /consistent_shares /add_val /add_valid_share => |>. rewrite /g_valid_share /get_wire_st_next /ISet_mem /get_wire_st_fdom /ISet.mem => |>. progress. rewrite add_shr_strong /MaurerAPI.unshare => |>. congr. rewrite /add_shrs Array5.tP => |>. progress. rewrite Array5.get_of_list => |>*. rewrite Array5.initE => |>*. rewrite !MaurerP.get_map /get_wire_st_shr => |>*. rewrite (prod_id (fst3 (MaurerP.get (W.P.ST.P.zip3 ys cs (W.P.protocol' x ys cs)) i0)).`1) => |>*. rewrite !MaurerP.get_zip3 => |>*. rewrite /add_shr /map2 !andabP !andaP => |>*. rewrite get_set_eqE => |>. have : ((MaurerP.get ys 0)).`1.`1 = ((MaurerP.get ys i0)).`1.`1. rewrite (valid_wid 0 i0 x ys) => |>*. rewrite !iset_in_def => |>*. rewrite /valid_inputs. progress. 
    case (i0=0) => |>. case (i0 = 1) => |>*. case (i0 = 2) => |>*. case (i0 = 3) => |>*. have : i0 = 4. smt(). progress. move => H2.
    rewrite !get_set_neqE => |>*. rewrite get_ofset => |>*. rewrite in_fsetU in_fset1 in H1 => |>*. move :H1. rewrite H2 => |>H3. congr. rewrite Array5.tP => |>j Hj1 Hj2. rewrite !Array5.initE => |>*. rewrite !andabP !andaP => |>*. rewrite /add => |>*. rewrite !MaurerP.get_map => |>. rewrite (prod_id (fst3 (MaurerP.get (W.P.ST.P.zip3 ys cs (W.P.protocol' x ys cs)) j)).`1) => |>. rewrite /get_wire_st_shr !MaurerP.get_zip3 !andabP !andaP => |>. rewrite get_set_neqE => |>. have : (MaurerP.get ys 0).`1.`1 = (MaurerP.get ys j).`1.`1. move :H. rewrite /valid_inputs => |>H. have : MaurerAdd.consistent_inputs x 0 j (MaurerP.get ys 0) (MaurerP.get ys j). rewrite H => |>. rewrite /ISet.mem !iset_in_def /parties => |>. rewrite /consistent_inputs => |>. rewrite !/add_valid_share => |>. rewrite /get_wire_st_next => |>. progress. rewrite -H4 H8 => |>. progress. rewrite -H1 => |>. qed.
    realize weak_privacy.
    proc. wp. sp. simplify. auto => |>. progress. rewrite /simulator /protocol => |>*. rewrite -fmap_eqIn => |>. rewrite /simulator /corrupted !/IMap.zip !/IMap.ofset !fdom_fzip !fdom_ofset !fsetIid => |>j Hj. rewrite !fzip_some => |>. rewrite !fdom_fzip !fdom_ofset !fsetIid => |>. rewrite !fdom_ofset !fsetIid => |>. rewrite !get_ofset => |>. rewrite !Hj => |>. rewrite /IMap.get /get MaurerP.get_zip3 => |>. have : 0 <= j < 5. have : j \in W.P.ST.partyset. apply (in_subset i{2}) => |>. move :H. rewrite /corrupted_set => />. rewrite iset_in_def => |>. move => Hj1. rewrite Hj1 => |>. rewrite get_ofset Hj => |>. rewrite MaurerP.tP => |>k Hk1 Hk2. rewrite /protocol' /protocol'' !MaurerP.get_init andabP andaP => |>. rewrite iseq_1 => |>. rewrite !MaurerP.get_init => />. have : 0 <= j < MaurerP.size. smt(). move => H2. rewrite H2 => />. rewrite !MaurerP.get_init !andabP !andaP => />. smt(). smt(). rewrite !MaurerP.get_init andabP andaP =>/>. rewrite /protocol_round => />. rewrite /get MaurerP.get_imap /local_protocol_round /from_local_messages => />. rewrite /rounds MaurerP.get_init => />. rewrite Array.tP => />. rewrite Array.size_set !Array.size_init => />. qed.
    realize gen_rand_ll.
    rewrite /gen_rand => |>*. smt(dunit_ll). qed.
    realize valid_gen_rand.
    rewrite /gen_rand => |>x rs H. rewrite /valid_rands => />i j H1. qed.
    realize dom_simulator.
    rewrite /simulator => |>. progress. rewrite /IMap.dom /IMap.zip /IMap.ofset !fdom_fzip !fdom_ofset !fsetIid => |>. qed.

end MaurerWeakAddProofs.

