require import AllCore Int List FSet SmtMap Distr PrimeField Ring.
require import Aux AuxList AuxFSet AuxSmtMap.
require import Array5 Array6 Array9.
require import NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgCircuit.
require import NextMsgWeak NextMsgWeakCircuit NextMsgWeakCircuitProofs.
require import NextMsgMaurer NextMsgMaurerMPC NextMsgMaurerAuxProofs NextMsgMaurerAddProofs.
require import NextMsgISet NextMsgIMap NextMsgMaurerP NextMsgMaurerAPI.

require import Maurer5Spec.
import Maurer5Spec Maurer5SS.
import MaurerAPI.

theory MaurerWeakConstProofs.

  lemma valid_wid i1 i2 x ys :
    i1 \in MaurerConst.GT.partyset /\ i2 \in MaurerConst.GT.partyset /\ MaurerConst.valid_inputs x ys =>
      ((MaurerP.get ys i1)).`1.`1 = ((MaurerP.get ys i2)).`1.`1.
    rewrite /valid_inputs => />. progress. have : (MaurerConst.consistent_inputs x i1 i2 ((MaurerP.get ys i1)) ((MaurerP.get ys i2))). rewrite H1 => />*. rewrite /consistent_inputs => />. qed.

  clone include WeakGateProofs with
    theory WG = MaurerWeakConst
    proof *.
    realize weak_correctness.
    rewrite /functionality /unshare_input /unshare_output /unshare /g_unshare /get_wire_st_next /get_wire_st_fdom => |>x ys cs H H0. rewrite /protocol /IMap.set /IMap.ofset /protocol_end /protocol' => |>. rewrite /local_protocol_end /rounds !MaurerP.get_imap => |>. rewrite /stateful_local_protocol_end /get_local_state /get_local_state' !MaurerP.get_zip3 => |>. rewrite /to_local_messages /update_local_state /init_local_state /local_gate_end /protocol'' !iseq_1 => |>. rewrite /cnst /mk_shares /size => |>. rewrite (prod_id (MaurerP.get ys 0).`1) => |>. 
    rewrite -fmap_eqIn => />*. rewrite !fdom_set !fdom_ofset => />j Hj. rewrite !get_ofset => />*. rewrite Hj => />*. 
    have : MaurerConst.valid_inputs x ys. move :H. rewrite /valid_inputs => />H k1 k2 Hk1 Hk2.  move => H1.  
    case (j=((MaurerP.get ys 0)).`1.`1) => />. rewrite get_set_eqE => />*. rewrite /unshare /g_unshare => />*. rewrite !MaurerP.get_map => />. rewrite /get_wire_st_shr !MaurerP.get_imap => />. rewrite !MaurerP.get_zip3 /size => />. rewrite (prod_id (MaurerP.get ys 0).`1) => />. rewrite (prod_id (MaurerP.get ys 1).`1) => />. rewrite (prod_id (MaurerP.get ys 2).`1) => />. rewrite !get_set_eqE => />*. rewrite (valid_wid 0 1 x ys) => />*. rewrite !iset_in_def /parties => />*. rewrite (valid_wid 0 2 x ys) => />*. rewrite !iset_in_def /parties => />*.
    rewrite /pshare => />*. rewrite /init_sh /shr_idx => />*. algebra.
    move => H2. rewrite !get_set_neqE /unshare /g_unshare => />*. rewrite !get_ofset => />*. move :Hj. rewrite in_fsetU in_fset1 H2 => />Hj. rewrite !MaurerP.get_map => />. rewrite /get_wire_st_shr !MaurerP.get_imap => />. rewrite !MaurerP.get_zip3 /size => />. rewrite (prod_id (MaurerP.get ys 0).`1) => />. rewrite (prod_id (MaurerP.get ys 1).`1) => />. rewrite (prod_id (MaurerP.get ys 2).`1) => />. rewrite !get_set_neqE => />. have : ((MaurerP.get ys 0)).`1.`1 = ((MaurerP.get ys 1)).`1.`1. rewrite (valid_wid 0 1 x ys) => />*. rewrite !iset_in_def /parties => />*. progress. rewrite -H3 H2 => />*. have : ((MaurerP.get ys 0)).`1.`1 = ((MaurerP.get ys 2)).`1.`1. rewrite (valid_wid 0 2 x ys) => />*. rewrite !iset_in_def /parties => />*. progress. rewrite -H3 H2 => />*. qed.
    realize weak_privacy.
    proc. wp. sp. simplify. auto => />. progress. rewrite /simulator /protocol => />*. rewrite -fmap_eqIn => />*. rewrite /fredom /corrupted fdom_fzip !fdom_ofset !fdom_fzip !fdom_ofset !fsetIid => />j Hj. rewrite fzip_some => />*. rewrite /fredom !fdom_fzip !fdom_ofset !fsetIid => />*. rewrite /fredom !ofset_some => />*. rewrite /get MaurerP.get_zip3 /size => />*. have : 0 <= j < 5. have : j \in MaurerWeakConst.P.ST.partyset. apply (in_subset i{2}) => />. rewrite iset_in_def => />. move => H3. rewrite H3 => />*. rewrite /protocol' /IMap.get /IMap.ofset /IMap.zip => />. rewrite !fzip_some => />. rewrite !fdom_ofset !fsetIid => />. rewrite !ofset_some => />*. rewrite /protocol'' /rounds !iseq_1 => />. rewrite /singl /pprset /pprempty MaurerP.get_init /size => />*. rewrite !H3 => />*. rewrite MaurerP.tP => />k Hk1 Hk2. rewrite !MaurerP.get_init /size !H3 !andabP !andaP => />*. rewrite /protocol_round !MaurerP.get_init !andabP !andaP => />*. rewrite Array.tP => />*. rewrite /get !MaurerP.get_imap /local_protocol_round => />. rewrite !MaurerP.get_zip3 !andabP !andaP => />. rewrite !Array.size_set !Array.size_init => />. qed.
    realize gen_rand_ll.
    rewrite /gen_rand => />*. smt(dunit_ll). qed.
    realize valid_gen_rand.
    rewrite /gen_rand => />x rs H. qed.
    realize dom_simulator.
    rewrite /simulator => />i ws r. rewrite /IMap.dom /IMap.zip !fdom_fzip !fdom_ofset => />*. rewrite !fsetIid => />*. qed.

end MaurerWeakConstProofs.
