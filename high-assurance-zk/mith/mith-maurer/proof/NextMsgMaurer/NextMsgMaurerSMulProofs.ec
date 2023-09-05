require import AllCore Int List FSet SmtMap Distr PrimeField Ring.
require import Aux AuxList AuxFSet AuxSmtMap.
require import Array5 Array6 Array9.
require import NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgCircuit.
require import NextMsgWeak NextMsgMaurer NextMsgMaurerMPC NextMsgMaurerAuxProofs NextMsgMaurerAddProofs NextMsgWeakCircuit NextMsgWeakCircuitProofs.

require import NextMsgISet NextMsgIMap NextMsgMaurerP NextMsgMaurerAPI.

require import Maurer5Spec.
import Maurer5Spec Maurer5SS.
import MaurerAPI.

theory MaurerWeakSMulProofs.
    
  lemma get_p (xs:'a MaurerP.arrayN) i :
    MaurerP.get xs i = MaurerP.get xs i. progress. qed.

  lemma get_gt_p (xs:'a MaurerP.arrayN) i :
    MaurerP.get xs i = MaurerP.get xs i. progress. qed.

  lemma valid_wire2 i g ws :
    i \in MaurerSMul.GT.partyset /\ MaurerSMul.valid_inputs g ws => g.`2.`1 \in fdom (MaurerP.get ws i).`1.`2.
    rewrite /valid_inputs => />H H0. have : (MaurerSMul.consistent_inputs g i i ((MaurerP.get ws i)) ((MaurerP.get ws i))). rewrite H0 => />*. rewrite /consistent_inputs => />H1 H2. qed.

  lemma valid_wire3 i g ws :
    i \in MaurerSMul.GT.partyset /\ MaurerSMul.valid_inputs g ws => g.`2.`2 \in fdom (MaurerP.get ws i).`1.`2.
    rewrite /valid_inputs => />H H0. have : (MaurerSMul.consistent_inputs g i i ((MaurerP.get ws i)) ((MaurerP.get ws i))). rewrite H0 => />*. rewrite /consistent_inputs => />H1 H2. qed.

  lemma valid_wid i1 i2 x ys :
    i1 \in MaurerSMul.GT.partyset /\ i2 \in MaurerSMul.GT.partyset /\ MaurerSMul.valid_inputs x ys =>
      ((MaurerP.get ys i1)).`1.`1 = ((MaurerP.get ys i2)).`1.`1.
    rewrite /valid_inputs => />H H0 H1. have : (MaurerSMul.consistent_inputs x i1 i2 ((MaurerP.get ys i1)) ((MaurerP.get ys i2))). rewrite H1 => />*. rewrite /consistent_inputs => />H2 H3 H4. qed.

  lemma valid_pubs i1 i2 x ys :
    i1 \in MaurerSMul.GT.partyset /\ i2 \in MaurerSMul.GT.partyset /\ MaurerSMul.valid_inputs x ys =>
      (MaurerP.get ys i1).`2 = (MaurerP.get ys i2).`2.
    rewrite /valid_inputs => />H H0 H1. have : (MaurerSMul.consistent_inputs x i1 i2 ((MaurerP.get ys i1)) ((MaurerP.get ys i2))). rewrite H1 => />*. clear H1. rewrite /consistent_inputs => />H1 H2 H3. qed.

  lemma valid_pub_shares i j x (ys:MaurerGate.share MaurerP.arrayN) :
    i \in MaurerSMul.GT.partyset /\ j \in MaurerSMul.GT.partyset =>
    MaurerSMul.valid_inputs x ys =>
      oget (MaurerP.get ys i).`1.`2.[x.`2.`2] =
      party_pshare i (party_unpshare (oget (MaurerP.get ys j).`1.`2.[x.`2.`2])).
    rewrite /valid_inputs => />H H0 H1. have : (MaurerSMul.consistent_inputs x i j ((MaurerP.get ys i)) ((MaurerP.get ys j))). rewrite H1 => />*. clear H1. rewrite /consistent_inputs => />H1 H2 H3. move :H3. rewrite /consistent_shares => |>. progress. move :H17 H18. rewrite /ISet.all fsetallP => />H17 H18. have : consistent_pub_shares i j (oget ((MaurerP.get ys i)).`1.`2.[x.`2.`2]) (oget ((MaurerP.get ys j)).`1.`2.[x.`2.`2]). rewrite H18 => />*. rewrite /consistent_pub_shares => /> H20 H21 H22. rewrite -H22. rewrite party_pshare_unpshare => />*. qed.

  lemma valid_pub_shares0 i shr (x:MaurerSMul.Gate) (ys:MaurerSMul.share MaurerP.arrayN) :
    i \in MaurerSMul.GT.partyset /\ 0 <= shr < 6 /\ MaurerSMul.valid_inputs x ys => (oget (MaurerP.get ys i).`1.`2.[x.`2.`2]).[shr] =
      (party_pshare i (party_unpshare (oget (MaurerP.get ys 0).`1.`2.[x.`2.`2]))).[shr].
    progress. rewrite (valid_pub_shares i 0 x ys) => />*. move :H. rewrite !iset_in_def /parties => />*. qed.

  lemma wire_unshare xs :
    (g_unshare xs).`1 = (MaurerP.get xs 0).`1.`1.
    rewrite /unshare => />*. qed.

  lemma dom_smul wi wj st :
    fdom (Maurer5Spec.smul wi wj st).`2 = fdom st.`2 `|` fset1 st.`1.
    rewrite /smul => />*. rewrite (prod_id st) => />*. rewrite fdom_set => />*. qed.

  clone include WeakGateProofs with
    theory WG = MaurerWeakSMul
    proof *.
    realize weak_correctness.
    rewrite /functionality => />x ys cs H H0. rewrite !/unshare_input !/unshare_ouput !/unshare /g_unshare /mul_val /get_wire_st_next /get_wire_st_fdom /mk_shares /protocol /protocol_end /protocol' /protocol'' /unshare_output /unshare_input /get_wire_st_next /unshare /g_unshare => />. rewrite !MaurerP.get_imap => />. rewrite !MaurerP.get_zip3 => />. rewrite !iseq_1 /size /get_wire_st_next /protocol_round /local_protocol_end /pprset => />. rewrite /stateful_local_protocol_round /get_local_state /get_local_state' !MaurerP.get_init /stateful_local_protocol_end /size /update_local_state => />. rewrite /local_gate_end /rounds !iseq_1 => />. rewrite /init_local_state /mk_shares /get_wire_st_fdom /pprempty /ppswap /unshare /smul => />.  rewrite (prod_id (MaurerP.get ys 0).`1) => />. 
    have : MaurerSMul.valid_inputs x ys. move :H. rewrite /valid_inputs => />H i j Hi Hj. move => H2.
    rewrite -fmap_eqIn => />. rewrite !fdom_set !fdom_ofset => />. move => i Hi. rewrite !get_ofset Hi => />. rewrite /IMap.ofset /IMap.get /IMap.set => />. rewrite !get_ofset => />. move :H. rewrite /valid_inputs => />H. have : MaurerSMul.consistent_inputs x 0 0 (MaurerP.get ys 0) (MaurerP.get ys 0). rewrite H => />. rewrite /ISet.mem !iset_in_def => />. rewrite /consistent_inputs /smul_valid_share /add_valid_share /get_wire_st_fdom /get_wire_st_next /ISet.mem => />. rewrite /get_wire_st_fdom /get_wire_st_next /get_wire_st_shr => />. progress. rewrite !MaurerP.get_map => />. rewrite !MaurerP.get_zip3 /size => />. rewrite (prod_id (MaurerP.get ys 0).`1) => />. rewrite (prod_id (MaurerP.get ys 1).`1) => />. rewrite (prod_id (MaurerP.get ys 2).`1) => />.
    case (i = ((MaurerP.get ys 0)).`1.`1) => />. rewrite !get_set_eqE => />*. rewrite (valid_wid 0 1 x ys) => />. rewrite !iset_in_def => />. rewrite (valid_wid 0 2 x ys) => />. rewrite !iset_in_def => />. 
    rewrite !(valid_pub_shares0 0 1 x ys) => />*. rewrite iset_in_def => />*.
    rewrite !(valid_pub_shares0 0 2 x ys) => />*. rewrite iset_in_def => />*.
    rewrite !(valid_pub_shares0 0 3 x ys) => />*. rewrite iset_in_def => />*.
    rewrite !(valid_pub_shares0 0 4 x ys) => />*. rewrite iset_in_def => />*.
    rewrite !(valid_pub_shares0 0 5 x ys) => />*. rewrite iset_in_def => />*.
    rewrite !(valid_pub_shares0 1 0 x ys) => />*. rewrite iset_in_def => />*. 
    rewrite !(valid_pub_shares0 1 1 x ys) => />*. rewrite iset_in_def => />*. 
    rewrite !(valid_pub_shares0 1 3 x ys) => />*. rewrite iset_in_def => />*. 
    rewrite !(valid_pub_shares0 2 1 x ys) => />*. rewrite iset_in_def => />*. 
    rewrite !(valid_pub_shares0 2 0 x ys) => />*. rewrite iset_in_def => />*. 
    rewrite !/party_pshare !/party_unpshare /pshare /init_sh /shr_idx /get_rshr =>/>*. 
    pose x200 := (oget ((MaurerP.get ys 0)).`1.`2.[x.`2.`1]).[0].
    pose x201 := (oget ((MaurerP.get ys 0)).`1.`2.[x.`2.`1]).[1].
    pose x202 := (oget ((MaurerP.get ys 0)).`1.`2.[x.`2.`1]).[2].
    pose x203 := (oget ((MaurerP.get ys 0)).`1.`2.[x.`2.`1]).[3].
    pose x204 := (oget ((MaurerP.get ys 0)).`1.`2.[x.`2.`1]).[4].
    pose x205 := (oget ((MaurerP.get ys 0)).`1.`2.[x.`2.`1]).[5].
    pose x210 := (oget ((MaurerP.get ys 1)).`1.`2.[x.`2.`1]).[0].
    pose x211 := (oget ((MaurerP.get ys 1)).`1.`2.[x.`2.`1]).[1].
    pose x213 := (oget ((MaurerP.get ys 1)).`1.`2.[x.`2.`1]).[3].
    pose x221 := (oget ((MaurerP.get ys 2)).`1.`2.[x.`2.`1]).[1].
    pose x300 := (oget ((MaurerP.get ys 0)).`1.`2.[x.`2.`2]).[0].
    ring. 
    move => Hi0. rewrite !get_set_neqE => />*. have : (MaurerP.get ys 0).`1.`1 = (MaurerP.get ys 1).`1.`1. rewrite (valid_wid 0 1 x ys) => />. rewrite !iset_in_def => />. progress. rewrite -H11 => />. have : (MaurerP.get ys 0).`1.`1 = (MaurerP.get ys 2).`1.`1. rewrite (valid_wid 0 2 x ys) => />. rewrite !iset_in_def => />. progress. rewrite -H11 => />. rewrite get_ofset => />*. rewrite in_fsetU in_fset1 in Hi => />*. move :Hi. rewrite Hi0 => />Hi. congr. rewrite !MaurerP.get_map => />. rewrite !MaurerP.get_map => />. qed.
    realize weak_privacy.
    proc. wp. sp. simplify. auto => />. progress. rewrite /simulator /protocol => />*. rewrite -fmap_eqIn => />*. rewrite /corrupted /IMap.zip fdom_fzip !fdom_ofset !fdom_fzip !fdom_ofset !fsetIid => />j Hj. rewrite fzip_some => />*. rewrite /IMap.redom /fredom !fdom_fzip !fdom_ofset !fsetIid => />*. rewrite /fredom !ofset_some => />*. rewrite !fzip_some => />. rewrite !fdom_ofset fsetIid => />. rewrite /IMap.ofset /IMap.get !ofset_some => />*. rewrite /get !MaurerP.get_zip3 /size => />*. have : 0 <= j < 5. have : j \in MaurerWeakSMul.P.ST.partyset. rewrite (in_subset i{2}) => />*. rewrite !iset_in_def => />. move => H3. rewrite H3 => />*. rewrite /protocol' /protocol'' /rounds !iseq_1 /pprset => />. rewrite !MaurerP.get_init /size !H3 /pprempty /ppswap /ppinit => />. rewrite !MaurerP.get_init /size !H3 => />. rewrite MaurerSMul.GT.pmap_eqP => />x Hx. rewrite /get !MaurerP.get_init /size => />. have : 0 <= x < 5. move :Hx. rewrite /ISet.mem !iset_in_def => />. move => H4. rewrite !H4 => />. rewrite !MaurerP.get_init /size !H4 => />. rewrite /protocol_round => />*. rewrite !MaurerP.get_init /size !H4 => />*. rewrite /singl Array.tP => />*. rewrite !Array.size_set !Array.size_init => />. qed.
    realize gen_rand_ll.
    rewrite /gen_rand => />*. smt(dunit_ll). qed.
    realize valid_gen_rand.
    rewrite /gen_rand => />x rs H. qed.
    realize dom_simulator.
    rewrite /simulator => />i ws r. rewrite /IMap.dom /IMap.zip fdom_fzip !fdom_ofset !fdom_fzip !fdom_ofset !fsetIid => />*. qed.

end MaurerWeakSMulProofs.


