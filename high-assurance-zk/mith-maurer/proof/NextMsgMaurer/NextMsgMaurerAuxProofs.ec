require import AllCore Int List FSet SmtMap Distr PrimeField Ring.
require import Aux AuxList AuxFSet AuxSmtMap AuxArray.
require import Array5 Array6 Array9 Array10.
require import NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgCircuit.
require import NextMsgMaurer NextMsgMaurerMPC NextMsgMaurerP NextMsgMaurerAPI.
require import NextMsgISet NextMsgIMap.

require import Maurer5Spec Maurer5SS.
import Maurer5Spec.
import Maurer5SS.
import MaurerAPI.

lemma dom_g_unshare xs :
  fdom (g_unshare xs).`2 = fdom (MaurerP.get xs 0).`1.`2.
  rewrite /g_unshare => />*. rewrite fdom_ofset => />*. qed.

lemma wire_g_unshare xs :
  (g_unshare xs).`1 = (MaurerP.get xs 0).`1.`1.
  rewrite /g_unshare => />*. qed.

lemma mpc_valid_inputsE x ws :
  MaurerReveal.valid_inputs x ws = MaurerCircuit.valid_inputs x ws.
  rewrite /MaurerReveal.valid_inputs /MaurerCircuit.valid_inputs => />*. 
  qed.

lemma party_unpshare_pshare i v :
  i \in MaurerSMul.ST.partyset =>
  party_unpshare (party_pshare i v) = v.
  rewrite /party_pshare /party_unpshare => />H. rewrite /pshare => />*. rewrite Array5.initE => />*. have : 0 <= i && i < 5. move :H. rewrite /partyset iset_in_def => />*. move => H0. rewrite H0 => />*. rewrite /init_sh /get_rshr => />*.
  rewrite (nth_map witness) => />*. rewrite size_shr_idx => />*. rewrite Array10.get_of_list => />*. 
  have : 0 <= nth witness (Maurer5SS.shr_idx i) 0 < 10. rewrite rng_shr_idx => />*. smt().
  rewrite shr_idx_nth_0 => />*. smt(). qed. 

lemma party_pshare_unpshare i s :
  i \in MaurerSMul.ST.partyset =>
  check_pshare i s =>
    party_pshare i (party_unpshare s) = s.
  rewrite /check_pshare !/party_pshare /party_unpshare => />H H0. rewrite -H0 => />*. qed.

op array5_send_messages (xs:('a Array5.t) Array5.t) : ('a Array5.t) Array5.t =
  Array5.init (fun i => Array5.init (fun j => xs.[j].[i] )).

lemma cr_set_ind cr (P: int fset -> bool) :
  card cr = 2 /\ cr \subset MaurerSMul.ST.partyset =>
  P (oflist [0;1]) =>
  P (oflist [0;2]) =>
  P (oflist [0;3]) =>
  P (oflist [0;4]) =>
  P (oflist [1;2]) =>
  P (oflist [1;3]) =>
  P (oflist [1;4]) =>
  P (oflist [2;3]) =>
  P (oflist [2;4]) =>
  P (oflist [3;4]) =>
  P cr.
  progress. move :H0. rewrite card2E => />H0. move :H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. rewrite !oflist_cons !oflist_nil !fsetU0 subsetP /(<=) => />. progress. have : uniq (elems cr). rewrite uniq_elems => />*. rewrite (size2E (elems cr)) => />*. move :H. rewrite cardE => />*. have : nth witness (elems cr) 0 \in MaurerSMul.ST.partyset. rewrite H0 => />*. rewrite in_fsetU !in_fset1 => />*. move => in0. have : nth witness (elems cr) 1 \in MaurerSMul.ST.partyset. rewrite H0 => />*. rewrite in_fsetU !in_fset1 => />*. move => in1. clear H0. move :in0 in1. rewrite /partyset !iset_in_def => />*.
  case (nth witness (elems cr) 0=0). move => cr00. progress.
  case (nth witness (elems cr) 1=1). move => cr11. progress. rewrite cr00 cr11 => />*.
  case (nth witness (elems cr) 1=2). move => cr12. progress. rewrite cr00 cr12 => />*. 
  case (nth witness (elems cr) 1=3). move => cr13. progress. rewrite cr00 cr13 => />*. 
  case (nth witness (elems cr) 1=4). move => cr14. progress. rewrite cr00 cr14 => />*. 
  progress. have : false. smt(). progress.
  case (nth witness (elems cr) 0=1). move => cr01. progress.
  case (nth witness (elems cr) 1=0). move => cr10. rewrite cr01 cr10 => />*. rewrite fsetUC => />*.
  case (nth witness (elems cr) 1=2). move => cr12. rewrite cr01 cr12 => />*.
  case (nth witness (elems cr) 1=3). move => cr13. rewrite cr01 cr13 => />*.
  case (nth witness (elems cr) 1=4). move => cr14. rewrite cr01 cr14 => />*.
  progress. have : false. smt(). progress.
  case (nth witness (elems cr) 0=2). move => cr02. progress. 
  case (nth witness (elems cr) 1=0). move => cr10. rewrite cr02 cr10 => />*. rewrite fsetUC => />*.
  case (nth witness (elems cr) 1=1). move => cr11. rewrite cr02 cr11 => />*. rewrite fsetUC => />*.
  case (nth witness (elems cr) 1=3). move => cr13. rewrite cr02 cr13 => />*.
  case (nth witness (elems cr) 1=4). move => cr14. rewrite cr02 cr14 => />*.
  progress. have : false. smt(). progress.
  case (nth witness (elems cr) 0=3). move => cr03. progress.
  case (nth witness (elems cr) 1=0). move => cr10. rewrite cr03 cr10 => />*. rewrite fsetUC => />*.
  case (nth witness (elems cr) 1=1). move => cr11. rewrite cr03 cr11 => />*. rewrite fsetUC => />*.
  case (nth witness (elems cr) 1=2). move => cr12. rewrite cr03 cr12 => />*. rewrite fsetUC => />*.
  case (nth witness (elems cr) 1=4). move => cr14. rewrite cr03 cr14 => />*.
  progress. have : false. smt(). progress.
  case (nth witness (elems cr) 0=4). move => cr04. progress.
  case (nth witness (elems cr) 1=0). move => cr10. rewrite cr04 cr10 => />*. rewrite fsetUC => />*.
  case (nth witness (elems cr) 1=1). move => cr11. rewrite cr04 cr11 => />*. rewrite fsetUC => />*.
  case (nth witness (elems cr) 1=2). move => cr12. rewrite cr04 cr12 => />*. rewrite fsetUC => />*.
  case (nth witness (elems cr) 1=3). move => cr13. rewrite cr04 cr13 => />*. rewrite fsetUC => />*.
  progress. have : false. smt(). progress.
  progress. have : false. smt(). progress. qed.

  lemma add_p_shr_0_1 s0 s1 :
    (add_p_shr 0 s0 (add_p_shr 1 s1 (Array10.create None))) =
      Array10.of_list witness [None;Some s1.[0];Some s1.[1];Some s1.[3];Some s0.[4];Some s0.[0];Some s0.[5];Some s0.[3];Some s0.[2];Some s0.[1]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_1_0 s1 s0 :
    (add_p_shr 1 s1 (add_p_shr 0 s0 (Array10.create None))) =
      Array10.of_list witness [None;Some s1.[0];Some s1.[1];Some s1.[3];Some s0.[4];Some s0.[0];Some s0.[5];Some s1.[5];Some s1.[4];Some s1.[2]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_0_2 s0 s2 :
    (add_p_shr 0 s0 (add_p_shr 2 s2 (Array10.create None))) =
      Array10.of_list witness [Some s2.[1];None;Some s2.[2];Some s2.[5];Some s0.[4];Some s0.[0];Some s0.[5];Some s0.[3];Some s0.[2];Some s0.[1]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_2_0 s2 s0 :
    (add_p_shr 2 s2 (add_p_shr 0 s0 (Array10.create None))) =
      Array10.of_list witness [Some s2.[1];None;Some s2.[2];Some s2.[5];Some s0.[4];Some s2.[3];Some s2.[0];Some s0.[3];Some s0.[2];Some s2.[4]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_0_3 s0 s3 :
    (add_p_shr 0 s0 (add_p_shr 3 s3 (Array10.create None))) =
      Array10.of_list witness [Some s3.[4];Some s3.[5];None;Some s3.[0];Some s0.[4];Some s0.[0];Some s0.[5];Some s0.[3];Some s0.[2];Some s0.[1]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_3_0 s3 s0 :
    (add_p_shr 3 s3 (add_p_shr 0 s0 (Array10.create None))) =
      Array10.of_list witness [Some s3.[4];Some s3.[5];None;Some s3.[0];Some s3.[2];Some s0.[0];Some s3.[3];Some s0.[3];Some s3.[1];Some s0.[1]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_0_4 s0 s4 :
    (add_p_shr 0 s0 (add_p_shr 4 s4 (Array10.create None))) =
      Array10.of_list witness [Some s4.[2];Some s4.[3];Some s4.[4];None;Some s0.[4];Some s0.[0];Some s0.[5];Some s0.[3];Some s0.[2];Some s0.[1]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_4_0 s4 s0 :
    (add_p_shr 4 s4 (add_p_shr 0 s0 (Array10.create None))) =
      Array10.of_list witness [Some s4.[2];Some s4.[3];Some s4.[4];None;Some s4.[1];Some s4.[5];Some s0.[5];Some s4.[0];Some s0.[2];Some s0.[1]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_1_2 s1 s2 :
    (add_p_shr 1 s1 (add_p_shr 2 s2 (Array10.create None))) =
      Array10.of_list witness [Some s2.[1];Some s1.[0];Some s1.[1];Some s1.[3];None;Some s2.[3];Some s2.[0];Some s1.[5];Some s1.[4];Some s1.[2]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_2_1 s2 s1 :
    (add_p_shr 2 s2 (add_p_shr 1 s1 (Array10.create None))) =
      Array10.of_list witness [Some s2.[1];Some s1.[0];Some s2.[2];Some s2.[5];None;Some s2.[3];Some s2.[0];Some s1.[5];Some s1.[4];Some s2.[4]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_1_3 s1 s3 :
    (add_p_shr 1 s1 (add_p_shr 3 s3 (Array10.create None))) =
      Array10.of_list witness [Some s3.[4];Some s1.[0];Some s1.[1];Some s1.[3];Some s3.[2];None;Some s3.[3];Some s1.[5];Some s1.[4];Some s1.[2]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_3_1 s3 s1 :
    (add_p_shr 3 s3 (add_p_shr 1 s1 (Array10.create None))) =
      Array10.of_list witness [Some s3.[4];Some s3.[5];Some s1.[1];Some s3.[0];Some s3.[2];None;Some s3.[3];Some s1.[5];Some s3.[1];Some s1.[2]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_1_4 s1 s4 :
    (add_p_shr 1 s1 (add_p_shr 4 s4 (Array10.create None))) =
      Array10.of_list witness [Some s4.[2];Some s1.[0];Some s1.[1];Some s1.[3];Some s4.[1];Some s4.[5];None;Some s1.[5];Some s1.[4];Some s1.[2]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_4_1 s4 s1 :
    (add_p_shr 4 s4 (add_p_shr 1 s1 (Array10.create None))) =
      Array10.of_list witness [Some s4.[2];Some s4.[3];Some s4.[4];Some s1.[3];Some s4.[1];Some s4.[5];None;Some s4.[0];Some s1.[4];Some s1.[2]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_2_3 s2 s3 :
    (add_p_shr 2 s2 (add_p_shr 3 s3 (Array10.create None))) =
      Array10.of_list witness [Some s2.[1];Some s3.[5];Some s2.[2];Some s2.[5];Some s3.[2];Some s2.[3];Some s2.[0];None;Some s3.[1];Some s2.[4]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_3_2 s3 s2 :
    (add_p_shr 3 s3 (add_p_shr 2 s2 (Array10.create None))) =
      Array10.of_list witness [Some s3.[4];Some s3.[5];Some s2.[2];Some s3.[0];Some s3.[2];Some s2.[3];Some s3.[3];None;Some s3.[1];Some s2.[4]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_2_4 s2 s4:
    (add_p_shr 2 s2 (add_p_shr 4 s4 (Array10.create None))) =
      Array10.of_list witness [Some s2.[1];Some s4.[3];Some s2.[2];Some s2.[5];Some s4.[1];Some s2.[3];Some s2.[0];Some s4.[0];None;Some s2.[4]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_4_2 s4 s2 :
    (add_p_shr 4 s4 (add_p_shr 2 s2 (Array10.create None))) =
      Array10.of_list witness [Some s4.[2];Some s4.[3];Some s4.[4];Some s2.[5];Some s4.[1];Some s4.[5];Some s2.[0];Some s4.[0];None;Some s2.[4]].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_3_4 s3 s4 :
    (add_p_shr 3 s3 (add_p_shr 4 s4 (Array10.create None))) =
      Array10.of_list witness [Some s3.[4];Some s3.[5];Some s4.[4];Some s3.[0];Some s3.[2];Some s4.[5];Some s3.[3];Some s4.[0];Some s3.[1];None].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma add_p_shr_4_3 s4 s3 :
    (add_p_shr 4 s4 (add_p_shr 3 s3 (Array10.create None))) =
      Array10.of_list witness [Some s4.[2];Some s4.[3];Some s4.[4];Some s3.[0];Some s4.[1];Some s4.[5];Some s3.[3];Some s4.[0];Some s3.[1];None].
    rewrite /add_p_shr !iseq_6 => />*. rewrite /shr_idx => />*. rewrite Array10.tP => />i Hi1 Hi2.
    case (i=0) => />*. case (i=1) => />*. case (i=2) => />*. case (i=3) => />*. case (i=4) => />*. case (i=5) => />*. case (i=6) => />*. case (i=7) => />*. case (i=8) => />*. have :i=9. smt(). progress. qed.

  lemma consistent_raw_shares_any i j x ss wid :
    MaurerMPCReveal.valid_outputs x ss =>
    i \in MaurerMPCReveal.WR.W.P.ST.partyset => j \in MaurerMPCReveal.WR.W.P.ST.partyset =>
    wid \in fdom ((MaurerP.get ss i)).`1.`2 =>
      MaurerAPI.consistent_raw_shares i j (oget (MaurerP.get ss i).`1.`2.[wid]) (oget (MaurerP.get ss j).`1.`2.[wid]).
    rewrite /valid_outputs => |>H H0 H1 H2. have : (MaurerMPCReveal.WR.mpc_consistent_outputs x i j ((MaurerP.get ss i)) ((MaurerP.get ss j))). rewrite H => />*. rewrite /mpc_consistent_outputs => |>H3 H4 H5 H6. move :H6. rewrite /consistent_shares => |>H6 H7 H8 H9 H10. move :H9 H10. rewrite /ISet.all all_iseqE fsetallP allP => |>H9 H10. have : MaurerAPI.consistent_raw_shares i j (get_wire_st_shr (MaurerP.get ss i).`1 wid) (get_wire_st_shr (MaurerP.get ss j).`1 wid). rewrite H10 => |>. rewrite in_iseq => |>. move :H4. rewrite /g_valid_share => |>. rewrite !/ISet.iset !/get_wire_st_fdom !/get_wire_st_next => |>H4_1 H4_2. move :H2. rewrite H4_2 /ISet.oflist => |>. rewrite mem_oflist in_iseq => |>. rewrite /get_wire_st_shr => |>. qed.

  lemma raw_shares_conv (i:pid) (si:shr) :
    MaurerAPI.raw_shares i si = Maurer5SS.raw_shares i si.
    rewrite /raw_shares /raw_shares' => />. rewrite !foldl_iseqE /get_rshr !iseq_6 => />. qed.

  lemma consistent_raw_shares_conv i j si sj :
    MaurerAPI.consistent_raw_shares i j si sj = Maurer5SS.consistent_raw_shares i j si sj.
    rewrite /consistent_raw_shares /IMap.all !fallP /IMap.zip => />. rewrite !raw_shares_conv => />. qed.

  lemma add_p_shr_0_1_swap s0 s1 :
    Maurer5SS.consistent_raw_shares 0 1 s0 s1 =>
      add_p_shr 0 s0 (add_p_shr 1 s1 (Array10.create None)) = add_p_shr 1 s1 (add_p_shr 0 s0 (Array10.create None)).
    rewrite add_p_shr_0_1 => />*. rewrite add_p_shr_1_0 => />*. rewrite (consistent_s01_s12 s0 s1) => />. rewrite (consistent_s03_s15 s0 s1) => />*. rewrite (consistent_s02_s14 s0 s1) => />*. qed.    

  lemma add_p_shr_0_2_swap s0 s2 :
    Maurer5SS.consistent_raw_shares 0 2 s0 s2 =>
      add_p_shr 0 s0 (add_p_shr 2 s2 (Array10.create None)) = add_p_shr 2 s2 (add_p_shr 0 s0 (Array10.create None)).
    rewrite add_p_shr_0_2 => />*. rewrite add_p_shr_2_0 => />*. rewrite (consistent_s00_s23 s0 s2) => />*. rewrite (consistent_s05_s20 s0 s2) => />*. rewrite (consistent_s01_s24 s0 s2) => />*. qed.   

  lemma add_p_shr_0_3_swap s0 s3 :
    Maurer5SS.consistent_raw_shares 0 3 s0 s3 =>
      add_p_shr 0 s0 (add_p_shr 3 s3 (Array10.create None)) = add_p_shr 3 s3 (add_p_shr 0 s0 (Array10.create None)).
    rewrite add_p_shr_0_3 => />*. rewrite add_p_shr_3_0 => />*. rewrite (consistent_s04_s32 s0 s3) => />*. rewrite (consistent_s05_s33 s0 s3) => />*. rewrite (consistent_s02_s31 s0 s3) => />*. qed.   

  lemma add_p_shr_0_4_swap s0 s4 :
    Maurer5SS.consistent_raw_shares 0 4 s0 s4 =>
      add_p_shr 0 s0 (add_p_shr 4 s4 (Array10.create None)) = add_p_shr 4 s4 (add_p_shr 0 s0 (Array10.create None)).
    rewrite add_p_shr_0_4 => />*. rewrite add_p_shr_4_0 => />*. rewrite (consistent_s04_s41 s0 s4) => />*. rewrite (consistent_s00_s45 s0 s4) => />*. rewrite (consistent_s03_s40 s0 s4) => />*. qed.   

  lemma add_p_shr_1_2_swap s1 s2 :
    Maurer5SS.consistent_raw_shares 1 2 s1 s2 =>
      add_p_shr 1 s1 (add_p_shr 2 s2 (Array10.create None)) = add_p_shr 2 s2 (add_p_shr 1 s1 (Array10.create None)).
    rewrite add_p_shr_1_2 => />*. rewrite add_p_shr_2_1 => />*. rewrite (consistent_s11_s22 s1 s2) => />*. rewrite (consistent_s13_s25 s1 s2) => />*. rewrite (consistent_s12_s24 s1 s2) => />*. qed.   

  lemma add_p_shr_1_3_swap s1 s3 :
    Maurer5SS.consistent_raw_shares 1 3 s1 s3 =>
      add_p_shr 1 s1 (add_p_shr 3 s3 (Array10.create None)) = add_p_shr 3 s3 (add_p_shr 1 s1 (Array10.create None)).
    rewrite add_p_shr_1_3 => />*. rewrite add_p_shr_3_1 => />*. rewrite (consistent_s10_s35 s1 s3) => />*. rewrite (consistent_s13_s30 s1 s3) => />*. rewrite (consistent_s14_s31 s1 s3) => />*. qed.   

  lemma add_p_shr_1_4_swap s1 s4 :
    Maurer5SS.consistent_raw_shares 1 4 s1 s4 =>
      add_p_shr 1 s1 (add_p_shr 4 s4 (Array10.create None)) = add_p_shr 4 s4 (add_p_shr 1 s1 (Array10.create None)).
    rewrite add_p_shr_1_4 => />*. rewrite add_p_shr_4_1 => />*. rewrite (consistent_s10_s43 s1 s4) => />*. rewrite (consistent_s11_s44 s1 s4) => />*. rewrite (consistent_s15_s40 s1 s4) => />*. qed.   

  lemma add_p_shr_2_3_swap s2 s3 :
    Maurer5SS.consistent_raw_shares 2 3 s2 s3 =>
      add_p_shr 2 s2 (add_p_shr 3 s3 (Array10.create None)) = add_p_shr 3 s3 (add_p_shr 2 s2 (Array10.create None)).
    rewrite add_p_shr_2_3 => />*. rewrite add_p_shr_3_2 => />*. rewrite (consistent_s21_s34 s2 s3) => />*. rewrite (consistent_s25_s30 s2 s3) => />*. rewrite (consistent_s20_s33 s2 s3) => />*. qed.   

  lemma add_p_shr_2_4_swap s2 s4 :
    Maurer5SS.consistent_raw_shares 2 4 s2 s4 =>
      add_p_shr 2 s2 (add_p_shr 4 s4 (Array10.create None)) = add_p_shr 4 s4 (add_p_shr 2 s2 (Array10.create None)).
    rewrite add_p_shr_2_4 => />*. rewrite add_p_shr_4_2 => />*. rewrite (consistent_s21_s42 s2 s4) => />*. rewrite (consistent_s22_s44 s2 s4) => />*. rewrite (consistent_s23_s45 s2 s4) => />*. qed.   

  lemma add_p_shr_3_4_swap s3 s4 :
    Maurer5SS.consistent_raw_shares 3 4 s3 s4 =>
      add_p_shr 3 s3 (add_p_shr 4 s4 (Array10.create None)) = add_p_shr 4 s4 (add_p_shr 3 s3 (Array10.create None)).
    rewrite add_p_shr_3_4 => />*. rewrite add_p_shr_4_3 => />*. rewrite (consistent_s34_s42 s3 s4) => />*. rewrite (consistent_s32_s41 s3 s4) => />*. rewrite (consistent_s35_s43 s3 s4) => />*. qed.   

(*lemma get_cp (xs:'a MaurerP.t) i :
  MaurerCircuit.P.T.P.get xs i = MaurerP.get xs i. progress. qed.*)

op gate_prot (g:MaurerGate.Gate) (ws:MaurerGate.share MaurerP.arrayN) (cs:MaurerGate.GT.local_rand MaurerP.arrayN) =
    with g = MaurerGate.Add wij =>
      let r = MaurerAdd.g_protocol wij ws (MaurerP.map unL cs)
      in (MaurerP.map (fun (x:_*(_*_)) => (x.`1,(MaurerP.map (Array.map L) x.`2.`1,L x.`2.`2))) r.`1,r.`2)
    with g = MaurerGate.SMul wij =>
      let r = MaurerSMul.g_protocol wij ws (MaurerP.map unL cs)
      in (MaurerP.map (fun (x:_*(_*_)) => (x.`1,(MaurerP.map (Array.map L) x.`2.`1,L x.`2.`2))) r.`1,r.`2)
    with g = MaurerGate.Const wij =>
      let r = MaurerConst.g_protocol wij ws (MaurerP.map unL cs)
      in (MaurerP.map (fun (x:_*(_*_)) => (x.`1,(MaurerP.map (Array.map L) x.`2.`1,L x.`2.`2))) r.`1,r.`2)
    with g = MaurerGate.Mul wij =>
      let r = MaurerMul.g_protocol wij ws (MaurerP.map unR cs)
      in (MaurerP.map (fun (x:_*(_*_)) => (x.`1,(MaurerP.map (Array.map R) x.`2.`1,R x.`2.`2))) r.`1,r.`2).

lemma gate_protocol_def (g:MaurerGate.Gate) ws (rs:MaurerGate.GT.local_rand MaurerP.arrayN) :
  MaurerGate.valid_rands g rs =>
    MaurerGate.protocol g ws rs = gate_prot g ws rs.
  rewrite /gate_prot /protocol /protocol' /protocol'' /protocol_end /local_protocol_end /protocol_round /stateful_local_protocol_end /get_local_state /get_local_state' /update_local_state /g_protocol /local_protocol_round /rounds !iseq_1 => |>H. move :H. case g => |>g H.  
  (*Add*)
  rewrite MaurerGate.GT.pmap_eqP => |>. progress. rewrite !MaurerGate.GT.get_pzip3 !H0 => |>*. rewrite !MaurerGate.GT.get_pmap => |>*. rewrite !MaurerGate.GT.get_pprset /g_protocol !H0 => |>*. rewrite !MaurerGate.GT.get_pzip3 !H0 => |>*. rewrite /ppswap !MaurerGate.GT.get_pmap => |>*. rewrite /pprempty !MaurerGate.GT.get_ppinit !H0 => |>*. rewrite MaurerGate.GT.pmap_eqP => |>*. progress. rewrite !MaurerGate.GT.get_pmap => |>*. rewrite !MaurerGate.GT.get_prset !H1 => |>*. rewrite !MaurerGate.GT.get_pinit !H1 => |>*. rewrite !MaurerGate.GT.get_pimap => |>*. rewrite /from_local_messages /stateful_local_protocol_round /get_local_state /get_local_state' Array.tP => |>. rewrite Array.size_set => |>. rewrite !Array.size_init => |>. move => i Hi1 Hi2. rewrite !iseq_nil => |>. rewrite Array.get_map => |>. rewrite Array.size_init => |>. rewrite Array.get_init => |>. have : 0 <= i < 1. smt(). move => H2. rewrite H2 => |>. rewrite /get /fst3 /snd3 MaurerP.get_zip3 => |>. have : 0 <= x0 < 5. move :H1. rewrite /ISet.mem iset_in_def => |>. move => H3. rewrite !H3 => |>.
  case (i=0) => |>. rewrite Array.get_set_eqE => |>. rewrite Array.size_init => |>. rewrite /local_gate_start /init_local_state => |>. rewrite MaurerP.get_init => |>. have : 0 <= x < 5. move :H0. rewrite /ISet.mem iset_in_def => |>. move => H4. rewrite H4 => |>. move => H4. rewrite !Array.get_set_neqE => |>*. rewrite !Array.get_init => |>*. have : false. smt(). progress. move :H. rewrite /MaurerGate.valid_rands => |>H. have : MaurerGate.consistent_rands (MaurerGate.Add g) x x (MaurerP.get rs x) (MaurerP.get rs x). rewrite H => |>. rewrite /MaurerGate.consistent_rands => |>. rewrite /gate_valid_rand => |>H1. rewrite isL_id => |>. rewrite /from_local_messages /to_local_messages /g_protocol /stateful_local_protocol_round /get_local_state /get_local_state' MaurerGate.GT.pmap_eqP => |>x H0. rewrite !MaurerGate.GT.get_pimap => |>*. rewrite !MaurerGate.GT.get_pzip3 => |>*. rewrite !H0 !iseq_nil /local_gate_end /local_gate_start /init_local_state => |>*. rewrite !MaurerGate.GT.get_pzip !H0 => |>*.
  (*SMul*)
  rewrite MaurerGate.GT.pmap_eqP => |>. progress. rewrite !MaurerGate.GT.get_pzip3 !H0 => |>*. rewrite !MaurerGate.GT.get_pmap => |>*. rewrite !MaurerGate.GT.get_pprset /g_protocol !H0 => |>*. rewrite !MaurerGate.GT.get_pzip3 !H0 => |>*. rewrite /ppswap !MaurerGate.GT.get_pmap => |>*. rewrite !MaurerGate.GT.get_ppinit !H0 => |>*. rewrite MaurerGate.GT.pmap_eqP => |>*. progress. rewrite !MaurerGate.GT.get_pmap => |>*. rewrite !MaurerGate.GT.get_prset !H1 => |>*. rewrite !MaurerGate.GT.get_pinit !H1 => |>*. rewrite !MaurerGate.GT.get_pimap => |>*. rewrite /from_local_messages /stateful_local_protocol_round /get_local_state /get_local_state' Array.tP => |>. rewrite Array.size_set => |>. rewrite !Array.size_init => |>. move => i Hi1 Hi2. rewrite !iseq_nil => |>. rewrite Array.get_map => |>. rewrite Array.size_init => |>. rewrite Array.get_init => |>. have : 0 <= i < 1. smt(). move => H2. rewrite H2 => |>. rewrite /get /fst3 /snd3 MaurerP.get_zip3 => |>. have : 0 <= x0 < 5. move :H1. rewrite /ISet.mem iset_in_def => |>. move => H3. rewrite !H3 => |>.
  case (i=0) => |>. rewrite Array.get_set_eqE => |>. rewrite Array.size_init => |>. rewrite /local_gate_start /init_local_state => |>. rewrite MaurerP.get_init => |>. have : 0 <= x < 5. move :H0. rewrite /ISet.mem iset_in_def => |>. move => H4. rewrite H4 => |>. move => H4. rewrite !Array.get_set_neqE => |>*. rewrite !Array.get_init => |>*. have : false. smt(). progress. move :H. rewrite /MaurerGate.valid_rands => |>H. have : MaurerGate.consistent_rands (MaurerGate.SMul g) x x (MaurerP.get rs x) (MaurerP.get rs x). rewrite H => |>. rewrite /MaurerGate.consistent_rands => |>. rewrite /gate_valid_rand => |>H1. rewrite isL_id => |>. rewrite /from_local_messages /to_local_messages /g_protocol /stateful_local_protocol_round /get_local_state /get_local_state' MaurerGate.GT.pmap_eqP => |>x H0. rewrite !MaurerGate.GT.get_pimap => |>*. rewrite !MaurerGate.GT.get_pzip3 => |>*. rewrite !H0 !iseq_nil /local_gate_end /local_gate_start /init_local_state => |>*. rewrite !MaurerGate.GT.get_pzip !H0 => |>*.
  (*Const*)
  rewrite MaurerGate.GT.pmap_eqP => |>. progress. rewrite !MaurerGate.GT.get_pzip3 !H0 => |>*. rewrite !MaurerGate.GT.get_pmap => |>*. rewrite !MaurerGate.GT.get_pprset /g_protocol !H0 => |>*. rewrite !MaurerGate.GT.get_pzip3 !H0 => |>*. rewrite /ppswap !MaurerGate.GT.get_pmap => |>*. rewrite !MaurerGate.GT.get_ppinit !H0 => |>*. rewrite MaurerGate.GT.pmap_eqP => |>*. progress. rewrite !MaurerGate.GT.get_pmap => |>*. rewrite !MaurerGate.GT.get_prset !H1 => |>*. rewrite !MaurerGate.GT.get_pinit !H1 => |>*. rewrite !MaurerGate.GT.get_pimap => |>*. rewrite /from_local_messages /stateful_local_protocol_round /get_local_state /get_local_state' Array.tP => |>. rewrite Array.size_set => |>. rewrite !Array.size_init => |>. move => i Hi1 Hi2. rewrite !iseq_nil => |>. rewrite Array.get_map => |>. rewrite Array.size_init => |>. rewrite Array.get_init => |>. have : 0 <= i < 1. smt(). move => H2. rewrite H2 => |>. rewrite /get /fst3 /snd3 MaurerP.get_zip3 => |>. have : 0 <= x0 < 5. move :H1. rewrite /ISet.mem iset_in_def => |>. move => H3. rewrite !H3 => |>.
  case (i=0) => |>. rewrite Array.get_set_eqE => |>. rewrite Array.size_init => |>. rewrite /local_gate_start /init_local_state => |>. rewrite MaurerP.get_init => |>. have : 0 <= x < 5. move :H0. rewrite /ISet.mem iset_in_def => |>. move => H4. rewrite H4 => |>. move => H4. rewrite !Array.get_set_neqE => |>*. rewrite !Array.get_init => |>*. have : false. smt(). progress. move :H. rewrite /MaurerGate.valid_rands => |>H. have : MaurerGate.consistent_rands (MaurerGate.Const g) x x (MaurerP.get rs x) (MaurerP.get rs x). rewrite H => |>. rewrite /MaurerGate.consistent_rands => |>. rewrite /gate_valid_rand => |>H1. rewrite isL_id => |>. rewrite /from_local_messages /to_local_messages /g_protocol /stateful_local_protocol_round /get_local_state /get_local_state' MaurerGate.GT.pmap_eqP => |>x H0. rewrite !MaurerGate.GT.get_pimap => |>*. rewrite !MaurerGate.GT.get_pzip3 => |>*. rewrite !H0 !iseq_nil /local_gate_end /local_gate_start /init_local_state => |>*. rewrite !MaurerGate.GT.get_pzip !H0 => |>*.  
  (*Mul*)
  rewrite MaurerGate.GT.pmap_eqP => |>. progress. rewrite !MaurerGate.GT.get_pzip3 !H0 => |>*. rewrite !MaurerGate.GT.get_pmap => |>*. rewrite !MaurerGate.GT.get_pprset /g_protocol !H0 => |>*. rewrite !MaurerGate.GT.get_pzip3 !H0 => |>*. rewrite /ppswap !MaurerGate.GT.get_pmap => |>*. rewrite !MaurerGate.GT.get_ppinit !H0 => |>*. rewrite MaurerGate.GT.pmap_eqP => |>*. progress. rewrite !MaurerGate.GT.get_pmap => |>*. rewrite !MaurerGate.GT.get_prset !H1 => |>*. rewrite !MaurerGate.GT.get_pinit !H1 => |>*. rewrite !MaurerGate.GT.get_pimap => |>*. rewrite /from_local_messages /stateful_local_protocol_round /get_local_state /get_local_state' Array.tP => |>*. rewrite Array.size_set !Array.size_init => |>. move => i Hi1 Hi2. rewrite !Array.get_init => |>. rewrite !Array.size_init andabP andaP => |>. rewrite Array.get_init => |>. have : 0 <= i < 1. smt(). move => H4. rewrite H4 => |>. 
  case (i=0) => |>. rewrite Array.get_set_eqE => |>*. rewrite Array.size_init => |>. rewrite !iseq_nil /get_msg => |>*. rewrite /send_messages /init_local_state /local_gate_start => |>. rewrite /get !MaurerP.get_init => |>. move :H0. rewrite /ISet.mem iset_in_def /parties /get /size => |>X1 X2. rewrite /get_shr /local_gate_start /mul_start !/fst3 !/snd3 /partyset => |>. move :H1. rewrite /ISet.mem iset_in_def /parties /size => |>X01 X02. rewrite (prod_id (MaurerP.get ws x0).`1) => |>. rewrite Array5.initE andabP andaP => |>. rewrite MaurerP.get_map => |>. rewrite MaurerP.get_zip /size andabP andaP => |>. rewrite MaurerP.get_zip => |>. rewrite !MaurerP.get_map !andabP !andaP => |>. rewrite (prod_id (MaurerP.get ws x0).`1) => |>. move => H5. rewrite Array.get_set_neqE => |>. rewrite Array.get_init => |>. have : false. smt(). progress. move :H. rewrite /MaurerGate.valid_rands => |>H1. have : MaurerGate.consistent_rands (MaurerGate.Mul g) x x (MaurerP.get rs x) (MaurerP.get rs x). rewrite H1 => |>. rewrite /consistent_rands => />H2 H3. rewrite isR_id => |>. rewrite /from_local_messages /to_local_messages /g_protocol /stateful_local_protocol_round /get_local_state /get_local_state' MaurerGate.GT.pmap_eqP /partyset /parties /size => |>x H0. rewrite !MaurerGate.GT.get_pimap => |>*. rewrite !MaurerGate.GT.get_pzip3 /partyset /parties /size => |>*. rewrite !H0 !iseq_nil /local_gate_end /local_gate_start /init_local_state => |>*. rewrite !MaurerGate.GT.get_pzip !H0 => |>*. rewrite /local_gate_end /send_messages /ppswap => |>*. congr. rewrite /send_messages Array5.tP => |>i Hi1 Hi2. rewrite /partyset /parties /size MaurerGate.GT.get_pinit /partyset /parties /size H0 => |>*. rewrite !MaurerP.get_init => />. have : 0 <= x < MaurerP.size. move :H0. rewrite /ISet.mem /ISet.iset iset_in_def /size => />. move => H1. rewrite /get H1 => />. rewrite !MaurerP.get_init !H1 /prget => />. rewrite Array5.initE andabP andaP => |>. rewrite MaurerP.get_map => |>*. rewrite !MaurerP.get_zip => |>. rewrite !MaurerP.get_map !andabP !andaP => |>. rewrite /gate_to_local_messages /mk_shares /mk_msgs => />. rewrite if_then => |>. 
   rewrite MaurerP.allP => |>j Hj1 Hj2. rewrite !MaurerP.get_init andabP andaP /get => |>. rewrite /prset MaurerP.get_init andabP andaP => |>. rewrite !MaurerP.get_init !andabP !andaP => |>. rewrite !MaurerP.get_init andabP andaP => |>. rewrite MaurerP.get_init andabP andaP => />. smt(). smt(). rewrite Array.get_set_eqE => |>. rewrite Array.size_init => |>. smt(). rewrite /mk_shares => |>. rewrite Array5.initE andabP andaP => |>. rewrite MaurerP.get_map => |>. rewrite MaurerP.get_init andabP andaP /prset => |>. rewrite /get MaurerP.get_init andabP andaP => |>. rewrite MaurerP.get_init => |>. rewrite MaurerP.get_init !andabP !andaP => |>. rewrite MaurerP.get_imap => |>. rewrite MaurerP.get_init andabP andaP => |>. smt(). smt(). rewrite /get_shr Array.get_set_eqE /local_gate_start => |>. rewrite Array.size_init => |>. smt(). rewrite !MaurerP.get_init !andabP !andaP => |>. rewrite /get_msg /mul_start MaurerP.get_zip => |>. rewrite (prod_id (MaurerP.get ws i).`1) => |>. smt(). qed.

lemma g_protocol_wire g ws c i :
    i \in MaurerGate.GT.partyset =>
      (MaurerP.get (MaurerGate.g_protocol g ws c).`2 i).`1.`1 =
      (MaurerP.get ws i).`1.`1 + 1.
    move => H. have : 0 <= i && i < 5. move :H. rewrite iset_in_def => />*. move => irng.
    rewrite /g_protocol => />*. rewrite !MaurerP.get_imap => />*. smt(). rewrite /get /local_gate !MaurerP.get_zip !irng => />*. rewrite /send_messages /gate_send_messages => />.
    rewrite /local_gate_end => />*. case g => />g.
    rewrite if_else => />. rewrite MaurerP.allP negb_forall => />. exists 0 => />. rewrite !MaurerP.get_imap => />. rewrite !MaurerP.get_imap => />. smt(). rewrite /local_gate_end /local_gate_start => />. rewrite /add /snd3 /thr3 => />. rewrite (prod_id ((MaurerP.get ws i)).`1) => />*. 
    rewrite if_else => />. rewrite MaurerP.allP negb_forall => />. exists 0 => />. rewrite !MaurerP.get_imap => />. rewrite !MaurerP.get_imap => />. smt(). rewrite /local_gate_end /local_gate_start => />. rewrite /add /snd3 /thr3 => />. rewrite (prod_id ((MaurerP.get ws i)).`1) => />*.
    rewrite if_else => />. rewrite MaurerP.allP negb_forall => />. exists 0 => />. rewrite !MaurerP.get_imap => />. rewrite !MaurerP.get_imap => />. smt(). rewrite /local_gate_end /local_gate_start => />. rewrite /add /snd3 /thr3 => />. rewrite (prod_id ((MaurerP.get ws i)).`1) => />*.
    rewrite if_then => />. rewrite MaurerP.allP => />j Hj1 Hj2. rewrite MaurerP.get_imap => />. rewrite !MaurerP.get_map => />. smt(). rewrite /send_messages /local_gate_end /mul_end => />*. rewrite (prod_id ((MaurerP.get ws i)).`1) => />*. qed.

  lemma circ_protocol_wire' x ws cs i :
    i \in MaurerGate.GT.partyset =>
      (MaurerP.get ((MaurerCircuit.circ_protocol' x ws cs)).`2.`2 i).`1.`1 =
      (MaurerP.get ws i).`1.`1 + size x.
    elim x ws cs => |>. progress. rewrite H => |>*. clear H. rewrite (_:MaurerCircuit.G.g_protocol=MaurerGate.g_protocol). progress. rewrite g_protocol_wire => |>*. algebra. qed.

  lemma circ_protocol_wire x ws cs i :
    i \in MaurerGate.GT.partyset =>
      (MaurerP.get ((MaurerCircuit.circ_protocol x ws cs)).`2 i).`1.`1 =
      (MaurerP.get ws i).`1.`1 + List.size x.
    rewrite /circ_protocol iset_in_def /parties => |>Hi1 Hi2. rewrite circ_protocol_wire' => |>. rewrite iset_in_def /parties => |>. qed.

lemma check_c_wire_rcons c g i :
    MaurerCircuit.check_c_wire (rcons c g) i = (MaurerCircuit.check_c_wire c i /\ MaurerCircuit.g_wire g = i + size c).
    elim c i => |>. progress. rewrite H => |>*. rewrite (_:i + 1 + size l = i + (1 + size l)). algebra.
    rewrite eq_logical => |>*. qed.

lemma c_pubs_cons g (c:MaurerGate.Gate list) ws :
  MaurerCircuit.c_pubs (cons g c) ws = MaurerCircuit.c_pubs c (MaurerCircuit.g_pubs g ws).
  rewrite /c_pubs => |>*. qed.

lemma c_pubs_rcons (c:MaurerGate.Gate list) (g:MaurerGate.Gate) ws :
  MaurerCircuit.c_pubs (rcons c g) ws = MaurerCircuit.g_pubs g (MaurerCircuit.c_pubs c ws).
    rewrite /c_pubs foldl_rcons => |>*. qed.

lemma valid_gate_fst' n x ps :
    (MaurerCircuit.valid_gate' n x ps).`1 = MaurerCircuit.g_pubs x ps.
    case x => |>*. qed.

  lemma valid_circuit_cat' n c1 c2 ws :
    MaurerCircuit.valid_circuit' n (c1 ++ c2) ws = (MaurerCircuit.valid_circuit' n c1 ws /\ MaurerCircuit.valid_circuit' (n+size c1) c2 (MaurerCircuit.c_pubs c1 ws)).
    move:n c2 ws. elim/last_ind:c1 => |>. progress.
    rewrite cat_rcons rcons_cat => |>*. rewrite !H => |>*. rewrite size_cat => |>*. rewrite -rcons_cat c_pubs_rcons => |>*. rewrite valid_gate_fst' => |>*. rewrite eq_logical => |>*. progress. smt(). smt(). qed.    

  lemma valid_circuit_rcons' n c g ws :
    MaurerCircuit.valid_circuit' n (rcons c g) ws = (MaurerCircuit.valid_circuit' n c ws /\ (MaurerCircuit.valid_gate' (n+size c) g (MaurerCircuit.c_pubs c ws)).`2).
    rewrite rcons_cat valid_circuit_cat' => |>*. qed.

  lemma valid_circuit_cons' n c g ws :
    MaurerCircuit.valid_circuit' n (cons g c) ws = ((MaurerCircuit.valid_gate' n g ws).`2 /\ MaurerCircuit.valid_circuit' (n+1) c (MaurerCircuit.g_pubs g ws)).
    rewrite /valid_circuit' => |>*. rewrite valid_gate_fst' => |>*. qed.

  lemma valid_circuit_cons g c n ps :
    MaurerCircuit.valid_circuit (cons g c) n ps => ((MaurerCircuit.valid_gate' n g ps).`2 /\ MaurerCircuit.valid_circuit c (n+1) (MaurerCircuit.g_pubs g ps)).
    rewrite !/MaurerCircuit.valid_circuit. simplify. rewrite !valid_gate_fst'. 
    case g => |>g.
    rewrite !/ISet.subset !/ISet.iset !/ISet.oflist => |>. progress. smt(size_ge0). smt(size_ge0). move :H1. rewrite !subsetP /(<=) => |>H1 a Ha. have : a \in oflist (iseq (fst3 g)). rewrite H1 => |>. rewrite !mem_oflist => |>. rewrite !in_iseq => |>. smt(). 
    rewrite !/ISet.subset !/ISet.iset !/ISet.oflist => |>. progress. smt(size_ge0). smt(size_ge0). move :H1. rewrite !subsetP /(<=) => |>H1 a Ha. have : a \in oflist (iseq (fst3 g)). rewrite H1 => |>. rewrite !mem_oflist => |>. rewrite !in_iseq => |>. smt(). 
    rewrite !/ISet.subset !/ISet.iset !/ISet.oflist => |>. progress. smt(size_ge0). smt(size_ge0). move :H1. rewrite !subsetP /(<=) => |>H1 a Ha. move :Ha. rewrite !in_fsetU !in_fset1 => |>Ha. elim Ha => |>. move => Ha. have : a \in oflist (iseq g.`1). rewrite H1 => |>. rewrite !mem_oflist => |>. rewrite !in_iseq => |>. smt(). rewrite mem_oflist => |>. rewrite in_iseq => |>. smt().
    rewrite !/ISet.subset !/ISet.iset !/ISet.oflist => |>. progress. smt(size_ge0). smt(size_ge0). move :H1. rewrite !subsetP /(<=) => |>H1 a Ha. have : a \in oflist (iseq (fst3 g)). rewrite H1 => |>. rewrite !mem_oflist => |>. rewrite !in_iseq => |>. smt(). qed.

  lemma valid_circuit_head g c n ps :
    MaurerCircuit.valid_circuit (cons g c) n ps => (MaurerCircuit.valid_gate' n g ps).`2.
    move => H. have : ((MaurerCircuit.valid_gate' n g ps).`2 /\ MaurerCircuit.valid_circuit c (n+1) (MaurerCircuit.g_pubs g ps)). rewrite valid_circuit_cons => |>*. progress. qed.

  lemma valid_circuit_behead g c n ps :
    MaurerCircuit.valid_circuit (cons g c) n ps => MaurerCircuit.valid_circuit c (n+1) (MaurerCircuit.g_pubs g ps).
    move => ?. have : ((MaurerCircuit.valid_gate' n g ps).`2 /\ MaurerCircuit.valid_circuit c (n+1) (MaurerCircuit.g_pubs g ps)). rewrite valid_circuit_cons => |>*. progress. qed.

  lemma g_pubs_acc g acc :
    MaurerCircuit.g_pubs g acc = MaurerCircuit.g_pubs g fset0 `|` acc.
    case g => |>. progress. rewrite fset0U => |>*. rewrite fset0U => |>. progress. rewrite /ISet.union fset0U fsetUC => |>*. rewrite fset0U => |>*. qed.

  lemma valid_circuit_check_c_wire' x n ps :
    MaurerCircuit.valid_circuit' n x ps => MaurerCircuit.check_c_wire x n.
    elim/last_ind x => |>. progress. 
    rewrite check_c_wire_rcons => |>*. rewrite H => |>*. 
    move :H0. rewrite valid_circuit_rcons' => |>*.
    move :H0. rewrite valid_circuit_rcons' => |>H0 H1. move :H1. case x => |>*. qed.

  lemma valid_circuit_check_c_wire x n ps :
    MaurerCircuit.valid_circuit x n ps => MaurerCircuit.check_c_wire x n.
    rewrite /MaurerCircuit.valid_circuit => |>*. rewrite (valid_circuit_check_c_wire' x n ps) => |>*. qed.

  lemma gate_end_wire i g (st:wire_st * pub_st) ins :
  (MaurerGate.gate_end i g st ins).`1.`1 = st.`1.`1 + 1.
  case g => |>g. rewrite /local_gate_end /add => |>*. rewrite (prod_id st.`1) => |>*. rewrite /local_gate_end /smul => |>*. rewrite (prod_id st.`1) => |>*. rewrite /local_gate_end /mul_end => |>*. rewrite (prod_id st.`1) => |>*. rewrite /local_gate_end /mul_end => |>. rewrite (prod_id st.`1) => |>. qed.

lemma gate_end_ge0 i g  (st:wire_st * pub_st) ins :
  0 <= st.`1.`1 =>
  0 <= (MaurerGate.gate_end i g st ins).`1.`1. 
  case g => |>g.
  rewrite /local_gate_end /add (prod_id st.`1) => |>*. smt().
  rewrite /local_gate_end /smul (prod_id st.`1) => |>*. smt().
  rewrite /local_gate_end (prod_id st.`1) /cnst => |>*. smt().
  rewrite /local_gate_end /mul_end (prod_id st.`1) => |>*.  smt(). qed.

lemma dom_gate_end i g (st:wire_st * pub_st) ins :
  fdom (MaurerGate.gate_end i g st ins).`1.`2 = fdom st.`1.`2 `|` fset1 st.`1.`1.
  case g => |>g.
  rewrite /local_gate_end /add (prod_id st.`1) => |>*. rewrite fdom_set => |>*. 
  rewrite /local_gate_end /smul (prod_id st.`1) => |>*. rewrite  fdom_set => |>*.
  rewrite /local_gate_end (prod_id st.`1) /cnst => |>*. rewrite fdom_set => |>*.
  rewrite /local_gate_end /mul_end (prod_id st.`1) => |>*. rewrite fdom_set => |>*. qed.

lemma dom_gate_end_pub i g (st:wire_st * pub_st) ins :
  (MaurerGate.gate_end i g st ins).`2 \subset st.`2 `|` fset1 st.`1.`1.
  case g => |>.
  progress. rewrite /local_gate_end /add subsetP /(<=) => |>a H. rewrite in_fsetU => |>*. smt().
  progress. rewrite /local_gate_end /smul subsetP /(<=) => |>a H. rewrite in_fsetU => |>*. smt().
  progress. rewrite /local_gate_end subsetP /(<=) => |>.
  progress. rewrite /local_gate_end subsetP /(<=) => |>a H. rewrite !in_fsetU !in_fset1 => |>*. smt(). qed.

lemma valid_circuit_c_pubs0' x n ps :
    0 <= n => MaurerCircuit.valid_circuit' n x ps => (MaurerCircuit.c_pubs x fset0 \subset iset' n (size x)).
    elim/last_ind x. rewrite /c_pubs => |>*. rewrite iset_fset0' => |>*.
    progress. rewrite c_pubs_rcons size_rcons. move :H1. rewrite valid_circuit_rcons' => |>. progress. have : MaurerCircuit.c_pubs s fset0 \subset iset' n (size s). rewrite H => |>*. clear H. rewrite subset_in. move :H1 H2. rewrite subsetP /(<=) => |>. case x => |>.
    progress. have : a \in iset' n (size s). rewrite H6 => |>*. apply/in_iset_succ' => |>*. smt(size_ge0).
    progress. have : a \in iset' n (size s). rewrite H7 => |>*. apply/in_iset_succ' => |>*. smt(size_ge0).
    progress. rewrite iset_succ' => |>*. rewrite size_ge0 => |>*. rewrite -H1. move :H3. rewrite /ISet.union !in_fsetU => |>*. smt().
    progress. have : a \in iset' n (size s). rewrite H6 => |>*. apply/in_iset_succ' => |>*. smt(size_ge0).
    qed.

lemma valid_circuit_c_pubs0 x n ps :
  MaurerCircuit.valid_circuit x n ps => (MaurerCircuit.c_pubs x fset0 \subset iset' n (size x)).
  rewrite /MaurerCircuit.valid_circuit => |>*. rewrite (valid_circuit_c_pubs0' x n ps) => |>*. qed.
    
(*lemma dom_raw_shares i ss :
  i \in MaurerGate.GT.partyset =>
  fdom (raw_shares i ss) = oflist (Maurer5SS.shr_idx i).
  rewrite /raw_shares foldl_iseqE !iseq_6 /shr_idx => |>H.
  case (i=0) => |>. rewrite !fdom_set !fdom_empty fset0U => |>. rewrite fsetP => |>x.
  rewrite !in_fsetU !in_fset1 !mem_oflist => |>. rewrite !nth_list_to_array6 => |>. smt().
  case (i=1) => |>. rewrite !fdom_set !fdom_empty fset0U => |>. rewrite fsetP => |>x.
  rewrite !in_fsetU !in_fset1 !mem_oflist => |>*. rewrite !nth_list_to_array6 => |>. smt().
  case (i=2) => |>. rewrite !fdom_set !fdom_empty fset0U => |>. rewrite fsetP => |>x.
  rewrite !in_fsetU !in_fset1 !mem_oflist => |>*. rewrite !nth_list_to_array6 => |>. smt().
  case (i=3) => |>. rewrite !fdom_set !fdom_empty fset0U => |>. rewrite fsetP => |>x.
  rewrite !in_fsetU !in_fset1 !mem_oflist => |>*. rewrite !nth_list_to_array6 => |>. smt().
  case (i=4) => |>. rewrite !fdom_set !fdom_empty fset0U => |>. rewrite fsetP => |>x.
  rewrite !in_fsetU !in_fset1 !mem_oflist => |>*. rewrite !nth_list_to_array6 => |>. smt().
  progress. have : false. move :H. rewrite iset_in_def => |>*. smt(). progress. qed.*)

(*op shr_idx_inv (p:pid) (idx:int) =
  oget (assoc (zip (Maurer5SS.shr_idx p) (iseq 6)) idx).*)

(*lemma raw_shares_inv i x a :
  i \in MaurerGate.GT.partyset =>
  a \in Maurer5SS.shr_idx i =>
  oget (raw_shares i x).[a] = x.[shr_idx_inv i a].
  rewrite !/raw_shares /shr_idx_inv /shr_idx iset_in_def foldl_iseqE !iseq_6 /parties. progress. rewrite !nth_list_to_array6 !/IMap.set !/IMap.empty => |>. move :H1. 
  case (i=0) => |>Hi0. rewrite /get_rshr !assoc_cons => |>. elim Hi0 => |>.  rewrite !get_setE => |>*. move => Hi0. elim Hi0 => |>. rewrite !get_setE => |>*. move => Hi0. elim Hi0 => |>. rewrite !get_setE => |>*. move => Hi0. elim Hi0 => |>. rewrite !get_setE => |>*. move => Hi0. elim Hi0 => |>. rewrite !get_setE => |>*. rewrite !get_setE => |>*.
  case (i=1) => |>Hi1. rewrite /get_rshr !assoc_cons => |>. elim Hi1 => |>.  rewrite !get_setE => |>*. move => Hi1. elim Hi1 => |>. rewrite !get_setE => |>*. move => Hi1. elim Hi1 => |>. rewrite !get_setE => |>*. move => Hi1. elim Hi1 => |>. rewrite !get_setE => |>*. move => Hi1. elim Hi1 => |>. rewrite !get_setE => |>*. rewrite !get_setE => |>*.
  case (i=2) => |>Hi2. rewrite /get_rshr !assoc_cons => |>. elim Hi2 => |>.  rewrite !get_setE => |>*. move => Hi2. elim Hi2 => |>. rewrite !get_setE => |>*. move => Hi2. elim Hi2 => |>. rewrite !get_setE => |>*. move => Hi2. elim Hi2 => |>. rewrite !get_setE => |>*. move => Hi2. elim Hi2 => |>. rewrite !get_setE => |>*. rewrite !get_setE => |>*.
  case (i=3) => |>Hi3. rewrite /get_rshr !assoc_cons => |>. elim Hi3 => |>.  rewrite !get_setE => |>*. move => Hi3. elim Hi3 => |>. rewrite !get_setE => |>*. move => Hi3. elim Hi3 => |>. rewrite !get_setE => |>*. move => Hi3. elim Hi3 => |>. rewrite !get_setE => |>*. move => Hi3. elim Hi3 => |>. rewrite !get_setE => |>*. rewrite !get_setE => |>*.
  case (i=4) => |>Hi4. rewrite /get_rshr !assoc_cons => |>. elim Hi4 => |>.  rewrite !get_setE => |>*. move => Hi4. elim Hi4 => |>. rewrite !get_setE => |>*. move => Hi4. elim Hi4 => |>. rewrite !get_setE => |>*. move => Hi4. elim Hi4 => |>. rewrite !get_setE => |>*. move => Hi4. elim Hi4 => |>. rewrite !get_setE => |>*. rewrite !get_setE => |>*.
  have : false. smt(). progress. qed.*)

(*lemma dom_shr_idx_inv i a :
  i \in MaurerGate.GT.partyset =>
  a \in (Maurer5SS.shr_idx i) =>
  0 <= shr_idx_inv i a < 6.
  rewrite /shr_idx_inv /shr_idx !iseq_6 => H.
  case (i=0) => |>Hi0. rewrite !assoc_cons => |>. elim Hi0 => |>. move => Hi0. elim Hi0 => |>. move => Hi0. elim Hi0 => |>. move => Hi0. elim Hi0 => |>. move => Hi0. elim Hi0 => |>.
  case (i=1) => |>Hi1. rewrite !assoc_cons => |>. elim Hi1 => |>. move => Hi1. elim Hi1 => |>. move => Hi1. elim Hi1 => |>. move => Hi1. elim Hi1 => |>. move => Hi1. elim Hi1 => |>.
  case (i=2) => |>Hi2. rewrite !assoc_cons => |>. elim Hi2 => |>. move => Hi2. elim Hi2 => |>. move => Hi2. elim Hi2 => |>. move => Hi2. elim Hi2 => |>. move => Hi2. elim Hi2 => |>.
  case (i=3) => |>Hi3. rewrite !assoc_cons => |>. elim Hi3 => |>. move => Hi3. elim Hi3 => |>. move => Hi3. elim Hi3 => |>. move => Hi3. elim Hi3 => |>. move => Hi3. elim Hi3 => |>.
  case (i=4) => |>Hi4. rewrite !assoc_cons => |>. elim Hi4 => |>. move => Hi4. elim Hi4 => |>. move => Hi4. elim Hi4 => |>. move => Hi4. elim Hi4 => |>. move => Hi4. elim Hi4 => |>.
  have : false. move :H. rewrite /partyset iset_in_def /parties => |>. smt(). progress. qed.*)

lemma raw_shares_map2 i (s1 s2:shr) a fop :
  i \in MaurerGate.GT.partyset => 
  a \in Maurer5SS.shr_idx i =>
  oget (Maurer5SS.raw_shares i (Array6.map2 fop s1 s2)).[a] = fop s1.[shr_idx_inv i a] s2.[shr_idx_inv i a].
  progress. rewrite raw_shares_inv => |>*. move :H. rewrite iset_in_def => />.
  rewrite Array6.map2iE. rewrite dom_shr_idx_inv => |>*. move :H. rewrite iset_in_def => />.
  progress. qed.

lemma get_add_p_shr i (si:shr) rs j :
  0 <= i < 5 =>
  (add_p_shr i si rs).[j] = if j \in Maurer5SS.shr_idx i then Some si.[shr_idx_inv i j] else rs.[j].
  rewrite /shr_idx /add_p_shr /shr_idx_inv iseq_6 => |>*. rewrite assoc_zip => |>*. rewrite size_shr_idx => |>*. rewrite /shr_idx => |>*.
  case (i=0) => |>. rewrite !index_cons !index_nil => |>*. case (j=5) => |>*. case (j=9) => |>*. case (j=8) => |>*. case (j=7) => |>*. case (j=4) => |>*. case (j=6) => |>*. rewrite !Array10.set_neqiE => |>*. 
  case (i=1) => |>*. rewrite !index_cons !index_nil => |>*. case (j=1) => |>*. case (j=2) => |>*. case (j=9) => |>*. case (j=3) => |>*. case (j=8) => |>*. case (j=7) => |>*. rewrite !Array10.set_neqiE => |>*. 
  case (i=2) => |>*. rewrite !index_cons !index_nil => |>*. case (j=6) => |>*. case (j=0) => |>*. case (j=2) => |>*. case (j=5) => |>*. case (j=9) => |>*. case (j=3) => |>*. rewrite !Array10.set_neqiE => |>*. 
  case (i=3) => |>*. rewrite !index_cons !index_nil => |>*. case (j=3) => |>*. case (j=8) => |>*. case (j=4) => |>*. case (j=6) => |>*. case (j=0) => |>*. case (j=1) => |>*. rewrite !Array10.set_neqiE => |>*. 
  case (i=4) => |>*. rewrite !index_cons !index_nil => |>*. case (j=7) => |>*. case (j=4) => |>*. case (j=0) => |>*. case (j=1) => |>*. case (j=2) => |>*. case (j=5) => |>*. rewrite !Array10.set_neqiE => |>*. 
  have : false. smt(). progress. qed.

lemma consistent_raw_shares_add_shr i j sx1 sx2 sy1 sy2 :
  i \in MaurerGate.GT.partyset => j \in MaurerGate.GT.partyset =>
  Maurer5SS.consistent_raw_shares i j sx1 sy1 =>
  Maurer5SS.consistent_raw_shares i j sx2 sy2 =>
    Maurer5SS.consistent_raw_shares i j (Maurer5Spec.add_shr sx1 sx2) (Maurer5Spec.add_shr sy1 sy2).
  rewrite !/consistent_raw_shares /add_shr /IMap.all !fallP => |>. progress. move :H1 H2 H3. rewrite !fdom_fzip => |>H1 H2 H3. rewrite !fzip_some => |>. 
  have : 0 <= i < 5. move :H. rewrite iset_in_def => />. move => irng.
  have : 0 <= j < 5. move :H0. rewrite iset_in_def => />. move => jrng.
  have : (oget (fzip (Maurer5SS.raw_shares i sx1) (Maurer5SS.raw_shares j sy1)).[a]).`1 = (oget (fzip (Maurer5SS.raw_shares i sx1) (Maurer5SS.raw_shares j sy1)).[a]).`2. rewrite H1 => |>. move :H3. rewrite !dom_raw_shares => |>. progress.
  have : (oget (fzip (Maurer5SS.raw_shares i sx2) (Maurer5SS.raw_shares j sy2)).[a]).`1 = (oget (fzip (Maurer5SS.raw_shares i sx2) (Maurer5SS.raw_shares j sy2)).[a]).`2. rewrite H2 => |>. move :H3. rewrite !dom_raw_shares => |>. progress.
  clear H1 H2. move :H3. rewrite !dom_raw_shares => |>. rewrite in_fsetI !mem_oflist => |>H1 H2. rewrite !raw_shares_map2 => |>. move :H4 H5. rewrite !get_fzip => |>. rewrite !ozip_some => |>. rewrite -fdomP dom_raw_shares => |>. rewrite mem_oflist => |>. rewrite -fdomP dom_raw_shares => |>. rewrite mem_oflist => |>. rewrite -fdomP dom_raw_shares => |>. rewrite mem_oflist => |>. rewrite -fdomP dom_raw_shares => |>. rewrite mem_oflist => |>. rewrite !raw_shares_inv => |>. progress. rewrite H3 H4 => |>. qed.

lemma consistent_raw_shares_smul i j sx1 sx2 sy1 sy2 :
  i \in MaurerGate.GT.partyset => j \in MaurerGate.GT.partyset =>
  sx1 = sx2 =>
  Maurer5SS.consistent_raw_shares i j sy1 sy2 =>
  Maurer5SS.consistent_raw_shares i j (Array6.map (fmul sx1) sy1) (Array6.map (fmul sx2) sy2).
  rewrite !/consistent_raw_shares !/IMap.all !fallP => |>. progress.
  have : 0 <= i < 5. move :H. rewrite iset_in_def => />. move => irng.
  have : 0 <= j < 5. move :H0. rewrite iset_in_def => />. move => jrng.
  move :H2. rewrite fdom_fzip !dom_raw_shares => |>H2. move :H2. rewrite in_fsetI !mem_oflist => |>H2 H3. rewrite !fzip_some => |>. rewrite !dom_raw_shares => |>. rewrite in_fsetI !mem_oflist => |>. rewrite !raw_shares_inv => |>. rewrite !Array6.mapiE. rewrite dom_shr_idx_inv => |>. rewrite dom_shr_idx_inv => |>. congr.
  have : (oget (fzip (Maurer5SS.raw_shares i sy1) (Maurer5SS.raw_shares j sy2)).[a]).`1 = (oget (fzip (Maurer5SS.raw_shares i sy1) (Maurer5SS.raw_shares j sy2)).[a]).`2. rewrite H1 => |>. rewrite fdom_fzip !dom_raw_shares => |>. rewrite in_fsetI !mem_oflist => |>. rewrite !fzip_some => |>. rewrite in_fsetI !dom_raw_shares => |>. rewrite !mem_oflist => |>. move :H. rewrite /partyset /iset mem_oflist => |>. move :H0. rewrite /partyset /iset mem_oflist => |>. rewrite !raw_shares_inv => |>. qed.

lemma pshare_unpshare i x :
  i \in MaurerGate.GT.partyset =>
  (Maurer5SS.pshare x).[i].[0] = x.
  rewrite iset_in_def /pshare => |>*. rewrite Array5.initE !andabP andaP => |>*. 
  rewrite /init_sh => |>*. rewrite (nth_map witness) => |>*. rewrite size_shr_idx => |>*. rewrite Array10.get_of_list. rewrite rng_shr_idx => |>*. rewrite shr_idx_nth_0 => |>*. 
  case (i=0) => |>*. case (i=1) => |>*. case (i=2) => |>*. case (i=3) => |>*. case (i=4) => |>*. have : false. smt(). progress. qed.

lemma consistent_pub_shares_pshare i j x :
  i \in MaurerGate.GT.partyset => j \in MaurerGate.GT.partyset =>
  consistent_pub_shares i j (party_pshare i x) (party_pshare j x).
  rewrite /consistent_pub_shares !/party_pshare => |>*. rewrite !/check_pshare !/party_unpshare !/party_pshare => |>*. rewrite /get_rshr !pshare_unpshare => |>*. qed.

lemma shr_idx_id (pid:int) (i:int) :
  (0 <= pid < 5) => (0 <= i < 6) =>
  shr_idx_inv pid (nth witness (Maurer5SS.shr_idx pid) i) = i.
  rewrite /shr_idx_inv => |>*. rewrite assoc_zip => |>*. rewrite size_iseq size_shr_idx => |>*.
  rewrite iseq_6 /shr_idx => |>*. 
  case (pid=0) => |>*. case (i=0) => |>*. case (i=1) => |>*. case (i=2) => |>*. case (i=3) => |>*. case (i=4) => |>*. case (i=5) => |>*. have : false. smt(). progress.
  case (pid=1) => |>*. case (i=0) => |>*. case (i=1) => |>*. case (i=2) => |>*. case (i=3) => |>*. case (i=4) => |>*. case (i=5) => |>*. have : false. smt(). progress.
  case (pid=2) => |>*. case (i=0) => |>*. case (i=1) => |>*. case (i=2) => |>*. case (i=3) => |>*. case (i=4) => |>*. case (i=5) => |>*. have : false. smt(). progress.
  case (pid=3) => |>*. case (i=0) => |>*. case (i=1) => |>*. case (i=2) => |>*. case (i=3) => |>*. case (i=4) => |>*. case (i=5) => |>*. have : false. smt(). progress.
  case (pid=4) => |>*. case (i=0) => |>*. case (i=1) => |>*. case (i=2) => |>*. case (i=3) => |>*. case (i=4) => |>*. case (i=5) => |>*. have : false. smt(). progress.
  have : false. smt(). progress. qed.

(*lemma nth_shr_idx_shr_idx_inv i a :
  i \in MaurerGate.GT.partyset =>
  a \in Maurer5SS.shr_idx i => 
  (nth witness (Maurer5SS.shr_idx i) (shr_idx_inv i a)) = a.
  rewrite iset_in_def /shr_idx_inv !iseq_6 => |>. progress. move :H1. rewrite /shr_idx => |>H1.
  case (i=0) => |>*. move :H1. progress. case (a=5) => |>*. case (a=9) => |>*. case (a=8) => |>*. case (a=7) => |>*. case (a=4) => |>*. case (a=6) => |>*. have : false. smt(). progress.
  case (i=1) => |>*. move :H1. progress. case (a=1) => |>*. case (a=2) => |>*. case (a=9) => |>*. case (a=3) => |>*. case (a=8) => |>*. case (a=7) => |>*. have : false. smt(). progress.
  case (i=2) => |>*. move :H1. progress. case (a=6) => |>*. case (a=0) => |>*. case (a=2) => |>*. case (a=5) => |>*. case (a=9) => |>*. case (a=3) => |>*. have : false. smt(). progress.
  case (i=3) => |>*. move :H1. progress. case (a=3) => |>*. case (a=8) => |>*. case (a=4) => |>*. case (a=6) => |>*. case (a=0) => |>*. case (a=1) => |>*. have : false. smt(). progress.
  case (i=4) => |>*. move :H1. progress. case (a=7) => |>*. case (a=4) => |>*. case (a=0) => |>*. case (a=1) => |>*. case (a=2) => |>*. case (a=5) => |>*. have : false. smt(). progress.
  have : false. smt(). progress. qed.*)

lemma consistent_raw_shares_pshare i j x :
  i \in MaurerGate.GT.partyset => j \in MaurerGate.GT.partyset =>
  Maurer5SS.consistent_raw_shares i j (party_pshare i x) (party_pshare j x).
  rewrite /consistent_raw_shares !/party_pshare /IMap.all fallP => |>. progress.
  have : 0 <= i < 5. move :H. rewrite iset_in_def => />. move => irng.
  have : 0 <= j < 5. move :H0. rewrite iset_in_def => />. move => jrng.
  move :H1. rewrite fdom_fzip in_fsetI !dom_raw_shares => |>. rewrite !mem_oflist => |>H1 H2. move :H. rewrite /partyset /iset mem_oflist => |>H. move :H0. rewrite /partyset /iset mem_oflist => |>H0. rewrite !fzip_some => |>*. rewrite !dom_raw_shares => |>*. rewrite in_fsetI !mem_oflist => |>*. rewrite !raw_shares_inv => |>*.
  rewrite /pshare => |>*. rewrite !Array5.initE !irng !jrng /init_sh => |>*. 
  rewrite !Array6.initE => |>*. rewrite !dom_shr_idx_inv => |>*. rewrite !(nth_map witness). rewrite size_shr_idx. progress. rewrite dom_shr_idx_inv => |>*. rewrite size_shr_idx. progress. rewrite dom_shr_idx_inv => |>*. rewrite !Array10.get_of_list. rewrite rng_shr_idx. rewrite dom_shr_idx_inv => |>*. rewrite rng_shr_idx. rewrite dom_shr_idx_inv => |>*. 
  rewrite !nth_shr_idx_shr_idx_inv => |>*. qed.

lemma consistent_raw_shares_mul_end i j (ms1 ms2:msgs) (ws1 ws2:wire_st) wid :
  i \in MaurerGate.GT.partyset => j \in MaurerGate.GT.partyset =>
  wid = ws1.`1 => wid = ws2.`1 =>
  (forall k, 0 <= k < 5 => Maurer5SS.consistent_raw_shares i j ms1.[k] ms2.[k]) =>
    Maurer5SS.consistent_raw_shares i j (oget (Maurer5Spec.mul_end ms1 ws1).`2.[wid]) (oget (Maurer5Spec.mul_end ms2 ws2).`2.[wid]).
  rewrite /mul_end => |>. rewrite (prod_id ws1) => |>. rewrite (prod_id ws2) => |>. progress. rewrite -H1 !get_set_eqE => |>*. 
  rewrite consistent_raw_shares_add_shr => |>*. rewrite consistent_raw_shares_add_shr => |>*. rewrite consistent_raw_shares_add_shr => |>*. rewrite consistent_raw_shares_add_shr => |>*.
  rewrite H2 => |>*. rewrite H2 => |>*. rewrite H2 => |>*. rewrite H2 => |>*. rewrite H2 => |>*.
  qed.

lemma consistent_raw_shares_mul_end_prefix i j (ms1 ms2:msgs) (ws1 ws2:wire_st) wid :
  i \in MaurerGate.GT.partyset => j \in MaurerGate.GT.partyset =>
  ws1.`1 = ws2.`1 =>
  wid \in iset ws1.`1 => 
    Maurer5SS.consistent_raw_shares i j (oget ws1.`2.[wid]) (oget ws2.`2.[wid]) =>
    Maurer5SS.consistent_raw_shares i j (oget (Maurer5Spec.mul_end ms1 ws1).`2.[wid]) (oget (Maurer5Spec.mul_end ms2 ws2).`2.[wid]).
  rewrite /mul_end => |>. rewrite (prod_id ws1) => |>. rewrite (prod_id ws2) => |>. progress. rewrite -H1 !get_set_neqE => |>*. move :H2. rewrite iset_in_def => |>*. smt(). move :H2. rewrite iset_in_def => |>*. smt(). qed.

lemma consistent_raw_shares_share i j v r :
  i \in MaurerGate.GT.partyset => j \in MaurerGate.GT.partyset =>
  Maurer5SS.consistent_raw_shares i j (Maurer5SS.share v r).[i] (Maurer5SS.share v r).[j].
  rewrite /consistent_raw_shares /IMap.all fallP => |>. progress.
  have : 0 <= i < 5. move :H. rewrite iset_in_def => />. move => irng.
  have : 0 <= j < 5. move :H0. rewrite iset_in_def => />. move => jrng.
  move :H1. rewrite fdom_fzip in_fsetI !dom_raw_shares => |>. rewrite !mem_oflist => |>H1 H2. move :H. rewrite /partyset /iset mem_oflist => |>H. move :H0. rewrite /partyset /iset mem_oflist => |>H0. rewrite !fzip_some => |>*. rewrite !dom_raw_shares => |>*. rewrite in_fsetI !mem_oflist => |>*. rewrite !raw_shares_inv /share => |>*.
  rewrite !Array5.initE !irng !jrng /init_sh => |>*. rewrite !Array6.initE. rewrite !dom_shr_idx_inv => |>*. rewrite !(nth_map witness). rewrite size_shr_idx. rewrite irng => |>*. rewrite dom_shr_idx_inv => |>*. rewrite size_shr_idx. rewrite jrng => |>*. rewrite dom_shr_idx_inv => |>*. 
  rewrite !nth_shr_idx_shr_idx_inv => |>*. qed.

lemma get_raw_shares pid i (s:shr) :
  0 <= pid < 5 =>
  (Maurer5SS.raw_shares pid s).[i] = if i \in Maurer5SS.shr_idx pid then Some s.[shr_idx_inv pid i] else None.
  rewrite /raw_shares /raw_shares' /shr_idx_inv foldl_iseqE iseq_6 => |>*. rewrite assoc_zip => |>*. rewrite size_shr_idx => |>*. rewrite /shr_idx => |>*. rewrite !/get_rshr /IMap.set /IMap.empty => |>.
  case (pid=0) => |>*. rewrite !index_cons !index_nil => |>*. 
  case (i=5) => |>*. smt(@SmtMap).
  case (i=9) => |>*. smt(@SmtMap).
  case (i=8) => |>*. smt(@SmtMap).
  case (i=7) => |>*. smt(@SmtMap).
  case (i=4) => |>*. smt(@SmtMap).
  case (i=6) => |>*. smt(@SmtMap).
  smt(@SmtMap).
  case (pid=1) => |>*. rewrite !index_cons !index_nil => |>*. 
  case (i=1) => |>*. smt(@SmtMap).
  case (i=2) => |>*. smt(@SmtMap).
  case (i=9) => |>*. smt(@SmtMap).
  case (i=3) => |>*. smt(@SmtMap).
  case (i=8) => |>*. smt(@SmtMap).
  case (i=7) => |>*. smt(@SmtMap).
  smt(@SmtMap).
  case (pid=2) => |>*. rewrite !index_cons !index_nil => |>*. 
  case (i=6) => |>*. smt(@SmtMap).
  case (i=0) => |>*. smt(@SmtMap).
  case (i=2) => |>*. smt(@SmtMap).
  case (i=5) => |>*. smt(@SmtMap).
  case (i=9) => |>*. smt(@SmtMap).
  case (i=3) => |>*. smt(@SmtMap).
  smt(@SmtMap).
  case (pid=3) => |>*. rewrite !index_cons !index_nil => |>*. 
  case (i=3) => |>*. smt(@SmtMap).
  case (i=8) => |>*. smt(@SmtMap).
  case (i=4) => |>*. smt(@SmtMap).
  case (i=6) => |>*. smt(@SmtMap).
  case (i=0) => |>*. smt(@SmtMap).
  case (i=1) => |>*. smt(@SmtMap).
  smt(@SmtMap).
  case (pid=4) => |>*. rewrite !index_cons !index_nil => |>*. 
  case (i=7) => |>*. smt(@SmtMap).
  case (i=4) => |>*. smt(@SmtMap).
  case (i=0) => |>*. smt(@SmtMap).
  case (i=1) => |>*. smt(@SmtMap).
  case (i=2) => |>*. smt(@SmtMap).
  case (i=5) => |>*. smt(@SmtMap).
  smt(@SmtMap).
  have : false. smt(). progress. qed.

  lemma add_p_shr_swap i j (ss:shrs) :
    0 <= i < 5 => 0 <= j < 5 => i <> j =>
    (forall i j, 0 <= i < 5 => 0 <= j < 5 => Maurer5SS.consistent_raw_shares i j ss.[i] ss.[j]) =>
      add_p_shr i ss.[i] (add_p_shr j ss.[j] (Array10.create None)) = add_p_shr j ss.[j] (add_p_shr i ss.[i] (Array10.create None)).
    pose cr := [i;j]. rewrite (_: (add_p_shr i ss.[i] (add_p_shr j ss.[j] (Array10.create None)) = add_p_shr j ss.[j] (add_p_shr i ss.[i] (Array10.create None))) = (fun cr => add_p_shr (nth witness cr 0) ss.[(nth witness cr 0)] (add_p_shr (nth witness cr 1) ss.[(nth witness cr 1)] (Array10.create None)) = add_p_shr (nth witness cr 1) ss.[(nth witness cr 1)] (add_p_shr (nth witness cr 0) ss.[(nth witness cr 0)] (Array10.create None))) cr ). progress. move => H1 H2 H3 H4.  apply cr_ind' => />. progress. 
    rewrite in_iseq => />*. move :H. rewrite /cr => />*. smt().
    rewrite add_p_shr_0_1_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_0_2_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_0_3_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_0_4_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_1_2_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_1_3_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_1_4_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_2_3_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_2_4_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_3_4_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_0_1_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_0_2_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_0_3_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_0_4_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_1_2_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_1_3_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_1_4_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_2_3_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_2_4_swap => />*. rewrite H4 => |>*.
    rewrite add_p_shr_3_4_swap => />*. rewrite H4 => |>*.
    qed.

lemma cr_missing_01 :
  cr_missing [0;1] = 0.
  rewrite /cr_missing /cr_missings => |>*. rewrite /shr_idxs fsetU0 /shr_idx iseq_10 => |>*. rewrite !oflist_cons !oflist_nil !fsetU0 => |>*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U !fset0I !fsetU0 => |>*. rewrite pick1 => |>*. qed.

lemma cr_missing_02 :
  cr_missing [0;2] = 1.
  rewrite /cr_missing /cr_missings => |>*. rewrite /shr_idxs fsetU0 /shr_idx iseq_10 => |>*. rewrite !oflist_cons !oflist_nil !fsetU0 => |>*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U !fset0I !fsetU0 => |>*. rewrite pick1 => |>*. qed.

lemma cr_missing_03 :
  cr_missing [0;3] = 2.
  rewrite /cr_missing /cr_missings => |>*. rewrite /shr_idxs fsetU0 /shr_idx iseq_10 => |>*. rewrite !oflist_cons !oflist_nil !fsetU0 => |>*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U !fset0I !fsetU0 => |>*. rewrite pick1 => |>*. qed.

lemma cr_missing_04 :
  cr_missing [0;4] = 3.
  rewrite /cr_missing /cr_missings => |>*. rewrite /shr_idxs fsetU0 /shr_idx iseq_10 => |>*. rewrite !oflist_cons !oflist_nil !fsetU0 => |>*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U !fset0I !fsetU0 => |>*. rewrite pick1 => |>*. qed.

lemma cr_missing_12 :
  cr_missing [1;2] = 4.
  rewrite /cr_missing /cr_missings => |>*. rewrite /shr_idxs fsetU0 /shr_idx iseq_10 => |>*. rewrite !oflist_cons !oflist_nil !fsetU0 => |>*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U !fset0I !fsetU0 => |>*. rewrite pick1 => |>*. qed.

lemma cr_missing_13 :
  cr_missing [1;3] = 5.
  rewrite /cr_missing /cr_missings => |>*. rewrite /shr_idxs fsetU0 /shr_idx iseq_10 => |>*. rewrite !oflist_cons !oflist_nil !fsetU0 => |>*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U !fset0I !fsetU0 !fset0U => |>*. rewrite pick1 => |>*. qed.

lemma cr_missing_14 :
  cr_missing [1;4] = 6.
  rewrite /cr_missing /cr_missings => |>*. rewrite /shr_idxs fsetU0 /shr_idx iseq_10 => |>*. rewrite !oflist_cons !oflist_nil !fsetU0 => |>*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U !fset0I !fsetU0 !fset0U => |>*. rewrite pick1 => |>*. qed.

lemma cr_missing_23 :
  cr_missing [2;3] = 7.
  rewrite /cr_missing /cr_missings => |>*. rewrite /shr_idxs fsetU0 /shr_idx iseq_10 => |>*. rewrite !oflist_cons !oflist_nil !fsetU0 => |>*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U !fset0I !fsetU0 !fset0U => |>*. rewrite pick1 => |>*. qed.

lemma cr_missing_24 :
  cr_missing [2;4] = 8.
  rewrite /cr_missing /cr_missings => |>*. rewrite /shr_idxs fsetU0 /shr_idx iseq_10 => |>*. rewrite !oflist_cons !oflist_nil !fsetU0 => |>*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U !fset0I !fsetU0 !fset0U => |>*. rewrite pick1 => |>*. qed.

lemma cr_missing_34 :
  cr_missing [3;4] = 9.
  rewrite /cr_missing /cr_missings => |>*. rewrite /shr_idxs fsetU0 /shr_idx iseq_10 => |>*. rewrite !oflist_cons !oflist_nil !fsetU0 => |>*. rewrite !fsetDUl !fsetDUr !fset1D !in_fset1 !fset0I !fsetI0 !fsetIid !fset0U !fset0I !fset0U => |>*. rewrite pick1 => |>*. qed.

lemma cr_missing_swap i j:
  0 <= i < 5 =>
  0 <= j < 5 =>
  cr_missing [i;j] = cr_missing [j;i].
  rewrite /cr_missing /cr_missings => |>*. rewrite !fsetU0 fsetUC => |>*. qed.

op unrshr (ss:shrs) : Maurer5SS.rshr =
  Array10.of_list witness [ss.[2].[1];ss.[1].[0];ss.[1].[1];ss.[1].[3];ss.[0].[4];ss.[0].[0];ss.[0].[5];ss.[0].[3];ss.[0].[2];ss.[0].[1]].

lemma reconstruct_missing (ss:shrs) (cr0 cr1:int) :
  0 <= cr0 < 5 =>
  0 <= cr1 < 5 =>
  cr0 <> cr1 =>
  (forall i j, 0 <= i < 5 => 0 <= j < 5 => Maurer5SS.consistent_raw_shares i j ss.[i] ss.[j]) =>
  (fsub (Maurer5SS.unshare ss) (foldr (fun (x:val option) (y:val) => (fadd (odflt fzero x) y)) fzero (to_list ((add_p_shr cr0 ss.[cr0] ((add_p_shr cr1 ss.[cr1] ((Array10.create None))))))))) = (unrshr ss).[cr_missing [cr0;cr1]].
  move => H H0 H1 H2. rewrite (_: (fsub ((Maurer5SS.unshare ss))
  (foldr (fun (x : val option) (y : val) => fadd (odflt fzero x) y) fzero
     (to_list (add_p_shr cr0 ss.[cr0] (add_p_shr cr1 ss.[cr1] ((Array10.create None)))))) =
(unrshr ss).[cr_missing [cr0;cr1]] ) = (fun cr => fsub ((Maurer5SS.unshare ss))
  (foldr (fun (x : val option) (y : val) => fadd (odflt fzero x) y) fzero
     (to_list (add_p_shr (nth witness cr 0) ss.[nth witness cr 0] (add_p_shr (nth witness cr 1) ss.[nth witness cr 1] ((Array10.create None)))))) =
 (unrshr ss).[cr_missing [nth witness cr 0;nth witness cr 1]] ) [cr0;cr1] ). progress. apply cr_ind => />. progress. rewrite in_iseq => |>*. case H3 => |>*. smt(). smt(). 
  rewrite cr_missing_01 => |>*. rewrite array10_to_list !get_add_p_shr /shr_idx_inv => |>*. rewrite !iseq_6 !assoc_zip  => |>*. rewrite /shr_idx => |>*. rewrite !index_cons !index_nil => |>*. rewrite /unshare /unrshr => |>*. algebra.
  rewrite cr_missing_02 => |>*. rewrite array10_to_list !get_add_p_shr /shr_idx_inv => |>*. rewrite !iseq_6 !assoc_zip  => |>*. rewrite /shr_idx => |>*. rewrite !index_cons !index_nil => |>*. rewrite /unshare /unrshr => |>*. rewrite -(consistent_s11_s22 ss.[1] ss.[2]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s13_s25 ss.[1] ss.[2]) => |>*. rewrite H2 => |>*. algebra.
  rewrite cr_missing_03 => |>*. rewrite array10_to_list !get_add_p_shr /shr_idx_inv => |>*. rewrite !iseq_6 !assoc_zip  => |>*. rewrite /shr_idx => |>*. rewrite !index_cons !index_nil => |>*. rewrite /unshare /unrshr => |>*. rewrite -(consistent_s21_s34 ss.[2] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s10_s35 ss.[1] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s13_s30 ss.[1] ss.[3]) => |>*. rewrite H2 => |>*. algebra.
  rewrite cr_missing_04 => |>*. rewrite array10_to_list !get_add_p_shr /shr_idx_inv => |>*. rewrite !iseq_6 !assoc_zip  => |>*. rewrite /shr_idx => |>*. rewrite !index_cons !index_nil => |>*. rewrite /unshare /unrshr => |>*. rewrite -(consistent_s21_s42 ss.[2] ss.[4]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s10_s43 ss.[1] ss.[4]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s11_s44 ss.[1] ss.[4]) => |>*. rewrite H2 => |>*. algebra.
  rewrite cr_missing_12 => |>*. rewrite array10_to_list !get_add_p_shr /shr_idx_inv => |>*. rewrite !iseq_6 !assoc_zip  => |>*. rewrite /shr_idx => |>*. rewrite !index_cons !index_nil => |>*. rewrite /unshare /unrshr => |>*. rewrite -(consistent_s00_s23 ss.[0] ss.[2]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s05_s20 ss.[0] ss.[2]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s01_s12 ss.[0] ss.[1]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s02_s14 ss.[0] ss.[1]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s03_s15 ss.[0] ss.[1]) => |>*. rewrite H2 => |>*. algebra.
  rewrite cr_missing_13 => |>*. rewrite array10_to_list !get_add_p_shr /shr_idx_inv => |>*. rewrite !iseq_6 !assoc_zip  => |>*. rewrite /shr_idx => |>*. rewrite !index_cons !index_nil => |>*. rewrite /unshare /unrshr => |>*. rewrite -(consistent_s21_s34 ss.[2] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s04_s32 ss.[0] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s01_s12 ss.[0] ss.[1]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s02_s14 ss.[0] ss.[1]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s03_s15 ss.[0] ss.[1]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s05_s33 ss.[0] ss.[3]) => |>*. rewrite H2 => |>*. algebra.
  rewrite cr_missing_14 => |>*. rewrite array10_to_list !get_add_p_shr /shr_idx_inv => |>*. rewrite !iseq_6 !assoc_zip  => |>*. rewrite /shr_idx => |>*. rewrite !index_cons !index_nil => |>*. rewrite /unshare /unrshr => |>*. rewrite -(consistent_s21_s42 ss.[2] ss.[4]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s04_s41 ss.[0] ss.[4]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s01_s12 ss.[0] ss.[1]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s02_s14 ss.[0] ss.[1]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s03_s15 ss.[0] ss.[1]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s00_s45 ss.[0] ss.[4]) => |>*. rewrite H2 => |>*. algebra.
  rewrite cr_missing_23 => |>*. rewrite array10_to_list !get_add_p_shr /shr_idx_inv => |>*. rewrite !iseq_6 !assoc_zip  => |>*. rewrite /shr_idx => |>*. rewrite !index_cons !index_nil => |>*. rewrite /unshare /unrshr => |>*. rewrite -(consistent_s10_s35 ss.[1] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s11_s22 ss.[1] ss.[2]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s13_s25 ss.[1] ss.[2]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s04_s32 ss.[0] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s00_s23 ss.[0] ss.[2]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s05_s20 ss.[0] ss.[2]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s02_s31 ss.[0] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s01_s24 ss.[0] ss.[2]) => |>*. rewrite H2 => |>*. algebra.
  rewrite cr_missing_24 => |>*. rewrite array10_to_list !get_add_p_shr /shr_idx_inv => |>*. rewrite !iseq_6 !assoc_zip  => |>*. rewrite /shr_idx => |>*. rewrite !index_cons !index_nil => |>*. rewrite /unshare /unrshr => |>*. rewrite -(consistent_s10_s43 ss.[1] ss.[4]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s11_s22 ss.[1] ss.[2]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s13_s25 ss.[1] ss.[2]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s04_s41 ss.[0] ss.[4]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s00_s23 ss.[0] ss.[2]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s05_s20 ss.[0] ss.[2]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s03_s40 ss.[0] ss.[4]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s01_s24 ss.[0] ss.[2]) => |>*. rewrite H2 => |>*. algebra.
  rewrite cr_missing_34 => |>*. rewrite array10_to_list !get_add_p_shr /shr_idx_inv => |>*. rewrite !iseq_6 !assoc_zip  => |>*. rewrite /shr_idx => |>*. rewrite !index_cons !index_nil => |>*. rewrite /unshare /unrshr => |>*. rewrite -(consistent_s21_s34 ss.[2] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s10_s35 ss.[1] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s11_s44 ss.[1] ss.[4]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s13_s30 ss.[1] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s04_s32 ss.[0] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s00_s45 ss.[0] ss.[4]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s05_s33 ss.[0] ss.[3]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s03_s40 ss.[0] ss.[4]) => |>*. rewrite H2 => |>*. rewrite -(consistent_s02_s31 ss.[0] ss.[3]) => |>*. rewrite H2 => |>*. algebra.
  move => x y H3 H4 H5.
  have : 0 <= x < 5. smt(). progress. have : 0 <= y < 5. smt(). progress.
  have : size (Maurer5SS.shr_idx x) = 6. rewrite size_shr_idx => |>*. progress. have : size (Maurer5SS.shr_idx y) = 6. rewrite size_shr_idx => |>*. progress.
  rewrite cr_missing_swap => |>*. rewrite add_p_shr_swap => |>*. qed.


lemma not_in_shr_idx_0 i :
  0 <= i < 10 =>
  (!(i \in Maurer5SS.shr_idx 0)) = (i = 0 \/ i = 1 \/ i = 2 \/ i = 3).
  rewrite /shr_idx => |>*. smt(). qed.

lemma not_in_shr_idx_1 i :
  0 <= i < 10 =>
  (!(i \in Maurer5SS.shr_idx 1)) = (i = 0 \/ i = 4 \/ i = 5 \/ i = 6).
  rewrite /shr_idx => |>*. smt(). qed.

lemma not_in_shr_idx_2 i :
  0 <= i < 10 =>
  (!(i \in Maurer5SS.shr_idx 2)) = (i = 1 \/ i = 4 \/ i = 7 \/ i = 8).
  rewrite /shr_idx => |>*. smt(). qed.

lemma not_in_shr_idx_3 i :
  0 <= i < 10 =>
  (!(i \in Maurer5SS.shr_idx 3)) = (i = 2 \/ i = 5 \/ i = 7 \/ i = 9).
  rewrite /shr_idx => |>*. smt(). qed.

lemma not_in_shr_idx_4 i :
  0 <= i < 10 =>
  (!(i \in Maurer5SS.shr_idx 4)) = (i = 3 \/ i = 6 \/ i = 8 \/ i = 9).
  rewrite /shr_idx => |>*. smt(). qed.

lemma nth_shr_idx_0 pid i :
  0 <= i < 6 => 0 <= pid < 5 =>
  (nth witness (Maurer5SS.shr_idx pid) i = 0) = ((pid=2 /\ i=1) \/ (pid=3 /\ i=4) \/ (pid=4 /\ i=2)).
  rewrite /shr_idx => |>*. case (pid=0) => |>*. smt(). case (pid=1) => |>*. smt(). case (pid=2) => |>*. smt(). case (pid=3) => |>*. smt(). case (pid=4) => |>*. smt(). smt(). qed.

lemma nth_shr_idx_1 pid i :
  0 <= i < 6 => 0 <= pid < 5 =>
  (nth witness (Maurer5SS.shr_idx pid) i = 1) = ((pid=1 /\ i=0) \/ (pid=3 /\ i=5) \/ (pid=4 /\ i=3)).
  rewrite /shr_idx => |>*. case (pid=0) => |>*. smt(). case (pid=1) => |>*. smt(). case (pid=2) => |>*. smt(). case (pid=3) => |>*. smt(). case (pid=4) => |>*. smt(). smt(). qed.

lemma nth_shr_idx_2 pid i :
  0 <= i < 6 => 0 <= pid < 5 =>
  (nth witness (Maurer5SS.shr_idx pid) i = 2) = ((pid=1 /\ i=1) \/ (pid=2 /\ i=2) \/ (pid=4 /\ i=4)).
  rewrite /shr_idx => |>*. case (pid=0) => |>*. smt(). case (pid=1) => |>*. smt(). case (pid=2) => |>*. smt(). case (pid=3) => |>*. smt(). case (pid=4) => |>*. smt(). smt(). qed.

lemma nth_shr_idx_3 pid i :
  0 <= i < 6 => 0 <= pid < 5 =>
  (nth witness (Maurer5SS.shr_idx pid) i = 3) = ((pid=1 /\ i=3) \/ (pid=2 /\ i=5) \/ (pid=3 /\ i=0)).
  rewrite /shr_idx => |>*. case (pid=0) => |>*. smt(). case (pid=1) => |>*. smt(). case (pid=2) => |>*. smt(). case (pid=3) => |>*. smt(). case (pid=4) => |>*. smt(). smt(). qed.

lemma nth_shr_idx_4 pid i :
  0 <= i < 6 => 0 <= pid < 5 =>
  (nth witness (Maurer5SS.shr_idx pid) i = 4) = ((pid=0 /\ i=4) \/ (pid=3 /\ i=2) \/ (pid=4 /\ i=1)).
  rewrite /shr_idx => |>*. case (pid=0) => |>*. smt(). case (pid=1) => |>*. smt(). case (pid=2) => |>*. smt(). case (pid=3) => |>*. smt(). case (pid=4) => |>*. smt(). smt(). qed.

lemma nth_shr_idx_5 pid i :
  0 <= i < 6 => 0 <= pid < 5 =>
  (nth witness (Maurer5SS.shr_idx pid) i = 5) = ((pid=0 /\ i=0) \/ (pid=2 /\ i=3) \/ (pid=4 /\ i=5)).
  rewrite /shr_idx => |>*. case (pid=0) => |>*. smt(). case (pid=1) => |>*. smt(). case (pid=2) => |>*. smt(). case (pid=3) => |>*. smt(). case (pid=4) => |>*. smt(). smt(). qed.

lemma nth_shr_idx_6 pid i :
  0 <= i < 6 => 0 <= pid < 5 =>
  (nth witness (Maurer5SS.shr_idx pid) i = 6) = ((pid=0 /\ i=5) \/ (pid=2 /\ i=0) \/ (pid=3 /\ i=3)).
  rewrite /shr_idx => |>*. case (pid=0) => |>*. smt(). case (pid=1) => |>*. smt(). case (pid=2) => |>*. smt(). case (pid=3) => |>*. smt(). case (pid=4) => |>*. smt(). smt(). qed.

lemma nth_shr_idx_7 pid i :
  0 <= i < 6 => 0 <= pid < 5 =>
  (nth witness (Maurer5SS.shr_idx pid) i = 7) = ((pid=0 /\ i=3) \/ (pid=1 /\ i=5) \/ (pid=4 /\ i=0)).
  rewrite /shr_idx => |>*. case (pid=0) => |>*. smt(). case (pid=1) => |>*. smt(). case (pid=2) => |>*. smt(). case (pid=3) => |>*. smt(). case (pid=4) => |>*. smt(). smt(). qed.

lemma nth_shr_idx_8 pid i :
  0 <= i < 6 => 0 <= pid < 5 =>
  (nth witness (Maurer5SS.shr_idx pid) i = 8) = ((pid=0 /\ i=2) \/ (pid=1 /\ i=4) \/ (pid=3 /\ i=1)).
  rewrite /shr_idx => |>*. case (pid=0) => |>*. smt(). case (pid=1) => |>*. smt(). case (pid=2) => |>*. smt(). case (pid=3) => |>*. smt(). case (pid=4) => |>*. smt(). smt(). qed.

lemma nth_shr_idx_9 pid i :
  0 <= i < 6 => 0 <= pid < 5 =>
  (nth witness (Maurer5SS.shr_idx pid) i = 9) = ((pid=0 /\ i=1) \/ (pid=1 /\ i=2) \/ (pid=2 /\ i=4)).
  rewrite /shr_idx => |>*. case (pid=0) => |>*. smt(). case (pid=1) => |>*. smt(). case (pid=2) => |>*. smt(). case (pid=3) => |>*. smt(). case (pid=4) => |>*. smt(). smt(). qed.
