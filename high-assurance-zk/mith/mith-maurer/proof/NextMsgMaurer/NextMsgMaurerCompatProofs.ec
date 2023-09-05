(* general *)
require import AllCore FSet SmtMap List.

(* hugo *)
require import Aux AuxList AuxFSet AuxSmtMap.
require import NextMsgMaurerCompat NextMsgMaurer NextMsgMaurerMPC NextMsgMaurerP NextMsgArray NextMsgMaurerAPI.
require import NextMsgMPC NextMsgISet NextMsgIMap.
require import NextMsgMaurerAuxProofs NextMsgMaurerProofs.
import NextMsgMaurerAuxProofs.

(* mbb *)
require import Array5 Array9.

require import AProtocol AProtocolFunctionality.
require import ASecretSharingScheme.
require import Maurer5SSCompat.

theory MaurerCompatProofs.
    
  lemma assoc_to_rands_t rs i :
    i \in MaurerProtocolFunctionality.pid_set =>
    oget (assoc (MaurerProtocol.to_rands_t rs) i) = MaurerP.get rs i.
    rewrite /pid_set in_iseq /to_rands_t => />*. rewrite MaurerP.assoc_to_assoc /size andabP andaP => />*. qed.

  lemma assoc_to_traces_t tr i :
    i \in MaurerProtocolFunctionality.pid_set =>
    oget (assoc (MaurerProtocol.to_traces_t tr) i) =
      let pouts = map (fun i => (i,tt)) MaurerProtocolFunctionality.pid_set in
      (pouts,MaurerP.get tr i).
    rewrite /pid_set in_iseq /to_traces_t => />*. rewrite assoc_map_r /pid_set in_iseq andaP => />*. qed.

  lemma rand_to_rands_t i xs : 
    i \in MaurerProtocolFunctionality.pid_set =>
    MaurerProtocol.rand i (MaurerProtocol.to_rands_t xs) = (MaurerP.get xs i).
    rewrite /rand /to_rands_t => />H. move :H. rewrite in_iseq => />*. rewrite MaurerP.assoc_to_assoc /size andabP andaP => />*. qed.

  lemma trace_to_traces_t i xs : 
    i \in MaurerProtocolFunctionality.pid_set =>
    MaurerProtocol.trace i (MaurerProtocol.to_traces_t xs) =
      let pouts = map (fun i => (i,tt)) MaurerProtocolFunctionality.pid_set in
      (pouts,MaurerP.get xs i).
    rewrite /trace /to_traces_t => />H. rewrite assoc_map_r => />*. move :H. rewrite /pid_set => />*. qed.

  lemma from_to_rands_t xs :
    MaurerProtocol.from_rands_t (MaurerProtocol.to_rands_t xs) = xs.
    rewrite /from_rands_t /to_rands_t => />*. rewrite MaurerP.tP => />*. rewrite MaurerP.get_init andabP andaP => />*. rewrite MaurerP.assoc_to_assoc andabP andaP => />*. qed.

  lemma to_from_rands_t c xs :
    MaurerProtocol.valid_rands c xs =>
    MaurerProtocol.to_rands_t (MaurerProtocol.from_rands_t xs) = xs.
    rewrite /to_rands_t /from_rands_t => />H H0. have : size xs = 5. have : size (unzip1 xs) = 5. 
rewrite H size_iseq => />*. rewrite size_map => />*. move => szxs. 
    apply (eq_from_nth witness) => />. rewrite MaurerP.size_to_assoc => />. rewrite szxs => />. move => i. rewrite MaurerP.size_to_assoc => />Hi1 Hi2. rewrite MaurerP.nth_to_assoc_some => />*. rewrite MaurerP.get_init andabP andaP => />. rewrite (assoc_iseq_some witness) => />. rewrite H => />. rewrite /pid_set => />. rewrite szxs => />. move :Hi2. rewrite szxs /size => />. 
    rewrite nth_onth (onth_nth (witness,witness)) => />. rewrite szxs /size => />. rewrite -(zip_unzip xs) => />*. rewrite nth_zip => />*. rewrite !size_map => />*. rewrite H => />*. rewrite nth_iseq => />*. move :Hi1 Hi2. rewrite /size => />*. qed.

  lemma to_from_input_t i xi :
    i \in MaurerProtocolFunctionality.pid_set =>
    MaurerProtocolFunctionality.to_input_t (MaurerProtocolFunctionality.from_input_t i xi) = xi.
    rewrite /pid_set /to_input_t /from_input_t /to_pinput_t /to_sinput_t => />. rewrite in_iseq =>/>Hi1 Hi2. rewrite eq2 => />*. rewrite /ISet.card !card_iset => />*. rewrite size_map => />*. rewrite size_ge0 => />*. rewrite !size_map => />*. split.
    apply (eq_from_nth witness) => />. rewrite size_map => />*. rewrite size_iseq => />*. rewrite ge0_max => />*. rewrite size_ge0 => />*. move => j. rewrite size_map size_iseq ge0_max => />. rewrite size_ge0 => />. move => Hj1 Hj2.
    rewrite !(nth_map witness) => />. rewrite size_iseq ge0_max => />. rewrite size_ge0 => />. rewrite /get_wire_st_shr /mkwire_st => />. rewrite ofset_some => />*. rewrite nth_iseq => />*. rewrite size_cat size_map => />*. rewrite Hj1 Hj2 /ISet.iset iset_in_def => />. smt(size_ge0). 
    rewrite nth_cat => />*. rewrite !nth_iseq => />*. rewrite !size_map => />*. rewrite !Hj1 !Hj2 => />. rewrite (nth_map witness) => />*. rewrite party_unpshare_pshare => />*. rewrite iset_in_def => />*.
    apply (eq_from_nth witness) => />. rewrite size_map size_iseq => />*. rewrite size_cat size_map => />*. rewrite ge0_max /get_wire_st_next /mkwire_st => />*. smt(size_ge0). algebra. move => j. rewrite size_map size_iseq ge0_max /get_wire_st_next /mkwire_st => />. rewrite size_cat size_map => />. smt(size_ge0). rewrite size_cat size_map => /> Hj1 Hj2. rewrite (nth_map witness) => />. rewrite size_iseq ge0_max => />. smt(). rewrite /get_wire_st_shr /mkwire_st => />. rewrite ofset_some => />*. rewrite nth_iseq Hj1 Hj2 /ISet.iset => />*. rewrite iset_in_def => />*. smt(size_ge0). move :Hj2. rewrite (_:size xi.`1 + size xi.`2 - size xi.`1 = size xi.`2). algebra. move => Hj2. 
    rewrite nth_cat => />*. rewrite !nth_iseq => />*. rewrite !andaP => />*. rewrite !size_map => />. have : !(size xi.`1 + j < size xi.`1). smt(size_ge0). move => H. rewrite H => />. rewrite (_:size xi.`1 + j - size xi.`1 = j). algebra. trivial. qed.

  lemma from_to_input_t i xp (xi:MaurerMPCReveal.P.ST.local_input) :
    i \in MaurerProtocolFunctionality.pid_set =>
    xi.`2 = iset (size xp) => xi.`1.`1 = card (fdom xi.`1.`2) =>
    (forall k, 0 <= k < size xp => MaurerAPI.party_pshare i (nth witness xp k) = oget xi.`1.`2.[k]) =>
    MaurerAPI.g_valid_share xi =>
    (MaurerProtocolFunctionality.from_input_t i (xp, (MaurerProtocolFunctionality.to_sinput_t xi))) = xi.
    rewrite /from_input_t /to_input_t /to_sinput_t => />. rewrite /get_wire_st_fdom /get_wire_st_next /mkwire_st => />. rewrite !size_cat !size_map !size_iseq /get_wire_st_shr /ISet.iset /ISet.subset /IMap.ofset /ISet.card => />. move => H H0 H1 H2 H3 H4 H5.
    rewrite !eq2 => />. rewrite H0 => />. rewrite H1 => />. rewrite card_iset => />. rewrite size_ge0 => />.
    have : 0 <= xi.`1.`1. rewrite H1 fcard_ge0 => />*. move => xige0.
    have : size xp = card xi.`2. have : card xi.`2 = card (iset (size xp)). rewrite H0 => />*. rewrite card_iset => />. rewrite size_ge0 => />. move => H6. rewrite H6 => />*. move => sxp.
    rewrite !sxp => />. rewrite ge0_max => />. have : card xi.`2 <= card (fdom xi.`1.`2). rewrite subset_leq_fcard => />*. rewrite H4 card_iset => />H6. smt().
    split. algebra. rewrite -fmap_eqIn => />. rewrite !fdom_ofset => />. rewrite -!H1 -!sxp => />. rewrite (_:size xp + (xi.`1.`1 - size xp) = xi.`1.`1). algebra. rewrite H1 H4 => />. rewrite card_iset => />j. rewrite iset_in_def =>Hj. 
    rewrite ofset_some => />. rewrite iset_in_def => />. rewrite nth_cat => />. rewrite size_map => />. case (j < size xp) => />Hj1. rewrite (nth_map witness) => />. move :Hj. progress. rewrite H2 => />. move :Hj. progress. rewrite some_oget => />*. rewrite -fdomP H4 iset_in_def => />*. 
    rewrite !(nth_map witness) => />*. rewrite size_iseq => />*. rewrite !sxp ge0_max => />*. smt(). progress. smt(). smt(). 
    rewrite nth_iseq => />*. have : 0 <= j - size xp /\ j - size xp < xi.`1.`1 - size xp. smt(). move => domi0. rewrite domi0 => />*. rewrite some_oget => />*. rewrite -fdomP. have : size xp + (j - size xp) = j. algebra. rewrite H4 iset_in_def => />H6. rewrite !H6 => />*. have : size xp + (j - size xp) = j. algebra. progress. rewrite H6 => />*. qed.

  lemma from_to_inputs_t xp (xs:MaurerMPCReveal.P.ST.local_input MaurerP.arrayN) :
    (forall i, 0 <= i < 5 => (MaurerP.get xs i).`2 = iset (size xp)) =>
    (forall i, 0 <= i < 5 => ((MaurerP.get xs i)).`1.`1 = card (fdom ((MaurerP.get xs i)).`1.`2) ) =>
    (forall i k, 0 <= i < 5 => 0 <= k < size xp => MaurerAPI.party_pshare i (nth witness xp k) = oget (MaurerP.get xs i).`1.`2.[k]) =>
    (forall i, 0 <= i < 5 => (MaurerAPI.g_valid_share ((MaurerP.get xs i)))) =>
    MaurerProtocolFunctionality.from_inputs_t (MaurerProtocolFunctionality.to_inputs_t xp xs) = xs.
    rewrite /from_inputs_t /to_inputs_t /to_sinputs_t /mk_inputs => |>H H0 H1 H2. rewrite MaurerP.tP /size => |>j Hj1 Hj2. rewrite MaurerP.get_init andabP andaP => |>. rewrite assoc_map_r => |>. rewrite in_iseq Hj1 Hj2 => |>. rewrite assoc_map_r => |>. rewrite in_iseq andaP => |>. rewrite from_to_input_t => |>. rewrite in_iseq => |>. rewrite H => |>. rewrite H0 => |>. move => k Hk1 Hk2. rewrite H1 => |>. rewrite /get_wire_st_next /get_wire_st_fdom /ISet.subset /ISet.iset => |>. rewrite H2 => />. qed.

  lemma to_outputs_t_pinit' o :
    MaurerProtocol.to_outputs_t' (MaurerMPCReveal.P.ST.pinit (fun _ => o)) = MaurerProtocolFunctionality.to_outputs_t o.
    rewrite /to_outputs_t' /to_outputs_t => />. apply/ map_eq => />i.  rewrite size_iseq ge0_max => /> Hi1 Hi2. rewrite /pinit MaurerP.get_init => />*. rewrite /pid_set !nth_iseq andaP => />*. rewrite andabP /size andaP => />. qed.

  lemma assoc_to_outputs_t' os i :
    i \in MaurerProtocolFunctionality.pid_set =>
    oget (assoc (MaurerProtocol.to_outputs_t' os) i) = MaurerP.get os i.
    rewrite /to_outputs_t' => />H. rewrite assoc_map_r H => />*. qed.

  lemma get_view_from_views_t i vs :
    i \in MaurerProtocolFunctionality.pid_set =>
    MaurerMPCReveal.P.ST.get_view i (MaurerProtocol.from_views_t vs) = MaurerProtocol.from_view_t i (oget (assoc vs i)).
    rewrite /get_view /from_views_t /from_view_t => />H. rewrite /get MaurerP.get_init => />*. move :H. rewrite /pid_set in_iseq => />H H0. rewrite /size H0 => />*. qed.

  lemma to_pairwise_consistent_trace c vs :
    MaurerProtocolFunctionality.valid_circuit c =>
    (forall (i j : MaurerProtocolFunctionality.pid_t),
      i \in MaurerProtocolFunctionality.pid_set =>
      j \in MaurerProtocolFunctionality.pid_set => MaurerProtocol.consistent_views c (oget (assoc vs i)) (oget (assoc vs j)) i j) =>
    MaurerMPCReveal.P.pairwise_consistent_trace c.`1 (MaurerProtocol.from_views_t vs).
    rewrite /consistent_views /pairwise_consistent_trace. move => H H0 i j Hij. rewrite (_:MaurerWeakReveal.ST.get_view=MaurerMPCReveal.P.ST.get_view). progress. rewrite !get_view_from_views_t. move :Hij. rewrite /pid_set /partyset in_iseq /ISet.mem !iset_in_def => />*. move :Hij. rewrite /pid_set /partyset in_iseq /ISet.mem !iset_in_def => />*. move :H0. simplify. move => H0.
    have : (MaurerProtocol.valid_view_t i (oget (assoc vs i))) /\
      (MaurerProtocol.valid_view_t j (oget (assoc vs i))) /\
      (MaurerProtocol.consistent_views' c i j ((MaurerProtocol.from_view_t i (oget (assoc vs i)))) ((MaurerProtocol.from_view_t j (oget (assoc vs j))))). rewrite H0 => />*. move :Hij. rewrite /pid_set /partyset in_iseq /ISet.mem !iset_in_def => />*. move :Hij. rewrite /pid_set /partyset in_iseq /ISet.mem !iset_in_def => />*. rewrite /consistent_views' /pairwise_consistent_views => |>. move :H. rewrite /valid_circuit => |>. move => I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12. rewrite /consistent_views => |>. 
    move :I11. rewrite /consistent_inputs /mpc_consistent_inputs /consistent_inputs /get_wire_st_next => |>. move => J1 J2 J3 J4 J5 J6 J7. rewrite J1 J3 => />. qed.

  lemma valid_rands_from c rs :
    MaurerProtocol.valid_rands c rs => MaurerMPCReveal.P.valid_rands c.`1 (MaurerProtocol.from_rands_t rs).
    rewrite /valid_rands => />H H0 i j Hi Hj.
    have : (MaurerProtocol.valid_rand c (oget (assoc rs i))). rewrite H0 => />*. move :Hi. rewrite in_iseq /ISet.mem iset_in_def => />*. 
    have : (MaurerProtocol.valid_rand c (oget (assoc rs j))). rewrite H0 => />*. move :Hj. rewrite in_iseq /ISet.mem iset_in_def => />*. 
    clear H0. rewrite /valid_rand /pub_input_conv => />H1 H2 H3 H4. rewrite H3 /from_rands_t /get => />*. rewrite !MaurerP.get_init => />*. have : 0 <= i < MaurerP.size. move :Hi. rewrite /ISet.mem iset_in_def => />*. move => irng. rewrite irng => />*. have : 0 <= j < MaurerP.size. move :Hj. rewrite /ISet.mem iset_in_def /parties => />. move => jrng. rewrite jrng => />*. rewrite -H1 H3 => />*. qed.

  lemma valid_rands_to (c:MaurerProtocolFunctionality.circuit_t) rs :
    MaurerMPCReveal.P.valid_rands c.`1 rs => MaurerProtocol.valid_rands c (MaurerProtocol.to_rands_t rs).
    rewrite /valid_rands=> />. progress.
    rewrite /to_rands_t. apply (eq_from_nth witness) => />. rewrite /to_assoc unzip1_zip size_iseq => />*. rewrite MaurerP.size_to_list => />*. rewrite ge0_max => />*. rewrite size_iseq => />. move => i Hi1 Hi2. 
    rewrite /pid_set !(nth_map witness) => />. move :Hi2. rewrite !size_map => />. move :Hi2. rewrite /to_assoc unzip1_zip => />. rewrite size_iseq MaurerP.size_to_list => />*. rewrite nth_iseq => />Hi2. rewrite nth_onth. rewrite (onth_nth (witness,witness)) => />. rewrite size_zip size_iseq MaurerP.size_to_list => />. move :Hi2. rewrite size_iseq => />. rewrite nth_zip => />*. rewrite size_iseq MaurerP.size_to_list => />*. rewrite nth_iseq => />*. 
    rewrite assoc_to_rands_t => />*. have : (MaurerWeakReveal.consistent_rands c.`1 pid pid ((MaurerP.get rs pid)) ((MaurerP.get rs pid))). rewrite H => />*. move :H0. rewrite /ISet.mem !iset_in_def in_iseq => />*. rewrite /consistent_rands => />*. 
    have : (MaurerWeakReveal.consistent_rands c.`1 pid pid ((MaurerP.get rs pid)) ((MaurerP.get rs pid))). rewrite H => />*. move :H0. rewrite /ISet.mem !iset_in_def in_iseq => />*. rewrite /consistent_rands => />*. rewrite assoc_to_rands_t /pub_input_conv => />*. qed.

  lemma valid_inputs_from c xs :
    MaurerProtocolFunctionality.valid_circuit c =>
    (MaurerProtocolFunctionality.valid_inputs c xs) =>
    (MaurerMPCReveal.P.valid_inputs c.`1 (MaurerProtocolFunctionality.from_inputs_t xs)).
    rewrite /valid_inputs /valid_inputs' !allP => |>H H0 H1 i j Hi Hj. 
    have : all
        (fun (j : int) =>
           MaurerProtocolFunctionality.consistent_inputs c i j
             (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t xs) i)
             (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t xs) j)) (
        iseq 5). rewrite H1 => />. move :Hi. rewrite in_iseq /ISet.mem iset_in_def => />. rewrite allP => |>H2. clear H1. 
    have : MaurerProtocolFunctionality.consistent_inputs c i j
        (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t xs) i)
        (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t xs) j). rewrite H2 => |>. move :Hj. rewrite /ISet.mem iset_in_def in_iseq => />. rewrite /consistent_inputs /mpc_consistent_inputs /consistent_inputs /get /get_wire_st_next => |>. clear H2.
    have : 0 <= i < 5. move :Hi. rewrite /ISet.mem iset_in_def => />. move => domi.
    have : 0 <= j < 5. move :Hj. rewrite /ISet.mem iset_in_def => />. move => domj.
    rewrite /from_inputs_t !MaurerP.get_init /size !domi !domj => |>. move => H1 H2 H3 H4 H5 H6 H7.
    move :H. rewrite /valid_circuit /ISet.iset /ISet.subset => |>. move => K1 K2 K3 K4. rewrite H1 H3 => |>. qed.

  lemma valid_inputs_to (c:MaurerProtocolFunctionality.circuit_t) xp (xs:MaurerMPCReveal.P.ST.local_input MaurerP.arrayN) :
    (forall i, 0 <= i < 5 => (MaurerP.get xs i).`2 = iset (size xp)) =>
    (forall i k, 0 <= i < 5 => 0 <= k < size xp => MaurerAPI.party_pshare i (nth witness xp k) = oget (MaurerP.get xs i).`1.`2.[k]) =>
    MaurerProtocolFunctionality.valid_circuit c =>
    MaurerProtocolFunctionality.valid_inputs' c xs =>
    MaurerProtocolFunctionality.valid_inputs c (MaurerProtocolFunctionality.to_inputs_t xp xs).
    rewrite /valid_inputs => |>. move => H H0 H1 H2. rewrite from_to_inputs_t => |>. move => i Hi1 Hi2.
    move :H2. rewrite /valid_inputs' allP => />H2. 
    have : all (fun (j : int) => MaurerProtocolFunctionality.consistent_inputs c i j (MaurerP.get xs i) (MaurerP.get xs j)) (iseq 5). rewrite H2 => />. rewrite in_iseq => />. rewrite allP => />H3. clear H2. 
    have : (MaurerProtocolFunctionality.consistent_inputs c i i ((MaurerP.get xs i)) ((MaurerP.get xs i))). rewrite H3 => />*. rewrite in_iseq => />. rewrite /consistent_inputs /g_valid_share /get_wire_st_next /get_wire_st_fdom => |>. move => I1 I2 I3 I4 I5 I6. rewrite I1 I4 card_iset. rewrite I3 //. rewrite I1 //. 
    move => i Hi1 Hi2. move :H2. rewrite /valid_inputs' allP => |>H2. 
    have : all (fun (j : int) => MaurerProtocolFunctionality.consistent_inputs c i j (MaurerP.get xs i) (MaurerP.get xs j)) (iseq 5). rewrite H2 => |>. rewrite in_iseq => />. rewrite allP => |>H3. have : MaurerProtocolFunctionality.consistent_inputs c i i (MaurerP.get xs i) (MaurerP.get xs i). rewrite H3 => />. rewrite in_iseq => />. rewrite /consistent_inputs => |>. 
    rewrite /to_inputs_t /mk_inputs => />*. rewrite -map_comp /(\o) => />*. rewrite map_id => />*. qed.

  lemma consistent_trace_public_consistent_inputs c xp vs i j :
    0 <= i < 5 => 0 <= j < 5 =>
    (MaurerProtocol.consistent_trace_public c xp vs) =>
    (MaurerProtocolFunctionality.consistent_inputs c i j
      ((MaurerP.get ((MaurerMPCReveal.WR.W.P.ST.get_trace_inputs (MaurerProtocol.from_views_t vs))) i))
     ((MaurerP.get ((MaurerMPCReveal.WR.W.P.ST.get_trace_inputs (MaurerProtocol.from_views_t vs))) j))).
    move => Hi Hj.
    rewrite /consistent_trace_public /consistent_views_public => |>H. rewrite /get_trace_inputs /from_views_t => |>. rewrite !MaurerP.get_map => |>. move :Hi. progress. move :Hj. progress. rewrite !MaurerP.get_init /size Hi Hj => |>. 
    have : (fst3 (oget (assoc vs i))).`1 = xp /\ (fst3 (oget (assoc vs j))).`1 = xp /\
      MaurerProtocol.consistent_views c (oget (assoc vs i)) (oget (assoc vs j)) i j. rewrite H => |>. rewrite in_iseq => />. move :Hi. progress. rewrite in_iseq => />. move :Hj. progress. 
    clear H. rewrite /consistent_views => />. qed.

  lemma local_output_view pid c xs rs :
    pid \in MaurerProtocolFunctionality.pid_set =>
    ((MaurerProtocolFunctionality.from_input_t pid ((MaurerProtocolFunctionality.input pid xs))), (((MaurerP.get ((MaurerMPCReveal.P.protocol c ((MaurerProtocolFunctionality.from_inputs_t xs)) ((MaurerProtocol.from_rands_t rs)))).`1 pid)).`2.`1, (MaurerProtocol.rand pid rs))) =
    (MaurerP.get ((MaurerMPCReveal.P.protocol c ((MaurerProtocolFunctionality.from_inputs_t xs)) ((MaurerProtocol.from_rands_t rs)))).`1 pid).
    rewrite !eq2 => />H. rewrite /from_inputs_t /from_input_t /input /rand /from_rands_t => />*. rewrite !size_cat => />*. rewrite !size_map /protocol => />*. rewrite /mkwire_st MaurerP.get_zip3 /size => />*. rewrite !MaurerP.get_init /size => />*.
    have : 0 <= pid < 5. move :H. rewrite in_iseq /size => />*. move => dom. rewrite !dom => />. rewrite !size_cat => />*. rewrite !size_map => />*. qed.

  lemma consistent_views_conv c xp vs i j :
    (MaurerProtocolFunctionality.valid_circuit c) => 
    (MaurerProtocol.consistent_views_public c xp (oget (assoc vs i)) (oget (assoc vs j)) i j) =>
    (MaurerMPCReveal.P.consistent_views c.`1 i j
      ((MaurerProtocol.from_view_t i (oget (assoc vs i))))
      ((MaurerProtocol.from_view_t j (oget (assoc vs j))))).
    rewrite /consistent_views_public /consistent_views /consistent_views'. rewrite /consistent_inputs /get_wire_st_next /get_wire_st_fdom => |>.  move => H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16. rewrite /mpc_consistent_inputs /consistent_inputs /get_wire_st_next => |>. 
    move :H1. rewrite /valid_circuit => |>I1 I2 I3 I4. rewrite !H9 !H11. rewrite I1 I2 => />*. qed.

  lemma pairwise_consistent_views_conv (c:MaurerProtocolFunctionality.circuit_t) i j vi vj :
    0 <= i < 5 => 0 <= j < 5 =>
    (MaurerProtocolFunctionality.valid_circuit c) => 
    MaurerProtocol.consistent_views' c i j vi vj = (vi.`1.`1.`1 = c.`2.`1 /\ vi.`1.`2 = c.`2.`2 /\ vj.`1.`1.`1 = c.`2.`1 /\ vj.`1.`2 = c.`2.`2 /\ MaurerMPCReveal.P.pairwise_consistent_views c.`1 i j vi vj).
    move => Hi Hj.
    rewrite /consistent_views' /pairwise_consistent_views => |>H. rewrite /consistent_views /consistent_inputs /consistent_rands' /consistent_rands /get_wire_st_next /pub_input_conv => |>. rewrite !MaurerWeakReveal.ST.eq_rmsgsP => |>. rewrite eq_logical => |>*. split.
    move => H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. rewrite /mpc_consistent_inputs /consistent_inputs => |>. move :H. rewrite /valid_circuit /get_wire_st_next /ISet.subset /ISet.iset => |>. move => I1 I2 I3 I4. rewrite !H5 !H7 => />. move :H3 H4. rewrite !MaurerReveal.ST.eq_rmsgsP => |>H3 H4. rewrite (_:MaurerWeakReveal.get_view_in_msgs=MaurerReveal.get_view_in_msgs). progress. rewrite (_:MaurerWeakReveal.get_view_out_msgs=MaurerReveal.get_view_out_msgs). progress. 
    move => H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. move :H9. rewrite /mpc_consistent_inputs /consistent_inputs => |>. rewrite !MaurerReveal.ST.eq_rmsgsP => |>. qed.

  lemma forward_consistency (c : MaurerProtocolFunctionality.circuit_t) xp (vs : MaurerProtocol.views_t) :
    MaurerProtocolFunctionality.valid_circuit c =>
    MaurerProtocol.consistent_trace_public c xp vs =>
    (exists rs sx, let xs = MaurerProtocolFunctionality.mk_inputs xp sx in 
                   MaurerProtocol.valid_rands c rs /\ MaurerProtocolFunctionality.valid_inputs c xs /\
                   let (tr,y) = MaurerProtocol.protocol c rs xs in
                   (forall pid, pid \in MaurerProtocolFunctionality.pid_set => oget (assoc vs pid) =
                     (MaurerProtocolFunctionality.input pid xs,(MaurerProtocol.rand pid rs,MaurerProtocol.trace pid tr)))).
    progress. pose tr := MaurerProtocol.from_views_t vs.
    exists (MaurerProtocol.to_rands_t (MaurerMPCReveal.WR.W.P.ST.get_trace_rands tr)) (MaurerProtocolFunctionality.to_sinputs_t (MaurerMPCReveal.WR.W.P.ST.get_trace_inputs tr)). rewrite valid_rands_to. rewrite MaurerMPCReveal.P.consistent_trace_rands => />i j Hij. rewrite /tr (_:MaurerWeakReveal.ST.get_view=MaurerMPCReveal.P.ST.get_view). progress. rewrite !get_view_from_views_t. move :Hij. rewrite /ISet.mem !iset_in_def /pid_set in_iseq => />*. move :Hij. rewrite /ISet.mem !iset_in_def /pid_set in_iseq => />*.
    rewrite /consistent_trace_public in H0 => |>. 
    have : (MaurerProtocol.consistent_views_public c xp (oget (assoc vs i)) (oget (assoc vs j)) i j). rewrite H0 => />*. move :Hij. rewrite /ISet.mem !iset_in_def /pid_set in_iseq => />*. move :Hij. rewrite /ISet.mem !iset_in_def /pid_set in_iseq => />*. rewrite (_:MaurerWeakReveal.consistent_views=MaurerMPCReveal.P.consistent_views). progress. rewrite (consistent_views_conv c xp vs). rewrite H. rewrite H0 => />*. move :Hij. rewrite /ISet.mem in_iseq iset_in_def => />*. move :Hij. rewrite /ISet.mem in_iseq !iset_in_def => />*. progress.
    rewrite valid_inputs_to => />. move => i Hi1 Hi2. rewrite /consistent_trace_public in H0 => |>. 
    have : (MaurerProtocol.consistent_views_public c xp (oget (assoc vs i)) (oget (assoc vs i)) i i). rewrite H0 => />*. rewrite in_iseq => />*. rewrite in_iseq => />*. rewrite /consistent_views_public => |>H1. rewrite /get_trace_inputs /tr /from_views_t /fst3 => />*. rewrite MaurerP.get_map => />*. rewrite MaurerP.get_init => />*. rewrite andabP andaP /size => />*. rewrite /from_view_t /from_input_t => />*. rewrite size_map => />*. 
    move => i k Hi1 Hi2 Hk1 Hk2. rewrite /consistent_trace_public in H0 => |>. 
    have : (MaurerProtocol.consistent_views_public c xp (oget (assoc vs i)) (oget (assoc vs i)) i i). rewrite H0 => />*. rewrite in_iseq => />*. rewrite in_iseq => />*. rewrite /consistent_views_public => |>. rewrite /tr /from_views_t /get_trace_inputs /fst3 /snd3 MaurerP.get_map => |>. rewrite MaurerP.get_init => |>. rewrite /from_view_t andabP andaP /size => |>. rewrite /from_input_t /mkwire_st /IMap.ofset /ISet.iset => |>. rewrite ofset_some => |>. rewrite size_cat => />*. rewrite size_map => />*. rewrite iset_in_def => />*. have : 0 <= size (oget (assoc vs i)).`1.`2. rewrite size_ge0 => />*. smt(). rewrite nth_cat => |>. rewrite size_map => |>. rewrite Hk2 => |>. rewrite !(nth_map witness) => |>. 
    rewrite /valid_inputs' allP => |>x. rewrite in_iseq allP => |>Hx1 Hx2 y. rewrite in_iseq => |>Hy1 Hy2. rewrite (consistent_trace_public_consistent_inputs c xp vs) => |>. 
    move => pid H1. 
    rewrite trace_to_traces_t => |>. rewrite from_to_rands_t => |>. rewrite !eq2 => |>. rewrite rand_to_rands_t /get_trace_rands /thr3 => |>. rewrite !MaurerP.get_map => |>. move :H1. rewrite in_iseq => />*. move :H1. rewrite in_iseq => />*.  
    rewrite /input /mk_inputs /to_sinputs /get_trace_inputs => |>. rewrite assoc_map_r H1 => |>. rewrite /to_sinputs_t /fst3 /snd3 => |>. rewrite assoc_map_r H1 => |>. rewrite /to_sinput_t !MaurerP.get_map => |>. move :H1. rewrite in_iseq => |>. rewrite /consistent_trace_public in H0 => |>.
    have : (MaurerProtocol.consistent_views_public c xp (oget (assoc vs pid)) (oget (assoc vs pid)) pid pid). rewrite H0 => |>. rewrite /consistent_views_public => |>. rewrite /tr /from_views_t /from_view_t => |>. rewrite !MaurerP.get_init /get_wire_st_shr => |>. have : 0 <= pid < MaurerP.size. move :H1. rewrite in_iseq /size => |>. move => H2. rewrite !H2 /get_wire_st_next /get_wire_st_fdom => |>. move => H3. split. 
    apply (eq_from_nth witness) => |>. rewrite !size_map => />*. rewrite size_iseq => />*. rewrite ge0_max => />*. rewrite /from_input_t => />*. rewrite size_cat => />*. rewrite !size_map => />*. rewrite /ISet.card /ISet.iset /IMap.ofset /mkwire_st card_iset => />*. rewrite size_ge0 => />*. rewrite (_: size (oget (assoc vs pid)).`1.`1 + size (oget (assoc vs pid)).`1.`2 - size (oget (assoc vs pid)).`1.`1 = size (oget (assoc vs pid)).`1.`2 ) => />*. algebra. rewrite size_ge0 => />*. rewrite /from_input_t => />*. rewrite size_cat => />*. rewrite /mkwire_st /IMap.ofset /ISet.iset size_map => />*. rewrite /ISet.card card_iset => />*. rewrite size_ge0 => />*. algebra. 
    move => i Hi1 Hi2.
    rewrite !(nth_map witness) => |>. rewrite size_iseq => />*. rewrite ge0_max => />*. rewrite /from_input_t => />*. rewrite size_cat => />*. rewrite !size_map => />*. rewrite /miwire_st /ISet.card /ISet.iset card_iset => />*. rewrite size_ge0 => />*. rewrite /mkwire_st /IMap.ofset => />. smt(size_ge0). rewrite /from_input_t => />*. rewrite size_cat => />*. rewrite size_map => />*. rewrite /mkwire_st /ISet.card /ISet.iset /IMap.ofset card_iset => />*. rewrite size_ge0 => />*. smt(). 
    rewrite nth_iseq => |>. rewrite Hi1 => |>. have : i < ((MaurerProtocolFunctionality.from_input_t pid (oget (assoc vs pid)).`1)).`1.`1 - ISet.card ((MaurerProtocolFunctionality.from_input_t pid (oget (assoc vs pid)).`1)).`2. rewrite /from_input_t => |>. rewrite size_cat => />*. rewrite !size_map => />*. rewrite /ISet.card card_iset => />*. rewrite size_ge0 => />*. rewrite /mkwire_st => />. smt(). move => nots. rewrite nots => |>. rewrite /from_input_t => |>. rewrite /ISet.card card_iset => |>. rewrite size_ge0 => />*. rewrite /IMap.ofset /mkwire_st => />. rewrite ofset_some => />*. rewrite size_cat => />*. rewrite !size_map => />*. rewrite iset_in_def => />*. progress. rewrite succ_ge0 => />*. rewrite size_ge0 => />*. smt(size_ge0).
    rewrite nth_cat => />*. rewrite !size_map => />*. have : ! size (oget (assoc vs pid)).`1.`1 + i < size (oget (assoc vs pid)).`1.`1. smt(size_ge0). move => notsz. rewrite notsz => />*. smt().
    rewrite (MaurerReveal.stateful_local_consistency c.`1 tr) => />*. 
    rewrite /get_trace_inputs /from_views_t /from_inputs_t => />*. rewrite /fst3 MaurerP.tP /size => />i Hi1 Hi2. rewrite MaurerP.get_init andabP andaP => />*. rewrite MaurerP.get_map => />*. rewrite assoc_map_r => />*. rewrite /from_views_t /from_view_t /tr !in_iseq /size => />*. rewrite !assoc_map_r => />*. rewrite !in_iseq !Hi1 !Hi2 => />. rewrite !MaurerP.get_map => />*. rewrite /from_views_t /from_view_t => />*. rewrite MaurerP.get_init => />*. rewrite /size !andabP !andaP => />*. congr. rewrite eq2 => />*. split. 
    have : (MaurerProtocol.consistent_views_public c (oget (assoc vs pid)).`1.`1 (oget (assoc vs i)) (oget (assoc vs i)) i i). rewrite H0 => />*. rewrite in_iseq => />*. rewrite in_iseq => />*. rewrite /consistent_views_public => />. progress. rewrite H4 => />*. 
    apply (eq_from_nth witness) => |>. rewrite !size_map => |>. rewrite size_iseq /from_input_t => |>. rewrite /ISet.card /mkwire_st card_iset => |>. rewrite size_ge0 => />*. rewrite size_cat => />*. rewrite !size_map => />*. rewrite ge0_max => />*. rewrite (_:size (oget (assoc vs i)).`1.`1 + size (oget (assoc vs i)).`1.`2 - size (oget (assoc vs i)).`1.`1 = size (oget (assoc vs i)).`1.`2). algebra. rewrite size_ge0 => />*. algebra.
    move => j. rewrite !size_map size_iseq => |>. rewrite ge0_max => |>. rewrite /from_input_t /ISet.card => />. rewrite /mkwire_st card_iset => />. rewrite size_map => />. rewrite size_ge0 => />. rewrite !size_cat !size_map => />. have : size (fst3 (oget (assoc vs i))).`1 + size (fst3 (oget (assoc vs i))).`2 - size (fst3 (oget (assoc vs i))).`1 = size (fst3 (oget (assoc vs i))).`2. algebra. move => A. rewrite A. rewrite size_ge0 //. rewrite /from_input_t /mkwire_st /ISet.card => |>. rewrite !size_cat !size_map card_iset => />. rewrite size_ge0 =>/>. rewrite (_: size (fst3 (oget (assoc vs i))).`1 + size (fst3 (oget (assoc vs i))).`2 - size (fst3 (oget (assoc vs i))).`1 = size (fst3 (oget (assoc vs i))).`2). algebra. move => Hj1 Hj2.
    rewrite (nth_map witness) => |>. rewrite size_iseq => |>. rewrite ge0_max => |>. rewrite size_ge0 => |>.
    rewrite /IMap.ofset ofset_some => />*. rewrite iset_in_def => />*. progress. rewrite succ_ge0 => />*. rewrite size_ge0 => />*. rewrite nth_iseq => />. rewrite Hj1 Hj2 => />. rewrite nth_iseq => />. rewrite Hj1 Hj2 => />. smt(size_ge0).
    rewrite nth_cat => />*. rewrite !size_map => />*. rewrite !nth_iseq => />. rewrite !Hj1 Hj2 => />. have : ! size (oget (assoc vs i)).`1.`1 + j < size (oget (assoc vs i)).`1.`1. smt(size_ge0). move => notsz. rewrite notsz => />*. smt().
    rewrite -MaurerReveal.equiv_pairwise_consistency. rewrite (_:MaurerReveal.pairwise_consistent_trace=MaurerMPCReveal.P.pairwise_consistent_trace). progress. rewrite to_pairwise_consistent_trace => |>i j Hi Hj. have : (MaurerProtocol.consistent_views_public c (oget (assoc vs pid)).`1.`1 (oget (assoc vs i)) (oget (assoc vs j)) i j). rewrite H0 => />*. rewrite /consistent_views_public => />*. 
    rewrite /tr /from_views_t => />. rewrite MaurerP.get_init andabP /size andaP => />. move :H3. rewrite /consistent_views => />. rewrite /get_wire_st_next /get_wire_st_fdom /get_view_in_msgs /get_view_out_msgs /from_view_t /get /from_input_t => />. progress. move :H3. rewrite /valid_view_t => />. progress. 
    have : 0 <= pid /\ pid < 5. move :H2. rewrite /size => />. move => pidsz. rewrite !pidsz => />. qed.

  lemma backward_consistency (c : MaurerProtocolFunctionality.circuit_t) xp (vs : MaurerProtocol.views_t) :
    MaurerProtocolFunctionality.valid_circuit c =>
    (exists rs sx, let xs = MaurerProtocolFunctionality.mk_inputs xp sx in 
                   MaurerProtocol.valid_rands c rs /\ MaurerProtocolFunctionality.valid_inputs c xs /\
                   let (tr,y) = MaurerProtocol.protocol c rs xs in
                   (forall pid, pid \in MaurerProtocolFunctionality.pid_set => oget (assoc vs pid) =
                     (MaurerProtocolFunctionality.input pid xs,(MaurerProtocol.rand pid rs,MaurerProtocol.trace pid tr))))
    => MaurerProtocol.consistent_trace_public c xp vs.
    progress. move :H2. rewrite (prod_id (MaurerProtocol.protocol c rs ((MaurerProtocolFunctionality.mk_inputs xp sx)))) => />. move => H2. rewrite /consistent_trace_public /consistent_views_public /consistent_views. simplify. move => i j Hi Hj. 
    pose tr := MaurerProtocol.from_views_t vs.
    rewrite (_: ((MaurerProtocol.from_view_t i (oget (assoc vs i)))) = ((MaurerMPCReveal.P.ST.get_view i tr)) ). rewrite /tr /from_views_t /get_view => />*. rewrite /get MaurerP.get_init => />*. move :Hi. rewrite in_iseq /size => />*. 
    rewrite (_: ((MaurerProtocol.from_view_t j (oget (assoc vs j)))) = ((MaurerMPCReveal.P.ST.get_view j tr)) ). rewrite /tr /from_views_t /get_view => />*. rewrite /get MaurerP.get_init => />*. move :Hj. rewrite in_iseq /size => />*. 
    rewrite pairwise_consistent_views_conv. move :Hi. rewrite in_iseq => />*. move :Hj. rewrite in_iseq => />*. rewrite H. 
    rewrite (MaurerMPCReveal.P.pairwise_global_consistency' c.`1 (MaurerProtocolFunctionality.from_inputs_t (MaurerProtocolFunctionality.mk_inputs xp sx)) (MaurerProtocol.from_rands_t rs) tr i j) => |>. move :Hi. rewrite /ISet.mem iset_in_def in_iseq => />*. move :Hj. rewrite /ISet.mem iset_in_def in_iseq => />*. rewrite /tr /from_views_t => />*. rewrite MaurerP.tP /size => />k Hk1 Hk2. rewrite MaurerP.get_init andabP andaP => />*. rewrite /from_view_t => />*. rewrite !H2 => />*. rewrite in_iseq => />*. rewrite !eq2 => />. 
    rewrite /protocol /from_inputs_t => />. rewrite MaurerP.get_zip3 /size andabP andaP => />. rewrite MaurerP.get_init /size andabP andaP => />. 
    rewrite /MaurerProtocol.protocol /from_inputs_t /from_rands_t !Hk1 !Hk2 => />. rewrite !Hk1 !Hk2 => />. rewrite !Hk1 !Hk2 => />. rewrite !MaurerP.get_init /size !Hk1 !Hk2 => />. rewrite /snd3 trace_to_traces_t => />. rewrite in_iseq => />. rewrite MaurerP.get_map => />. rewrite MaurerReveal.equiv_stateful_protocol => />K1 K2 K3. 
    rewrite /protocol => />*. rewrite MaurerP.get_zip3 andabP andaP => />*. rewrite /from_rands_t => />. rewrite valid_inputs_from => />. rewrite valid_rands_from => />. 
    rewrite !H2 => />*. rewrite /mk_inputs /input => />*. rewrite !assoc_map_r => />*. rewrite !Hi !Hj => />*. rewrite /valid_view_t /MaurerProtocol.protocol => />*. rewrite !trace_to_traces_t => />*.
    move :H1. rewrite /valid_inputs /valid_inputs' allP => |>H1 H3. 
    have : all
        (fun (j0 : int) =>
           MaurerProtocolFunctionality.consistent_inputs c i j0
             (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t (MaurerProtocolFunctionality.mk_inputs xp sx)) i)
             (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t (MaurerProtocolFunctionality.mk_inputs xp sx)) j0))
        (iseq 5). rewrite H3 => />. rewrite allP => />H4.
    have : (MaurerProtocolFunctionality.consistent_inputs c i j ((MaurerP.get ((MaurerProtocolFunctionality.from_inputs_t ((MaurerProtocolFunctionality.mk_inputs xp sx)))) i)) ((MaurerP.get ((MaurerProtocolFunctionality.from_inputs_t ((MaurerProtocolFunctionality.mk_inputs xp sx)))) j))). rewrite H4 => |>. rewrite /consistent_inputs. rewrite /from_inputs_t /mk_inputs /get_view. rewrite /get_wire_st_next !MaurerP.get_init /size => |>. move :Hi Hj. rewrite !in_iseq /size. move => Hi' Hj'. rewrite !andabP. simplify. rewrite /tr /from_views_t /from_view_t !assoc_map_r. rewrite !Hi' Hj' => |>. rewrite !in_iseq /size. rewrite !Hi' !Hj' => |>. rewrite /get !MaurerP.get_init => |>. rewrite /size !andabP !Hi' !Hj' => |>. move => K1 K2 K3 K4 K5 K6 K7. rewrite !H2 => />. rewrite in_iseq /size => />. rewrite in_iseq /size => />. rewrite /input /mk_inputs !assoc_map_r => />. rewrite !in_iseq /size => />. rewrite !Hi' !Hj' => />. qed.

  clone include Protocol with

    theory F = MaurerProtocolFunctionality,

    type rand_t <- MaurerProtocol.rand_t,
    op valid_rand <- MaurerProtocol.valid_rand,
    type in_messages_t <- MaurerProtocol.in_messages_t,
    type poutput_t <- MaurerProtocol.poutput_t,
    op local_output <- MaurerProtocol.local_output,
    op protocol <- MaurerProtocol.protocol,
    op consistent_views <- MaurerProtocol.consistent_views
    proof *.
    realize correct.
    rewrite /protocol /f => |>c rs xs H H0 H1. rewrite (_:MaurerReveal.stateful_protocol=MaurerMPCRevealProofs.M.P.stateful_protocol). progress. rewrite -MaurerMPCRevealProofs.mpc_correctness => |>.
    rewrite (_:MaurerMPCRevealProofs.M.P.valid_rands=MaurerMPCReveal.P.valid_rands). progress. rewrite valid_rands_from => |>. 
    rewrite (_:MaurerMPCRevealProofs.M.P.valid_inputs=MaurerMPCReveal.P.valid_inputs). progress. rewrite valid_inputs_from => |>. 
    rewrite to_outputs_t_pinit' => />. qed.
    realize correct_domain.
    rewrite /protocol /pid_set /to_traces_t /from_inputs_t => />c rs xs. rewrite -!map_comp /(\o) => />*. rewrite !id_map => />*. qed.
    realize local_output_correct.
    rewrite /local_output /protocol /pid_set /output /trace => |>c pid xs rs H. rewrite assoc_to_traces_t => />*. rewrite /from_view_t => />*. rewrite MaurerP.get_map => />*. move :H. rewrite in_iseq /size => />*. rewrite assoc_to_outputs_t' /snd3 => />*.
    rewrite (_:MaurerReveal.stateful_protocol=MaurerMPCReveal.P.stateful_protocol). progress. rewrite !MaurerMPCReveal.P.equiv_stateful_protocol => />*. rewrite (_:rand=MaurerProtocol.rand). progress. rewrite (_:F.input=MaurerProtocolFunctionality.input). progress. rewrite local_output_view => |>.
    rewrite (_:(MaurerReveal.local_protocol pid (fst3 c)
   (MaurerP.get
      (MaurerMPCReveal.P.protocol (fst3 c) (MaurerProtocolFunctionality.from_inputs_t xs)
         (MaurerProtocol.from_rands_t rs)).`1 pid)).`2=(MaurerMPCReveal.P.local_protocol pid (fst3 c) (MaurerMPCReveal.P.ST.P.get (MaurerMPCReveal.P.protocol (fst3 c) (MaurerProtocolFunctionality.from_inputs_t xs) (MaurerProtocol.from_rands_t rs)).`1 pid)).`2). progress.
    rewrite MaurerMPCReveal.P.local_protocol_snd_repeat => />. move :H. rewrite /ISet.mem in_iseq iset_in_def => />*. qed.
    realize global_consistency.
    move => c xp vs H. split. move => H0. 
    apply (forward_consistency c xp vs) => |>.
    apply (backward_consistency c xp vs) => |>. qed.
    realize messages_consistency.
    move => c i j xs rs H H0 H1 H2 H3. rewrite (prod_id (MaurerProtocol.protocol c rs xs)). simplify. rewrite /MaurerProtocol.protocol. simplify. rewrite (_:trace=MaurerProtocol.trace). progress. rewrite !trace_to_traces_t /snd3. rewrite H. rewrite H0. rewrite !MaurerP.get_map. move :H. rewrite in_iseq => |>. move :H0. rewrite in_iseq => |>. 
    pose tr := ((MaurerReveal.stateful_protocol c.`1 ((MaurerProtocolFunctionality.from_inputs_t xs)) ((MaurerProtocol.from_rands_t rs)))).`1. rewrite /consistent_views. simplify.
    rewrite (_: (MaurerProtocol.from_view_t i
     (F.input i xs,
      (rand i rs, (map (fun (i0 : int) => (i0, tt)) MaurerProtocolFunctionality.pid_set, snd3 (MaurerP.get tr i))))) = MaurerReveal.ST.get_view i tr). rewrite /get_view /from_view_t /input => |>. rewrite /tr => |>. rewrite !eq2 => |>. progress.
    rewrite /stateful_protocol => |>. rewrite /get MaurerP.get_zip3 => |>. move :H. rewrite in_iseq /size => |>Hi1 Hi2. rewrite /from_inputs_t => |>. rewrite MaurerP.get_init andabP /size Hi1 Hi2 => |>. 
    rewrite /stateful_protocol => |>. rewrite /rand /from_inputs_t /get MaurerP.get_zip3 => |>. move :H. rewrite in_iseq /size => |>Hi1 Hi2. rewrite /from_rands_t => |>. rewrite MaurerP.get_init /size andabP andaP => |>. 
    rewrite /stateful_protocol => |>. rewrite /rand /from_inputs_t /get MaurerP.get_zip3 => |>. move :H. rewrite in_iseq /size => |>Hi1 Hi2. rewrite /from_rands_t => |>. rewrite MaurerP.get_init /size andabP andaP => |>. 
    rewrite /stateful_protocol => |>. rewrite /rand /from_inputs_t /get MaurerP.get_zip3 => |>. move :H. rewrite in_iseq /size => |>Hi1 Hi2. rewrite /from_rands_t => |>. rewrite MaurerP.get_init /size andabP andaP => |>. 
    rewrite (_: (MaurerProtocol.from_view_t j
     (F.input j xs,
      (rand j rs, (map (fun (i0 : int) => (i0, tt)) MaurerProtocolFunctionality.pid_set, snd3 (MaurerP.get tr j))))) = MaurerReveal.ST.get_view j tr). rewrite /get_view /from_view_t /input => |>. rewrite /tr => |>. rewrite !eq2 => |>. progress.
    rewrite /stateful_protocol => |>. rewrite /get MaurerP.get_zip3 => |>. move :H0. rewrite in_iseq /size => |>Hj1 Hj2. rewrite /from_inputs_t => |>. rewrite MaurerP.get_init andabP /size Hj1 Hj2 => |>. 
    rewrite /stateful_protocol => |>. rewrite /rand /from_inputs_t /get MaurerP.get_zip3 => |>. move :H0. rewrite in_iseq /size => |>Hj1 Hj2. rewrite /from_rands_t => |>. rewrite MaurerP.get_init /size andabP andaP => |>. 
    rewrite /stateful_protocol => |>. rewrite /rand /from_inputs_t /get MaurerP.get_zip3 => |>. move :H0. rewrite in_iseq /size => |>Hj1 Hj2. rewrite /from_rands_t => |>. rewrite MaurerP.get_init /size andabP andaP => |>. 
    rewrite /stateful_protocol => |>. rewrite /rand /from_inputs_t /get MaurerP.get_zip3 => |>. move :H0. rewrite in_iseq /size => |>Hj1 Hj2. rewrite /from_rands_t => |>. rewrite MaurerP.get_init /size andabP andaP => |>. 
    rewrite pairwise_consistent_views_conv => |>. move :H. rewrite in_iseq => |>. move :H0. rewrite in_iseq => |>. 
    rewrite (MaurerMPCReveal.P.pairwise_global_consistency' c.`1 (MaurerProtocolFunctionality.from_inputs_t xs) (MaurerProtocol.from_rands_t rs) tr i j) => />. move :H. rewrite /ISet.mem in_iseq iset_in_def => />. move :H0. rewrite /ISet.mem in_iseq iset_in_def => />. rewrite /tr MaurerReveal.equiv_stateful_protocol => |>. rewrite valid_inputs_from => |>. rewrite valid_rands_from => |>.
    move :H3. rewrite /valid_inputs /valid_inputs' allP => |>X1 X2.
    have : all
        (fun (j0 : int) =>
           MaurerProtocolFunctionality.consistent_inputs c i j0
             (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t xs) i)
             (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t xs) j0)) (
        iseq 5). rewrite X2 => |>. rewrite allP => |>X3. 
    have : (MaurerProtocolFunctionality.consistent_inputs c i j ((MaurerP.get ((MaurerProtocolFunctionality.from_inputs_t xs)) i)) ((MaurerP.get ((MaurerProtocolFunctionality.from_inputs_t xs)) j))). rewrite X3 => |>. rewrite /consistent_inputs. rewrite /from_inputs_t /mk_inputs /get_view. rewrite /get_wire_sts_next /get_wire_st_fdom !MaurerP.get_init /size. move :H H0. rewrite !in_iseq /size. move => Hi Hj. rewrite !andabP !Hi !Hj => |>. rewrite /get_wire_st_next => |>. move => K1 K2 K3 K4 K5 K6 K7. move :H2. rewrite /valid_circuit => |>K8 K9 K10 K11. rewrite /tr /from_views_t /from_view_t. rewrite /stateful_protocol /from_inputs_t. simplify. rewrite /get !MaurerP.get_zip3 !andabP /size !Hi !Hj => |>. simplify. rewrite !MaurerP.get_init !andabP /size !Hi !Hj. simplify. progress. qed.

end MaurerCompatProofs.

  (* for MitH *)
  lemma valid_inputs_shares c xs :
    MaurerProtocolFunctionality.valid_circuit c =>
    MaurerProtocolFunctionality.valid_inputs c xs => MaurerLSSS.valid_shares (MaurerProtocolFunctionality.sinputs xs).
    move => H. rewrite /valid_inputs /valid_inputs' /valid_shares !allP /sinputs => />H0 H1.
    rewrite -map_comp /(\o) => />. rewrite map_id => />. move => x. rewrite in_iseq => />Hx1 Hx2. rewrite allP => />y. rewrite in_iseq => />Hy1 Hy2.
    rewrite /get_party_share => />. have : all (fun (j : int) => MaurerProtocolFunctionality.consistent_inputs c x j (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t xs) x) (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t xs) j)) (iseq 5). rewrite H1 => />. rewrite in_iseq => />. rewrite allP => />H2. clear H1. have : MaurerProtocolFunctionality.consistent_inputs c x y (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t xs) x) (MaurerP.get (MaurerProtocolFunctionality.from_inputs_t xs) y). rewrite H2 => />. rewrite in_iseq => />. clear H2. rewrite /consistent_inputs => />. rewrite /from_inputs_t /from_input_t /get_wire_st_next /get_wire_st_fdom /get_wire_st_shr => />. rewrite !MaurerP.get_init /size /mkwire_st !andabP !Hx1 !Hx2 !Hy1 !Hy2 => />. rewrite !size_cat !size_map => />. rewrite /ISet.iset /IMap.ofset !fdom_ofset /ISet.equal => />. move => |> H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
    rewrite !assoc_map_r => />. rewrite !in_iseq !andaP => />. 
    have : card (iset (size (oget (assoc xs x)).`1)) = card (iset (size (oget (assoc xs y)).`1)). rewrite H3 H4 => />. rewrite !card_iset => />. rewrite size_ge0 => />. rewrite size_ge0 => />. move => Sz1.
    move : H1. rewrite -H2 !Sz1 => />. smt(). move => Sz.
    rewrite allP => />p Hp.
    rewrite /consistent_shares => />. move :H13. rewrite all_iseqE allP => />H13.
    move :Hp. rewrite in_nth => />. move => i. rewrite !size_zip Sz min_eq => />Hi1 Hi2. 
    rewrite !nth_onth !(onth_nth (witness,witness)) => />. rewrite size_zip Sz min_eq => />. rewrite !nth_zip => />. pose x0 := size (oget (assoc xs x)).`1 + i.
    have : MaurerAPI.consistent_raw_shares x y
         (oget
            (ofset (nth witness (cat (map (MaurerAPI.party_pshare x) (oget (assoc xs x)).`1) (oget (assoc xs x)).`2))
               (iset (size (oget (assoc xs x)).`1 + size (oget (assoc xs x)).`2))).[x0])
         (oget
            (ofset (nth witness (cat (map (MaurerAPI.party_pshare y) (oget (assoc xs y)).`1) (oget (assoc xs y)).`2))
               (iset (size (oget (assoc xs y)).`1 + size (oget (assoc xs y)).`2))).[x0]). rewrite H13 => />. rewrite /x0 in_iseq => />. have : 0 <= size (oget (assoc xs x)).`1. rewrite size_ge0 => />. smt(). 
    rewrite !ofset_some => />. rewrite /x0 !iset_in_def => />. have : 0 <= size (oget (assoc xs x)).`1. rewrite size_ge0 => />. smt(). rewrite /x0 !iset_in_def => />. have : 0 <= size (oget (assoc xs y)).`1. rewrite size_ge0 => />. smt(). 
    rewrite !nth_cat => />. rewrite /x0 !size_map consistent_raw_shares_conv => />. rewrite !if_else => />. smt(). smt().
    rewrite (_:(size (oget (assoc xs x)).`1 + i - size (oget (assoc xs x)).`1)=i). algebra. 
    rewrite (_:(size (oget (assoc xs x)).`1 + i - size (oget (assoc xs y)).`1)=i). have : size (oget (assoc xs x)).`1 = size (oget (assoc xs y)).`1. smt(). move => Sz1. rewrite Sz1. algebra.
    progress. qed.
    
