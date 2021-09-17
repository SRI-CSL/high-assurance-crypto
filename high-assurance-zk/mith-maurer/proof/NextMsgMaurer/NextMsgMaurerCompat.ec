

(* general *)
require import AllCore List Distr.

(* hugo *)
require import Aux AuxList.
require import NextMsgMaurer NextMsgMaurerMPC NextMsgISet NextMsgIMap NextMsgArray.
require import NextMsgMaurerP NextMsgMaurerAPI.
import MaurerAPI ISet IMap Array.

(* vitor *)
require import ADomain.
require import AProtocol.
require import AProtocolFunctionality.

theory MaurerDomain.

  clone include Domain with
    type wire_t = val,
    op wire_to_bool (w:wire_t) : bool = (w = zero_val).

end MaurerDomain.

theory MaurerProtocolFunctionality.

  type pinput_tt = val list.
  type sinput_tt = shr list.
  type input_tt = pinput_tt * sinput_tt.
  type inputs_tt = (int * input_tt) list.
  type sinputs_tt = (int * sinput_tt) list.
  type outputs_tt = (int * val) list.

  op from_input_t i (x: input_tt) : MaurerGate.share =
    let pubs = map (party_pshare i) x.`1 in
    let secs = x.`2 in
    let shrs = pubs ++ secs in
    let wst = mkwire_st i (size shrs) (IMap.ofset (fun wid => (nth witness shrs wid)) (ISet.iset (size shrs))) in
    let pst = ISet.iset (size pubs) in
    (wst,pst).

  op from_inputs_t (xs: inputs_tt) : MaurerGate.share MaurerP.arrayN =
    MaurerP.init (fun i => from_input_t i (oget (assoc xs i))).

  op to_pinput_t (xs:MaurerGate.share) : pinput_tt =
    let npubs = ISet.card xs.`2 in
    map (fun k => party_unpshare (get_wire_st_shr xs.`1 k) ) (iseq npubs).
  op to_sinput_t (xs:MaurerGate.share) : sinput_tt =
    let npubs = ISet.card xs.`2 in
    let nsecs = get_wire_st_next xs.`1 - npubs in
    map (fun k => get_wire_st_shr xs.`1 (npubs + k) ) (iseq nsecs).
  op to_input_t (xs:MaurerGate.share) : input_tt =
    (to_pinput_t xs,to_sinput_t xs).
  op to_sinputs_t (xs:MaurerGate.share MaurerP.arrayN) : sinputs_tt =
    map (fun i => (i,to_sinput_t (MaurerP.get xs i) )) (iseq 5).

  op to_outputs_t (o:val) : outputs_tt =
    map (fun i => (i,o)) (iseq 5).

  op from_outputs_t (o:outputs_tt) : val =
    (head witness o).`2.

  type circuit_tt = MaurerCircuit.circuit * (wid * ISet.iset).

  op consistent_inputs (c:circuit_tt) i j (wi wj:MaurerGate.share) =
    get_wire_st_next wi.`1 = c.`2.`1 /\ get_wire_st_next wj.`1 = c.`2.`1 /\
    ISet.equal wi.`2 c.`2.`2 /\ ISet.equal wj.`2 c.`2.`2 /\ 
    g_valid_share wi /\ g_valid_share wj /\
    consistent_shares i j wi wj.

  op valid_inputs' (c:circuit_tt) ws =
    all (fun i => all (fun j => consistent_inputs c i j (MaurerP.get ws i) (MaurerP.get ws j)) (iseq 5)) (iseq 5).

  clone include ProtocolFunctionality with

    type circuit_t = MaurerCircuit.circuit * (wid * ISet.iset),
    op n = 5,
    op t = 2,
    type pid_t = int,
    op pid_set = iseq 5,

    type pinput_t = val list,
    type sinput_t = shr list,

    op valid_circuit (c:circuit_t) : bool =
      MaurerCircuit.valid_circuit c.`1 c.`2.`1 c.`2.`2,
      
    op valid_inputs (c : circuit_t) (xs : inputs_t) : bool =
      unzip1 xs = pid_set /\ 
      valid_inputs' c (from_inputs_t xs),

    type output_t = val,

    op f (c:circuit_t) (xs:inputs_t) : outputs_t =
      let ws = from_inputs_t xs in
      let o = MaurerMPCReveal.functionality c.`1 ws in
      to_outputs_t o

    proof *.
    realize n_pos. rewrite /n => />*. qed.
    realize t_pos. rewrite /t => />*. qed.
    realize pid_set_uniq. rewrite /pid_set iseq_5 => />*. qed.
    realize pid_set_size. rewrite size_iseq => />*. qed.

  op to_inputs_t xp (xs:MaurerGate.share MaurerP.arrayN) : inputs_tt =
    mk_inputs xp (to_sinputs_t xs).

end MaurerProtocolFunctionality.

theory MaurerProtocol.

  type poutput_tt = unit.
  type poutputs_tt = (MaurerProtocolFunctionality.pid_t * poutput_tt) list.
  type in_messages_tt = MaurerReveal.ST.in_msgs.
  type trace_tt = poutputs_tt * in_messages_tt.
  type traces_tt = (MaurerProtocolFunctionality.pid_t * trace_tt) list.
  type rand_tt = MaurerGate.GT.local_rand list.
  type rands_tt = (MaurerProtocolFunctionality.pid_t * rand_tt) list.
  type view_tt = MaurerProtocolFunctionality.input_t * (rand_tt * trace_tt).
  type views_tt = (MaurerProtocolFunctionality.pid_t * view_tt) list.

  op to_rands_t (rs:MaurerReveal.ST.local_rand MaurerP.arrayN) : (rands_tt) =
    MaurerP.to_assoc rs.

  op from_rands_t (rs:rands_tt) : MaurerReveal.ST.local_rand MaurerP.arrayN =
    MaurerP.init (fun i => oget (assoc rs i)).

  op to_view_t (v:MaurerReveal.ST.view) : view_tt =
    let pouts = map (fun i => (i,tt)) MaurerProtocolFunctionality.pid_set in
    (MaurerProtocolFunctionality.to_input_t v.`1,(v.`2.`2,(pouts,v.`2.`1))).

  op from_view_t i (v:view_tt) : MaurerReveal.ST.view =
    (MaurerProtocolFunctionality.from_input_t i v.`1,(v.`2.`2.`2,v.`2.`1)).

  op from_views_t (vs:views_tt) : MaurerReveal.ST.trace = 
    MaurerP.init (fun i => from_view_t i (oget (assoc vs i))).

  op to_traces_t (msgs: MaurerReveal.ST.in_msgs MaurerP.arrayN) : traces_tt =
    let pouts = map (fun i => (i,tt)) MaurerProtocolFunctionality.pid_set in
    map (fun i => (i,(pouts,MaurerP.get msgs i))) MaurerProtocolFunctionality.pid_set.

  op to_outputs_t' (o:MaurerReveal.ST.local_output MaurerP.arrayN) : MaurerProtocolFunctionality.outputs_tt =
    map (fun i => (i,MaurerP.get o i)) MaurerProtocolFunctionality.pid_set.

  op valid_view_t (i:MaurerProtocolFunctionality.pid_t) (v:view_tt) =
     v.`2.`2.`1 = map (fun i => (i,tt)) MaurerProtocolFunctionality.pid_set.

  op consistent_rands' x ri rj =
    MaurerCircuit.circ_valid_rand x ri /\
    MaurerCircuit.circ_valid_rand x rj.

  op consistent_views' (x:MaurerProtocolFunctionality.circuit_t) (i j:int) (vi vj:MaurerReveal.ST.view) : bool =
    MaurerReveal.ST.valid_view x.`1 vi /\ MaurerReveal.ST.valid_view x.`1 vj /\ 
    MaurerReveal.ST.eq_rmsgs (MaurerReveal.get_view_in_msgs j vi) (MaurerReveal.get_view_out_msgs j i x.`1 vj) /\
    MaurerReveal.ST.eq_rmsgs (MaurerReveal.get_view_in_msgs i vj) (MaurerReveal.get_view_out_msgs i j x.`1 vi) /\
    MaurerProtocolFunctionality.consistent_inputs x i j vi.`1 vj.`1 /\
    consistent_rands' x.`1 vi.`2.`2 vj.`2.`2. 

  clone include Protocol with

    theory F = MaurerProtocolFunctionality,

    type rand_t = MaurerGate.GT.local_rand list,
    op valid_rand (c:F.circuit_t) (r:rand_t) =
      MaurerCircuit.circ_valid_rand c.`1 r,
    
    type in_messages_t = MaurerReveal.ST.in_msgs,
    type poutput_t = unit,

    op local_output (c:F.circuit_t) i (v:view_t) : F.output_t =
      let vi = from_view_t i v in
      (MaurerReveal.local_protocol i c.`1 vi).`2,

    op protocol (c:F.circuit_t) (rs:rands_t) (ws:F.inputs_t) : traces_t * F.outputs_t =
      let ws' = MaurerProtocolFunctionality.from_inputs_t ws in
      let rs' = from_rands_t rs in
      let to' = MaurerReveal.stateful_protocol c.`1 ws' rs' in
      let t = to_traces_t (MaurerP.map snd3 to'.`1) in
      let o = to_outputs_t' to'.`2 in
      (t,o),

    op consistent_views (c :F.circuit_t) (vi vj : view_t) (i j : F.pid_t) : bool =
      let vi' = from_view_t i vi in
      let vj' = from_view_t j vj in
      valid_view_t i vi /\ valid_view_t j vi /\
      consistent_views' c i j vi' vj'.

    op consistent_views_output (c :F.circuit_t) (xp :F.pinput_t) (vi vj : view_t) (i j : F.pid_t) : bool =
      let vi' = from_view_t i vi in
      let vj' = from_view_t j vj in
      MaurerReveal.stateful_consistent_views_outputs c.`1 i j vi' vj'.

    op consistent_views_public_output (c : F.circuit_t) (xp : F.pinput_t) (vi : view_t) (vj : view_t) (i : F.pid_t) (j : F.pid_t) : bool =
            let vi' = (from_view_t i vi) in
            let vj' = (from_view_t j vj) in
            let cv = MaurerReveal.stateful_consistent_views_outputs c.`1 i j vi' vj' in
            let ci = MaurerProtocolFunctionality.consistent_inputs c i j vi'.`1 vj'.`1 in
            let cr = consistent_rands' c.`1 vi'.`2.`2 vj'.`2.`2 in
            cv && ci && cr.

    op from_corrupted_parties_t (cr:MaurerProtocolFunctionality.pid_t list) : MaurerMPCReveal.corrupted_parties =
      oflist cr.

    op to_corrupted_views_t (cr:MaurerProtocolFunctionality.pid_t list) (vs:MaurerMPCReveal.corrupted_views) : views_tt = 
      map (fun i => (i,to_view_t (oget (IMap.get vs i))) ) cr.

    op from_corrupted_inputs_t (xs: MaurerProtocolFunctionality.inputs_tt) : MaurerGate.share MaurerMPCReveal.cmap =
      IMap.imap MaurerProtocolFunctionality.from_input_t (IMap.ofassoc xs).

  op simulator (cr : MaurerProtocolFunctionality.pid_t list) (c :MaurerProtocolFunctionality.circuit_t) (xs : MaurerProtocolFunctionality.inputs_t) (rs : MaurerProtocol.rands_t) (y : MaurerProtocolFunctionality.outputs_t) : MaurerProtocol.views_t =
      let cr' = from_corrupted_parties_t cr in
      let xs' = from_corrupted_inputs_t xs in
      let rs' = from_rands_t rs in
      let y' = MaurerProtocolFunctionality.from_outputs_t y in
      let vs' = MaurerMPCReveal.simulator cr' c.`1 xs' rs' y' in
      to_corrupted_views_t cr vs'.

  op gen_rand (c:MaurerCircuit.Circuit) : rands_tt distr =
     dapply MaurerP.to_assoc (MaurerWeakCircuit.circ_gen_rand c).

end MaurerProtocol.

(* Boolean output, for MitH *)

theory MaurerBoolProtocol.

  clone include BoolProtocol with
    theory P = MaurerProtocol,
    op true_output = zero_val.

end MaurerBoolProtocol.

