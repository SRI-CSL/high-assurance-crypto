require import AllCore Int List.
require import Aux AuxList NextMsgISet NextMsgIMap.
require import NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol.

import Array.

theory Gate.

  type Gate.
  type share.
  type local_msgs.
  type local_in_msgs = local_msgs.
  type local_out_msgs = local_msgs.

  clone import Trace as GT with
    type local_input = share,
    type local_output = share,
    type public_input = Gate,
    op rounds _ = 1
    proof rounds_ge0.
    realize rounds_ge0. progress. qed.

  op local_gate_start : party -> Gate -> share -> local_rand -> local_out_msgs.
  op local_gate_end : party -> Gate -> share -> local_in_msgs -> share.

  op gate_valid_rand : Gate -> local_rand -> bool.
  op gate_valid_rands (x:Gate) (cs:local_rand P.arrayN) =
    P.all (fun _ c => gate_valid_rand x c) cs.

  clone include StatefulProtocol with
    theory ST = GT,
    type local_messages = local_msgs,
    type local_state = share * (local_rand,local_in_msgs) either,
    op init_local_state i g (wis:share) ris = (wis,L ris),
    op stateful_local_protocol_round i _ g (st:share * (local_rand,local_in_msgs) either) = local_gate_start i g (st.`1) (unL st.`2),
    op update_local_state i _ g ins (st:share * (local_rand,local_in_msgs) either) = (st.`1,R ins),
    op stateful_local_protocol_end i g (st:share * (local_rand,local_in_msgs) either) = local_gate_end i g (st.`1) (unR st.`2),
    op consistent_rands x i j ri rj =
      gate_valid_rand x ri /\ gate_valid_rand x rj.

  op g_protocol (x:Gate) (ws:share pmap) (cs:local_rand pmap) : trace * share pmap = 
    let outs = GT.P.imap (fun i (wc:share*local_rand) => local_gate_start i x wc.`1 wc.`2) (GT.P.zip ws cs) in
    let ins = send_messages outs in
    let o = GT.P.imap (fun i (wi:share*local_in_msgs) => local_gate_end i x wi.`1 wi.`2) (GT.P.zip ws ins) in
    let rins = GT.P.map (fun bin => GT.P.map (fun msg => Array.init 1 (fun j => if j=0 then msg else witness)) (from_local_messages bin)) ins in
    let tr = GT.P.zip3 ws rins cs in
    (tr,o).

  lemma valid_local_gate_start j x r ws cs :
    valid_local_messages x r (local_gate_start j x ws cs).
    rewrite (_:(local_gate_start j x ws cs) = stateful_local_protocol_round j 1 x (ws,L cs)). rewrite /stateful_local_protocol_round => />. rewrite valid_stateful_local_protocol_round => />. qed.

end Gate.

(* defines a fixpoint over gates *)
theory Circuit.

  clone import Gate as G.

  type Circuit = Gate list.
  
  clone import Trace as CT with
    theory P = G.GT.P,
    type public_input = Circuit,
    type local_input = share ,
    type local_output = share ,
    type local_rand = GT.local_rand list,
    type msg = GT.msg,
    op eq_msg = G.GT.eq_msg,
    op parties = GT.parties,
    op rounds c = List.size c
    proof *.
    realize rounds_ge0.
    rewrite /rounds => />*. rewrite size_ge0 => />*. qed.
    realize eq_msgP. rewrite /eq_msg => />m1 m2. rewrite G.GT.eq_msgP => />. qed.

  op circ_valid_rand c (rs:local_rand) : bool =
      List.size(c) = List.size(rs) /\ lsame (fun g r => G.gate_valid_rand g r) c rs.

  clone include StatefulProtocol with
    theory ST = CT,
    type local_messages = G.local_msgs,
    op valid_local_messages p r ms = G.valid_local_messages (nth witness p r) 0 ms,
    op valid_msg p r ms = G.valid_msg (nth witness p r) 0 ms,
    op from_local_messages = G.from_local_messages,
    op to_local_messages = G.to_local_messages,
    op send_messages = G.send_messages,
    type local_state = G.share * CT.local_rand,
    op init_local_state i x (ws:local_input) rs = ((ws,rs)),
    op stateful_local_protocol_round i (r:round) (c:public_input) (st:G.share * CT.local_rand) =
      let g = nth witness c r in
      G.local_gate_start i g st.`1 (head witness st.`2),
    op update_local_state i (r:round) (c:public_input) (ins:local_in_messages) (st:G.share * CT.local_rand) =
      let g = nth witness c r in
      (G.local_gate_end i g st.`1 ins,behead st.`2),
    op stateful_local_protocol_end (i:party) (_:public_input) (st:G.share * CT.local_rand) = st.`1,
    op consistent_rands c i j r1 r2 =
      circ_valid_rand c r1 /\ circ_valid_rand c r2
    proof *.
    realize to_from_local_messages by smt(G.to_from_local_messages).
    realize from_to_local_messages.
    move => />p r xs H. rewrite /from_local_messages (G.from_to_local_messages (nth witness p r) 0) => />. qed.
    realize ppswap_from_messages.
    move => p r outs H. rewrite (_:(ST.ppswap<:CT.msg>)=G.ST.ppswap). progress. rewrite (G.ppswap_from_messages (nth witness p r) 0). move :H. rewrite /valid_messages => />. trivial. qed.
    realize valid_pmsgs_from.
    rewrite /valid_local_messages /valid_pmsgs => p r xs H. rewrite ST.P.allP => />i Hi1 Hi2. 
    have : G.valid_pmsgs (nth witness p r) 0 (from_local_messages xs). rewrite G.valid_pmsgs_from => />. rewrite /valid_pmsgs => />. rewrite G.ST.P.allP => />H1. rewrite /valid_msg H1 => />. qed.
    realize get_local_messages_eqP.
    move => xs ys. rewrite G.get_local_messages_eqP => />. qed.
    realize valid_send_messages.
    rewrite /valid_messages => />outs p r. rewrite !ST.P.allP => />H i Hi1 Hi2. rewrite /valid_local_messages => />.
    have : G.valid_messages (nth witness p r) 0 (G.send_messages outs). rewrite G.valid_send_messages => />. rewrite /valid_messages => />. rewrite G.ST.P.allP => />j Hj1 Hj2. rewrite /valid_local_messages in H. rewrite H => />.
    rewrite /valid_messages G.ST.P.allP => />H1. rewrite H1 => />. qed.
    realize valid_stateful_local_protocol_round. 
    rewrite /valid_local_messages /stateful_local_protocol_round => />i r x st. rewrite G.valid_local_gate_start => />. qed.
    realize valid_local_messages_to.
    move => p r xs. rewrite /valid_pmsgs /valid_local_messages /to_local_messages ST.P.allP => />H. rewrite G.valid_local_messages_to => />. rewrite /valid_pmsgs G.ST.P.allP => />j Hj1 Hj2. have : valid_msg p r (ST.P.get xs j). rewrite H => />. rewrite /valid_msg => />. qed.

  op circ_protocol' (c:Gate list) (ws:local_input CT.pmap) (rs:(GT.local_rand list) CT.pmap) : (msg list) CT.ppmap * ((GT.local_rand list) CT.pmap * local_output CT.pmap) = 
    with c = [] => (CT.ppinit (fun _ _ => []),(CT.pinit (fun _ => []),ws))
    with c = g :: c' => 
      let r = P.map (head witness) rs in
      let to = g_protocol g ws r in
      let ws' = to.`2 in
      let r1 = P.map thr3 to.`1 in
      let outs = stateful_protocol_round 0 c (P.zip ws rs) in
      let ins1 = from_messages (send_messages outs) in
      let tro = circ_protocol' c' ws' (P.map behead rs) in
      (CT.ppcons ins1 tro.`1,(CT.pcons r1 tro.`2.`1,tro.`2.`2)).

  op circ_protocol (c:Circuit) (ws:local_input pmap) (rs:local_rand pmap) : (trace * local_output pmap) = 
    let o = circ_protocol' c ws rs in
    let vins = P.map (P.map (rlist (size c))) o.`1 in
    let tr = P.zip3 ws vins (o.`2.`1) in 
    (tr,o.`2.`2).
      
  op circ_valid_rands x cs =
       CT.P.all (fun _ c => circ_valid_rand x c) cs.

end Circuit.

