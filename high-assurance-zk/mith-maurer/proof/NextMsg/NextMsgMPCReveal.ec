require import AllCore Int List Distr.
require import Aux AuxList NextMsgISet NextMsgIMap.
require import NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgCircuit NextMsgWeak NextMsgMPC.

import ISet IMap Array.

(* adds a last reveal step to a protocol *)
theory Reveal.

  clone import StatefulProtocol as M.

  type pub_input.
  op pub_input_conv : pub_input -> M.ST.public_input.
  type final_output.
  op weak_rounds x = M.ST.rounds (pub_input_conv x).

  op reveal_local_start : pub_input -> M.ST.local_output -> M.local_out_messages.
  op reveal_local_end : pub_input -> M.local_in_messages -> final_output.

   op mpc_local_protocol_round i r (x:pub_input) (st:(M.local_state,M.local_out_messages) either) = if r < weak_rounds x
    then M.stateful_local_protocol_round i r (pub_input_conv x) (unL st)
    else reveal_local_start x (M.stateful_local_protocol_end i (pub_input_conv x) (unL st)).

  op mpc_update_local_state i r x ins (st:(M.local_state,M.local_out_messages) either) = if r < weak_rounds x
    then L (M.update_local_state i r (pub_input_conv x) ins (unL st))
    else R ins.

  op mpc_local_protocol_end (i:M.ST.party) (x:pub_input) (st:(M.local_state,M.local_out_messages) either) = reveal_local_end x (unR st).

  op mpc_consistent_inputs (x:pub_input) (i j:M.ST.party) (ss1 ss2:M.ST.local_input) : bool.
  op mpc_consistent_outputs (x:pub_input) (i j:M.ST.party) (ss1 ss2:M.ST.local_output) : bool.

  op final_valid_local_messages : pub_input -> M.local_messages -> bool. 
  op final_valid_msg : pub_input -> M.ST.msg -> bool.

  axiom final_valid_local_send_messages p outs i :
    final_valid_local_messages p (M.ST.P.get outs i) = final_valid_local_messages p (M.ST.P.get ((M.send_messages outs)) i).

  axiom valid_reveal_local_start x o :
   final_valid_local_messages x (reveal_local_start x o).

  axiom final_to_from_local_messages p xs :
    final_valid_local_messages p xs => to_local_messages (from_local_messages xs) = xs.

  axiom final_from_to_local_messages p xs :
    (forall i, 0 <= i < ST.P.size => final_valid_msg p (ST.P.get xs i) ) =>
    from_local_messages (to_local_messages xs) = xs.

  axiom final_ppswap_from_messages p outs :
    (forall i, 0 <= i < ST.P.size => final_valid_local_messages p (ST.P.get outs i)) =>
    ST.ppswap (from_messages outs) = from_messages (send_messages outs).

  axiom final_valid_pmsgs_from p xs i :
    0 <= i < ST.P.size =>
    final_valid_local_messages p xs => final_valid_msg p (ST.P.get (from_local_messages xs) i).

  clone include StatefulProtocol with
    theory ST.P = M.ST.P,
    type ST.local_output = final_output,
    type ST.local_input = M.ST.local_input,
    type ST.public_input = pub_input,
    type ST.local_rand = M.ST.local_rand,
    op ST.rounds x = M.ST.rounds (pub_input_conv x) + 1,
    type ST.msg = M.ST.msg,
    op ST.eq_msg = M.ST.eq_msg,
    
    type local_state = (M.local_state,M.local_out_messages) either,
    type local_messages = M.local_messages,
    op init_local_state i x wi ri = L (M.init_local_state i (pub_input_conv x) wi ri),
    op stateful_local_protocol_round = mpc_local_protocol_round,
    op update_local_state = mpc_update_local_state,
    op stateful_local_protocol_end = mpc_local_protocol_end,
    op valid_local_messages p r xs = if r < weak_rounds p
      then M.valid_local_messages (pub_input_conv p) r xs
      else final_valid_local_messages p xs,
    op valid_msg p r xs = if r < weak_rounds p
      then M.valid_msg (pub_input_conv p) r xs
      else final_valid_msg p xs,
    op to_local_messages = M.to_local_messages,
    op from_local_messages = M.from_local_messages,
    op send_messages = M.send_messages,
    op consistent_inputs = mpc_consistent_inputs,
    op consistent_rands x = M.consistent_rands (pub_input_conv x).

end Reveal.

theory WeakReveal.

  clone import Weak as W.
  clone include Reveal with
    theory M = W.P.

end WeakReveal.

(* security of the combined mpc + reveal protocol *)
theory MPCReveal.

  clone import WeakReveal as WR.

  (* essentially an unsharing functionality / protocol *)
  op reveal_functionality : pub_input -> W.public_output -> final_output.

  op mpc_functionality (x:pub_input) (ws:W.local_inputs) =
    reveal_functionality x (W.functionality (pub_input_conv x) (W.unshare_input ws)).

  op reveal_start (x:pub_input) : W.local_outputs -> M.local_out_messages M.ST.pmap =
    W.P.ST.P.map (reveal_local_start x).

  (* we can reconstruct final messages from the corrupted shares + output *)
  (* a special redundancy property of some secret sharings that allows us to prevent having to perform a final resharing *)
  op reconstruct_final : W.corrupted_parties -> pub_input -> W.corrupted_outputs -> final_output -> W.P.local_out_messages W.P.ST.pmap.

  op valid_outputs (x:pub_input) (ws:W.P.ST.local_output W.P.ST.pmap) : bool =
    forall i j, ISet.mem i W.P.ST.partyset /\ ISet.mem j W.P.ST.partyset => mpc_consistent_outputs x i j (W.P.ST.P.get ws i) (W.P.ST.P.get ws j).

  op mpc_simulator i x ws cs y = 
    let viyi = W.simulator_out i (pub_input_conv x) ws cs in
    let vi = viyi.`1 in
    let yi = viyi.`2 in
    let ys = W.P.from_messages (W.P.send_messages (reconstruct_final i x yi y)) in
    IMap.imap (fun i (v:W.P.ST.view) => (v.`1,(W.P.ST.prextset v.`2.`1 (W.P.ST.rounds (pub_input_conv x)) (W.P.ST.P.get ys i),v.`2.`2))) vi.

  clone include MPC with
    theory P = WR,
    op functionality = mpc_functionality,
    op simulator = mpc_simulator,
    op gen_rand x = W.gen_rand (pub_input_conv x),
    op corrupted_t = WR.W.corrupted_t.

end MPCReveal.    
