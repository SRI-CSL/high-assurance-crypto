require import AllCore Int List Distr Ring.
require import Aux AuxList.
require import NextMsgArray NextMsgFixedArray NextMsgISet NextMsgIMap NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgCircuit NextMsgWeakCircuit.
require import NextMsgWeak NextMsgMPC NextMsgMPCReveal.
require import NextMsgMaurer.
require import NextMsgMaurerP NextMsgMaurerAPI.

import MaurerAPI.

theory MaurerWeakAdd.

  clone include WeakGate with
    theory G = MaurerAdd,

    type secret = g_sec,
    op unshare = g_unshare,
    op functionality (wij:MaurerAdd.Gate) (ws:secret) =
      let val = add_val (oget (IMap.get ws.`2 wij.`2.`1)) (oget (IMap.get ws.`2 wij.`2.`2)) in
      (ws.`1+1,IMap.set ws.`2 ws.`1 val),
    op simulator (is:corrupted_parties) (wij:MaurerAdd.Gate) (ws:corrupted_inputs) (rs:rand) =
      let ins = IMap.ofset (fun _ => MaurerP.init (fun _ => Array.singl 0 tt)) is in
      IMap.zip (IMap.redom is ws) (IMap.zip ins (corrupted is rs)),
    op gen_rand _ = dunit (G.GT.pinit (fun _ => tt)),
    op corrupted_t = 2
    proof *.
    realize corrupted_le. rewrite /corrupted_t /parties => />. qed.

end MaurerWeakAdd.

theory MaurerWeakSMul.

  clone include WeakGate with
    theory G = MaurerSMul,
    
    type secret = g_sec,
    op unshare = g_unshare,
    op functionality (wij:MaurerSMul.Gate) (ws:secret) =
      let val = mul_val (oget (IMap.get ws.`2 wij.`2.`1)) (oget (IMap.get ws.`2 wij.`2.`2)) in
      (ws.`1+1,IMap.set ws.`2 ws.`1 val),
    op simulator = MaurerWeakAdd.simulator,
    op gen_rand _ = dunit (G.GT.pinit (fun _ => tt)),
    op corrupted_t = 2
    proof *.
    realize corrupted_le. rewrite /corrupted_t /parties => />. qed.

end MaurerWeakSMul.

theory MaurerWeakConst.

  clone include WeakGate with
    theory G = MaurerConst,
    
    type secret = g_sec,
    op unshare = g_unshare,
    op functionality (wc:MaurerConst.Gate) (ws:secret) =
      (ws.`1+1,IMap.set ws.`2 ws.`1 wc.`2),
    op simulator (is:corrupted_parties) (wc:MaurerConst.Gate) (ws:corrupted_inputs) (rs:rand) =
      let ins = IMap.ofset (fun _ => MaurerP.init (fun _ => Array.singl 0 tt)) is in
      IMap.zip (IMap.redom is ws) (IMap.zip ins (corrupted is rs)),
    op gen_rand _ = dunit (G.GT.pinit (fun _ => tt)),
    op corrupted_t = 2
    proof *.
    realize corrupted_le. rewrite /corrupted_t /parties => />. qed.

end MaurerWeakConst.

theory MaurerWeakMul.

  clone include WeakGate with
    theory G = MaurerMul,
    
    type secret = g_sec,
    op unshare = g_unshare,
    op functionality (wij:MaurerMul.Gate) (ws:secret) =
      let val = mul_val (oget (IMap.get ws.`2 wij.`2.`1)) (oget (IMap.get ws.`2 wij.`2.`2)) in
      (ws.`1+1,IMap.set ws.`2 ws.`1 val),
    op simulator (is:ISet.iset) (wij:MaurerMul.Gate) (ws:corrupted_inputs) rs =
      let outs = MaurerP.init (fun i => if ISet.mem i is
        then mul_start wij.`2.`1 wij.`2.`2 (oget (IMap.get ws i)).`1 (MaurerP.get rs i)
        else MaurerAPI.shrs_to_msgs (share zero_val (MaurerP.get rs i) )) in
      let ins = G.send_messages outs in
      let ins0 = IMap.ofset (fun i => MaurerP.init (fun j => Array.singl 0 (get_msg (MaurerP.get ins i) j))) is in
      IMap.zip (IMap.redom is ws) (IMap.zip ins0 (corrupted is rs)),
    op gen_rand (wij:MaurerMul.Gate) = dapply (MaurerP.of_list) gen_parties_rand,
    op corrupted_t = 2
    proof *.
    realize corrupted_le. rewrite /corrupted_t /parties => />. qed.

end MaurerWeakMul.

theory MaurerWeakGate.

import MaurerGate.

op gate_func (g:Gate) ws =
    with g = Add wij => MaurerWeakAdd.functionality wij ws
    with g = SMul wij => MaurerWeakSMul.functionality wij ws
    with g = Const wij => MaurerWeakConst.functionality wij ws
    with g = Mul wij => MaurerWeakMul.functionality wij ws.
op gate_sim is g ws (rs:((unit,rand) either) MaurerP.arrayN) =
    with g = Add wij =>
      let v = MaurerWeakAdd.simulator is wij ws (MaurerP.map unL rs) 
      in IMap.map (fun (v:_*(_*_)) => (v.`1,(MaurerP.map (Array.map L) v.`2.`1,L v.`2.`2))) v
    with g = SMul wij =>
      let v = MaurerWeakSMul.simulator is wij ws (MaurerP.map unL rs) 
      in IMap.map (fun (v:_*(_*_)) => (v.`1,(MaurerP.map (Array.map L) v.`2.`1,L v.`2.`2))) v
    with g = Const wij =>
      let v = MaurerWeakConst.simulator is wij ws (MaurerP.map unL rs) 
      in IMap.map (fun (v:_*(_*_)) => (v.`1,(MaurerP.map (Array.map L) v.`2.`1,L v.`2.`2))) v
    with g = Mul wij =>
      let v = MaurerWeakMul.simulator is wij ws (MaurerP.map unR rs)
      in IMap.map (fun (v:_*(_*_)) => (v.`1,(MaurerP.map (Array.map R) v.`2.`1,R v.`2.`2))) v.
op gate_rand g =
    with g = Add wij => dapply (MaurerP.map L) (MaurerWeakAdd.gen_rand wij)
    with g = SMul wij => dapply (MaurerP.map L) (MaurerWeakSMul.gen_rand wij)
    with g = Const wij => dapply (MaurerP.map L) (MaurerWeakConst.gen_rand wij)
    with g = Mul wij => dapply (MaurerP.map R) (MaurerWeakMul.gen_rand wij).
 
  clone include WeakGate with
    theory G = MaurerGate,
    
    type secret = g_sec,
    op unshare = g_unshare,
    op functionality = gate_func,
    op simulator = gate_sim,
    op gen_rand = gate_rand,
    op corrupted_t = 2
    proof *.
    realize corrupted_le. rewrite /corrupted_t /parties => />. qed.

end MaurerWeakGate.

theory MaurerWeakCircuit.

  import MaurerGate MaurerWeakGate.
  import MaurerCircuit.

  clone include WeakCircuit with
    theory WG = MaurerWeakGate,
    op B.consistent_inputs = MaurerCircuit.consistent_inputs.

end MaurerWeakCircuit.

theory MaurerWeakReveal.

  clone include WeakReveal with
    theory W = MaurerWeakCircuit,
    type pub_input = MaurerReveal.pub_input,
    op pub_input_conv = MaurerReveal.pub_input_conv,
    type final_output = MaurerReveal.final_output,
    op reveal_local_start = MaurerReveal.reveal_local_start,
    op reveal_local_end = MaurerReveal.reveal_local_end,
    op final_valid_local_messages = MaurerReveal.final_valid_local_messages,
    op final_valid_msg = MaurerReveal.final_valid_msg,
    op mpc_consistent_inputs = MaurerReveal.mpc_consistent_inputs,
    op mpc_consistent_outputs = MaurerReveal.mpc_consistent_outputs,
    op stateful_consistent_outputs = MaurerReveal.stateful_consistent_outputs.

end MaurerWeakReveal.

theory MaurerMPCReveal.

  clone include MPCReveal with
    theory WR = MaurerWeakReveal,
    op reveal_functionality (_:WR.pub_input) (ws:WR.W.public_output) : WR.final_output = oget (IMap.get ws.`2 (ws.`1-1)),
    op reconstruct_final (is) x (wis:WR.W.corrupted_outputs) o =
      let wos = IMap.map (fun (wi:MaurerAdd.share) => (get_wire_st_shr wi.`1 (get_wire_st_next wi.`1-1)) ) wis in
      let rs2 = reconstruct_shrs o wos in
      MaurerP.init (fun i => R (mk_msgs (MaurerP.create (get_shr rs2 i)) ) ).

end MaurerMPCReveal.
