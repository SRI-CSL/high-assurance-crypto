open PrimeField

open AGate
open Shamir

module RefreshGateData (PC : PartyConfiguration) = struct

  module S = Shamir(PC)

  val n : int = PC.n
  val t : int = PC.t
    
  type pid_t = PC.pid_t
  val pid_set : pid_t list = PC.pid_set

  type pinput_t = unit
  type sinput_t = S.share_t
  
  type output_t = S.secret_t

  type rand_t = polynomial

  type msgs_t = t

  type poutput_t = S.share_t

  type in_messages_t = (pid_t * msgs_t) list
  type out_messages_t = (pid_t * msgs_t) list

  type trace_t = (pid_t * poutputs_t) * in_messages_t
     
  type view_t = input_t * rand_t * trace_t

  let party_exec1 (r : rand_t) (x : input_t) : (pid_t * share_t) list = HMShamir.share r fzero

  let party_exec2 (x : input_t) (ms : (pid_t * share_t) list) : output_t = fadd (fst (snd x)) (sumt (map snd ms))

  let out_messages (pid : pid_t) (v : view_t) : out_messages_t = let (x, r, tr) = v in party_exec1 r x

  let local_output (pid : pid_t) (v : view_t) : output_t = 
    let (x, r, tr) = v in 
    let (ys, ims) = tr in
    let yi = party_exec2 x (snd tr) in
    if yi = output pid ys then reconstruct ys else witness

  let gate (rs : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let p1s = map (fun pid => (pid, party_exec1 (oget (assoc rs pid)) (oget (assoc xs pid)))) pid_set in
    let ms = map (fun pid => (pid, map (fun ms => let (sender, m) = ms in (sender, get_messages_to pid m)) p1s)) pid_set in 
    let pouts = map (fun pid => (pid, party_exec2 (oget (assoc xs pid)) (oget (assoc ms pid)))) pid_set in

    let y = reconstruct pouts in
    let ys = map (fun pid => (pid, y)) pid_set in
    let tr = map (fun pid => (pid, (pouts, oget (assoc ms pid)))) pid_set in
    (tr, ys)

  let rec zs_to_string = function 
    | Nil -> ""
    | Cons (x,xs) -> Z.to_string (snd x) ^ zs_to_string xs

  let rec msgs_to_string = function
    | PInputLM (w,c) -> Z.to_string c
    | SInputLM w -> ""
    | ConstantLM (gid, c) -> Z.to_string c
    | AdditionLM (gid, tr, trl, trr) -> zs_to_string tr ^ msgs_to_string trl ^ msgs_to_string trr
    | MultiplicationLM (gid, tr, trl, trr) -> zs_to_string tr ^ msgs_to_string trl ^ msgs_to_string trr
    | SMultiplicationLM (gid, tr, trl, trr) -> zs_to_string tr ^ msgs_to_string trl ^ msgs_to_string trr

  let rec gate_local_trace_to_string = function
    | PInputLT w c -> Z.to_string c
    | SInputLT w -> ""
    | ConstantLT (gid, c) -> Z.to_string c
    | AdditionLT (gid, m, wl, wr) -> msgs_to_string m ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr
    | MultiplicationLT (gid, m, wl, wr) -> msgs_to_string m ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr
    | SMultiplicationLT (gid, m, wl, wr) -> msgs_to_string m ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr

  let rec gate_local_traces_to_string = function
    | Nil -> ""
    | Cons (x,xs) -> gate_local_trace_to_string x ^ gate_local_traces_to_string xs
                                             
  let input_to_string (x : input_t) : string = Z.to_string (fst (snd x))

  let rand_to_string (r : rand_t) : string = polynomial_to_string r

  let trace_to_string (tr : trace_t) : string =
    let (ys, ims) = tr in zs_to_string ys ^ gate_local_traces_to_string tr

  let view_to_string (v : view_t) : string =
    let (x, r, tr) = v in
    input_to_string x ^ rand_to_string r ^ trace_to_string tr

end

module RefreshGate (PC : PartyConfiguration) = Gate (RefreshGateData (PC))
