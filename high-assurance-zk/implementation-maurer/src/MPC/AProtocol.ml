open Utils
open ECList
open ECOption
open ECCore

open ACircuit
   
module type ProtocolData = sig

  type circuit_t

  val n : Z.t
  val t : Z.t

  type pid_t
  val pid_set : pid_t list

  type pinput_t
  type sinput_t
  type input_t = pinput_t * sinput_t
  type inputs_t = (pid_t * input_t) list
  type pinputs_t = (pid_t * pinput_t) list
  type sinputs_t = (pid_t * sinput_t) list
                   
  type output_t
  type outputs_t = (pid_t * output_t) list

  type rand_t
  type rands_t = (pid_t * rand_t) list

  type in_messages_t

  type poutput_t
  type poutputs_t = (pid_t * poutput_t) list

  type trace_t = poutputs_t * in_messages_t
  type traces_t = (pid_t * trace_t) list
                                  
  type view_t = input_t * (rand_t * trace_t)
  type views_t = (pid_t * view_t) list

  val local_output : circuit_t -> pid_t -> view_t -> output_t

  val protocol : circuit_t -> rands_t -> inputs_t -> traces_t * outputs_t

  val view_to_string : view_t -> string

  val consistent_views : circuit_t -> view_t -> view_t -> pid_t -> pid_t -> bool
  val consistent_views_public_output : circuit_t -> pinput_t -> view_t -> view_t -> pid_t -> pid_t -> bool
  
end

module Protocol (PD : ProtocolData) = struct
    
  let n : Z.t = PD.n
  let t : Z.t = PD.t
  type pid_t = PD.pid_t
  let pid_set = PD.pid_set

  type circuit_t = PD.circuit_t

  type pinput_t = PD.pinput_t
  type sinput_t = PD.sinput_t
  type input_t = PD.input_t
  type inputs_t = PD.inputs_t
  type pinputs_t = PD.pinputs_t
  type sinputs_t = PD.sinputs_t

  let input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid)
  let pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs)
  let sinput (pid : pid_t) (xs : inputs_t) : sinput_t = snd (input pid xs)

  let mk_inputs (xp : pinput_t) (sx : (pid_t * sinput_t) list) = map (fun pid -> (pid, (xp, oget (assoc sx pid)))) pid_set

  let pinputs (xs : inputs_t) : pinputs_t = map (fun pid -> (pid, fst (oget (assoc xs pid)))) pid_set
  let sinputs (xs : inputs_t) : sinputs_t = map (fun pid -> (pid, snd (oget (assoc xs pid)))) pid_set

  type output_t = PD.output_t
  type outputs_t = PD.outputs_t
  let output (pid : pid_t) (xs : outputs_t) : output_t = oget (assoc xs pid)

  type rand_t = PD.rand_t
  type rands_t = PD.rands_t
  let rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid)

  type in_messages_t = PD.in_messages_t

  type poutput_t = PD.poutput_t
  type poutputs_t = PD.poutputs_t
  let poutput (pid : pid_t) (pouts : poutputs_t) : poutput_t = oget (assoc pouts pid)

  type trace_t = PD.trace_t
  type traces_t = PD.traces_t
  let trace (pid : pid_t) (trs : traces_t) : trace_t = oget (assoc trs pid)

  type view_t = PD.view_t
  type views_t = PD.views_t
  let view (pid : pid_t) (vs : views_t) : view_t = oget (assoc vs pid)
               
  let local_output = PD.local_output

  let protocol = PD.protocol

  let view_to_string = PD.view_to_string

  let consistent_views = PD.consistent_views
  let consistent_views_public_output = PD.consistent_views_public_output

  let consistent_views_public (c : circuit_t) xp (vi : view_t) (vj : view_t) (i : pid_t) (j : pid_t) : bool =
    let (xi, (ri, ti)) = vi in
    let (xj, (rj, tj)) = vj in
    fst xi = xp && fst xj = xp && consistent_views c vi vj i j

  let extract_inputs (xs : inputs_t) (pids : pid_t list) : inputs_t =
    map (fun pid -> (pid, input pid xs)) pids
  let extract_rands (rs : rands_t) (pids : pid_t list) : rand_t list =
    map (fun pid -> rand pid rs) pids
  let extract_traces (tr : traces_t) (pids : pid_t list) : trace_t list =
    map (fun pid -> trace pid tr) pids

  (*let consistent_views (c : circuit_t) (xp : pinput_t) (vi : view_t) (vj : view_t) (i : pid_t) (j : pid_t) =
    let (xi, ri, ti) = vi in
    let (xj, rj, tj) = vj in
    let outj = out_messages c j vj in
    fst xi = xp && fst xj = xp && valid_circuit_trace c (snd ti) && valid_circuit_trace c (snd tj) &&
    (fst xi = fst xj && fst xi = xp) && 
    get_messages_from j (snd ti) = get_messages_to i (out_messages c j vj) &&
    get_messages_from i (snd tj) = get_messages_to j (out_messages c i vi)*)
               
end
