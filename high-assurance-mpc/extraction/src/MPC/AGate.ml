open Utils
open ECList
   
module type GateData = sig

  type input_t
  type inputs_t = (input_t * input_t * input_t * input_t * input_t) * 
                  (input_t * input_t * input_t * input_t * input_t)

  type rand_t
  type rands_t = rand_t * rand_t * rand_t * rand_t * rand_t

  type output_t
  type outputs_t = output_t * output_t * output_t * output_t * output_t

  type message_t
  type messages_tuple_t = message_t * message_t * message_t * message_t * message_t

  type out_messages_t = messages_tuple_t
  type in_messages_t = messages_tuple_t

  type trace_t = in_messages_t
  type traces_t = trace_t * trace_t * trace_t * trace_t * trace_t

  val eval_gate : rands_t -> inputs_t -> traces_t * outputs_t
  val local_party_exec : input_t * input_t -> rand_t -> trace_t -> output_t
  val out_messages : input_t * input_t -> rand_t -> trace_t -> out_messages_t
  
  type leakage_t
  type leakages_t = leakage_t * leakage_t * leakage_t * leakage_t * leakage_t

  val party_phi : input_t * input_t -> leakage_t

  type view_t = (input_t * input_t) * rand_t * trace_t

  val message_to_string : message_t -> string

end

module Gate (GD : GateData) = struct

  type pid_t = pid_mpc_t

  type input_t = GD.input_t
  type inputs_t = GD.inputs_t
  let get_party_input (pid : pid_t) (x : inputs_t) : input_t * input_t =
    match pid with
      | P1 -> let (x,y) = x in let (x1,x2,x3,x4,x5) = x in let (y1,y2,y3,y4,y5) = y in (x1,y1)
      | P2 -> let (x,y) = x in let (x1,x2,x3,x4,x5) = x in let (y1,y2,y3,y4,y5) = y in (x2,y2)
      | P3 -> let (x,y) = x in let (x1,x2,x3,x4,x5) = x in let (y1,y2,y3,y4,y5) = y in (x3,y3)
      | P4 -> let (x,y) = x in let (x1,x2,x3,x4,x5) = x in let (y1,y2,y3,y4,y5) = y in (x4,y4)
      | P5 -> let (x,y) = x in let (x1,x2,x3,x4,x5) = x in let (y1,y2,y3,y4,y5) = y in (x5,y5)

  type rand_t = GD.rand_t
  type rands_t = GD.rands_t
  (*let valid_rands = GD.valid_rands*)
  let get_party_rand (pid : pid_t) (x : rands_t) : rand_t =
    match pid with
      | P1 -> let (x1,x2,x3,x4,x5) = x in x1
      | P2 -> let (x1,x2,x3,x4,x5) = x in x2
      | P3 -> let (x1,x2,x3,x4,x5) = x in x3
      | P4 -> let (x1,x2,x3,x4,x5) = x in x4
      | P5 -> let (x1,x2,x3,x4,x5) = x in x5

  type output_t = GD.output_t
  type outputs_t = GD.outputs_t
  let get_party_output (pid : pid_t) (x : outputs_t) : output_t =
    match pid with
      | P1 -> let (x1,x2,x3,x4,x5) = x in x1
      | P2 -> let (x1,x2,x3,x4,x5) = x in x2
      | P3 -> let (x1,x2,x3,x4,x5) = x in x3
      | P4 -> let (x1,x2,x3,x4,x5) = x in x4
      | P5 -> let (x1,x2,x3,x4,x5) = x in x5

  type message_t = GD.message_t
  type messages_tuple_t = GD.messages_tuple_t

  type out_messages_t = GD.out_messages_t
  let get_messages_to (pid : pid_t) (x : out_messages_t) : message_t =
    match pid with
      | P1 -> let (x1,x2,x3,x4,x5) = x in x1
      | P2 -> let (x1,x2,x3,x4,x5) = x in x2
      | P3 -> let (x1,x2,x3,x4,x5) = x in x3
      | P4 -> let (x1,x2,x3,x4,x5) = x in x4
      | P5 -> let (x1,x2,x3,x4,x5) = x in x5

  type in_messages_t = GD.in_messages_t
  let get_messages_from (pid : pid_t) (x : in_messages_t) : message_t =
    match pid with
      | P1 -> let (x1,x2,x3,x4,x5) = x in x1
      | P2 -> let (x1,x2,x3,x4,x5) = x in x2
      | P3 -> let (x1,x2,x3,x4,x5) = x in x3
      | P4 -> let (x1,x2,x3,x4,x5) = x in x4
      | P5 -> let (x1,x2,x3,x4,x5) = x in x5

  type trace_t = GD.trace_t
  type traces_t = GD.traces_t
  let get_party_trace (pid : pid_t) (x : traces_t) : trace_t =
    match pid with
      | P1 -> let (x1,x2,x3,x4,x5) = x in x1
      | P2 -> let (x1,x2,x3,x4,x5) = x in x2
      | P3 -> let (x1,x2,x3,x4,x5) = x in x3
      | P4 -> let (x1,x2,x3,x4,x5) = x in x4
      | P5 -> let (x1,x2,x3,x4,x5) = x in x5

  let eval_gate = GD.eval_gate
  let local_party_exec = GD.local_party_exec
  let out_messages = GD.out_messages
  
  type leakage_t = GD.leakage_t
  type leakages_t = GD.leakages_t
  let get_party_leakage (pid : pid_t) (x : leakages_t) : leakage_t =
    match pid with
      | P1 -> let (x1,x2,x3,x4,x5) = x in x1
      | P2 -> let (x1,x2,x3,x4,x5) = x in x2
      | P3 -> let (x1,x2,x3,x4,x5) = x in x3
      | P4 -> let (x1,x2,x3,x4,x5) = x in x4
      | P5 -> let (x1,x2,x3,x4,x5) = x in x5

  let party_phi = GD.party_phi
  let phi (x : inputs_t) : leakages_t = 
    let (x,y) = x in
    let (x1,x2,x3,x4,x5) = x in let (y1,y2,y3,y4,y5) = y in
    (party_phi (x1,y1), party_phi (x2,y2), party_phi (x3,y3), party_phi (x4,y4), party_phi (x5,y5))

  type view_t = (input_t * input_t) * rand_t * trace_t

end
