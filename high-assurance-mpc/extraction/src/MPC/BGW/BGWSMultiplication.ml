open PrimeField
open Core
open Option

open SMultiplicationGate

module BGWSMultiplicationData = struct

  type input_t = t
  type inputs_t = (input_t * input_t * input_t * input_t * input_t) * 
                  (input_t * input_t * input_t * input_t * input_t)

  type rand_t = unit
  type rands_t = rand_t * rand_t * rand_t * rand_t * rand_t

  type output_t = t
  type outputs_t = output_t * output_t * output_t * output_t * output_t

  type message_t = t
  type messages_tuple_t = message_t * message_t * message_t * message_t * message_t

  type out_messages_t = messages_tuple_t
  type in_messages_t = messages_tuple_t

  type trace_t = in_messages_t
  type traces_t = trace_t * trace_t * trace_t * trace_t * trace_t

  let party_exec (r : rand_t) (x : input_t * input_t) : output_t = let (x1,x2) = x in fmul x1 x2
  let empty_trace : trace_t = (witness, witness, witness, witness, witness)

  let eval_gate (r : rands_t) (x : inputs_t) : traces_t * outputs_t = 
    let (r1,r2,r3,r4,r5) = r in
    let (x1,x2) = x in
    let (x11,x12,x13,x14,x15) = x1 in
    let (x21,x22,x23,x24,x25) = x2 in
    let y1 = party_exec r1 (x11,x21) in
    let y2 = party_exec r2 (x12,x22) in
    let y3 = party_exec r3 (x13,x23) in
    let y4 = party_exec r4 (x14,x24) in
    let y5 = party_exec r5 (x15,x25) in
    let tr1 = empty_trace in
    let tr2 = empty_trace in
    let tr3 = empty_trace in
    let tr4 = empty_trace in
    let tr5 = empty_trace in

    ((tr1,tr2,tr3,tr4,tr5), (y1,y2,y3,y4,y5))

  let local_party_exec (x : input_t * input_t) (r : rand_t) (tr : trace_t) : output_t = let (x1,x2) = x in fmul x1 x2
  let out_messages (x : input_t * input_t) (r : rand_t) (tr : trace_t) : out_messages_t = empty_trace
  
  type leakage_t = unit
  type leakages_t = leakage_t * leakage_t * leakage_t * leakage_t * leakage_t

  let party_phi (x : input_t * input_t) : leakage_t = ()

  type view_t = (input_t * input_t) * rand_t * trace_t

  let message_to_string (m : message_t) = if m = witness then "" else Z.to_string m

end

module BGWSMultiplicationGate = SMultiplicationGate (BGWSMultiplicationData)
