open PrimeField

open AGate

module type AdditionGateData = sig

  type input_t = t
  type inputs_t = (input_t * input_t * input_t * input_t * input_t) * 
                  (input_t * input_t * input_t * input_t * input_t)

  type rand_t
  type rands_t = rand_t * rand_t * rand_t * rand_t * rand_t

  type output_t = t
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

module AdditionGate (AGD : AdditionGateData) = Gate (AGD)
