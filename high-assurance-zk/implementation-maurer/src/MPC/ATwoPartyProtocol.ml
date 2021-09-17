module type TwoPartyProtocolData = sig

  type pid_t

  type input1_t
  type input2_t
  type inputs_t = input1_t * input2_t

  type rand1_t
  type rand2_t
  type rands_t = rand1_t * rand2_t

  type output1_t
  type output2_t
  type outputs_t = output1_t * output2_t

  type trace_t

  val protocol : rands_t -> inputs_t -> trace_t * outputs_t

end

module TwoPartyProtocol (PDATA : TwoPartyProtocolData) = struct

  type pid_t = PDATA.pid_t

  type input1_t = PDATA.input1_t
  type input2_t = PDATA.input2_t
  type inputs_t = PDATA.inputs_t

  type rand1_t = PDATA.rand1_t
  type rand2_t = PDATA.rand2_t
  type rands_t = PDATA.rands_t

  type output1_t = PDATA.output1_t
  type output2_t = PDATA.output2_t
  type outputs_t = PDATA.outputs_t

  type trace_t = PDATA.trace_t

  let protocol = PDATA.protocol

end
