module type ZKProtocolData = sig

  type witness_t
  type instance_t
  val relation : witness_t -> instance_t -> bool

  type prover_input_t = witness_t * instance_t
  type verifier_input_t = instance_t
  type inputs_t = prover_input_t * verifier_input_t

  type prover_rand_t
  type verifier_rand_t
  type rands_t = prover_rand_t * verifier_rand_t

  type prover_output_t = unit
  type verifier_output_t = bool
  type outputs_t = prover_output_t * verifier_output_t

  type trace_t

  val protocol : rands_t -> inputs_t -> trace_t * outputs_t

end

module ZKProtocol (ZKD : ZKProtocolData) = struct

  type witness_t = ZKD.witness_t
  type instance_t = ZKD.instance_t
  let relation = ZKD.relation

  type prover_input_t = ZKD.prover_input_t
  type verifier_input_t = ZKD.verifier_input_t
  type inputs_t = ZKD.inputs_t

  type prover_rand_t = ZKD.prover_rand_t
  type verifier_rand_t = ZKD.verifier_rand_t
  type rands_t = ZKD.rands_t

  type prover_output_t = ZKD.prover_output_t
  type verifier_output_t = ZKD.verifier_output_t
  type outputs_t = ZKD.outputs_t

  type trace_t = ZKD.trace_t

  let protocol = ZKD.protocol

end