open AZKProtocol

module type SigmaProtocolData = sig

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

  type commitment_t
  type challenge_t
  type response_t

  type prover_state_t
  type verifier_state_t

  val commitment : prover_rand_t -> prover_input_t -> prover_state_t * commitment_t
  val challenge : verifier_rand_t -> verifier_input_t -> commitment_t -> verifier_state_t * challenge_t
  val response : prover_state_t -> challenge_t -> response_t
  val check : verifier_state_t -> response_t -> bool

  type trace_t = commitment_t * challenge_t * response_t

end

module ZKSigmaProtocolData (SPData : SigmaProtocolData) = struct

  type witness_t = SPData.witness_t
  type instance_t = SPData.instance_t
  let relation = SPData.relation

  type prover_input_t = witness_t * instance_t
  type verifier_input_t = instance_t
  type inputs_t = prover_input_t * verifier_input_t

  type prover_rand_t = SPData.prover_rand_t
  type verifier_rand_t = SPData.verifier_rand_t
  type rands_t = prover_rand_t * verifier_rand_t

  type prover_output_t = unit
  type verifier_output_t = bool
  type outputs_t = prover_output_t * verifier_output_t

  type trace_t = SPData.trace_t

  let protocol (r : rands_t) (x : inputs_t) : trace_t * outputs_t =
    let (r_p, r_v) = r in
    let (x_p, x_v) = x in
    let (stp,c) = SPData.commitment r_p x_p in
    let (stv,ch) = SPData.challenge r_v x_v c in
    let r = SPData.response stp ch in
    let b = SPData.check stv r in
    ((c, ch, r), ((),b))

end

module ZKSigmaProtocol (SPData : SigmaProtocolData) = ZKProtocol (ZKSigmaProtocolData (SPData))