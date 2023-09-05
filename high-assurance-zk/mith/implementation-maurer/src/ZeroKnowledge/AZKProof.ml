open Utils

open ATwoPartyProtocol

module type ZKProofData = sig

  type witness_t
  type statement_t

  type prover_input_t = witness_t * statement_t
  type verifier_input_t = statement_t
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

module ZKProofProtocolData (ZK : ZKProofData) = struct

  type pid_t = pid_zk_t

  type input1_t = ZK.prover_input_t
  type input2_t = ZK.verifier_input_t
  type inputs_t = input1_t * input2_t

  type rand1_t = ZK.prover_rand_t
  type rand2_t = ZK.verifier_rand_t
  type rands_t = rand1_t * rand2_t

  type output1_t = ZK.prover_output_t
  type output2_t = ZK.verifier_output_t
  type outputs_t = output1_t * output2_t

  type trace_t = ZK.trace_t

  let protocol = ZK.protocol

end

module ZKProof (ZK : ZKProofData) = TwoPartyProtocol (ZKProofProtocolData(ZK))
