require import Int Distr Real.

from General require import Utils.
from ZeroKnowledge require import AZKPProtocol AZKFunctionality.

theory SigmaProtocol.

  clone import ZKFunctionality.

  type pid_t = pid_zk_t.

  type commitment_t.
  type challenge_t.
  type response_t.

  op challenge_distr : challenge_t distr.
  axiom challenge_distr_ll : is_lossless challenge_distr.

  type prover_input_t = witness_t * statement_t.
  type verifier_input_t = statement_t.
  type inputs_t = prover_input_t * verifier_input_t.
  op valid_inputs : inputs_t -> bool.

  type prover_output_t = unit.
  type verifier_output_t = bool.
  type outputs_t = prover_output_t * verifier_output_t.

  type prover_rand_t.
  type verifier_rand_t = challenge_t.
  op valid_rand_prover : prover_rand_t -> prover_input_t -> bool.
  op valid_rand_verifier : verifier_rand_t -> verifier_input_t -> bool.
  type rands_t = prover_rand_t * verifier_rand_t.
  op valid_rands (r : rands_t) (x : inputs_t) : bool =
    let (rp,rv) = r in
    let (xp,xv) = x in
    valid_rand_prover rp xp /\ valid_rand_verifier rv xv.

  type trace_t = commitment_t * challenge_t * response_t.

  type prover_state_t.
  type verifier_state_t.

  op commitment : prover_rand_t -> prover_input_t -> prover_state_t * commitment_t.
  op challenge : verifier_rand_t -> verifier_input_t -> commitment_t -> verifier_state_t * challenge_t.
  op response : prover_state_t -> challenge_t -> response_t.
  op check : verifier_state_t -> response_t -> bool.

  op protocol (r : rands_t) (x : inputs_t) : trace_t * outputs_t = 
    let (r_p, r_v) = r in
    let (x_p, x_v) = x in
    let (stp,c) = commitment r_p x_p in
    let (stv,ch) = challenge r_v x_v c in
    let r = response stp ch in
    let b = check stv r in
    ((c, ch, r), ((),b)).

  op accepting_conversation : statement_t -> trace_t -> bool.

  type prover_leakage_t.
  type verifier_leakage_t.
  type leakage_t = prover_leakage_t * verifier_leakage_t.

  op prover_phi : prover_input_t -> prover_leakage_t.
  op verifier_phi : verifier_input_t -> verifier_leakage_t.

  clone import ZKPProtocol with 
    type ZKFunctionality.witness_t = witness_t,
    type ZKFunctionality.statement_t = statement_t,
    op ZKFunctionality.relation = relation,
    op ZKFunctionality.valid_statement = valid_statement,
    op ZKFunctionality.valid_inputs = valid_inputs,

    op valid_inputs = valid_inputs,
  
    type prover_rand_t = prover_rand_t,
    type verifier_rand_t = verifier_rand_t,
    op valid_rand_prover = valid_rand_prover,
    op valid_rand_verifier = valid_rand_verifier,

    op valid_rands = valid_rands,

    type trace_t = trace_t,
    op accepting_conversation = accepting_conversation,

    op protocol = protocol,

    type prover_leakage_t = prover_leakage_t,
    type verifier_leakage_t = verifier_leakage_t,

    op prover_phi = prover_phi,
    op verifier_phi = verifier_phi.

end SigmaProtocol.
