from General require import Utils.

from MPC require import ATwoPartyProtocol.
from ZeroKnowledge require import AZKFunctionality.

theory ZKPProtocol.

  type pid_t = pid_zk_t.

  clone import ZKFunctionality.

  type prover_input_t = witness_t * statement_t.
  type verifier_input_t = statement_t.
  type inputs_t = prover_input_t * verifier_input_t.
  op valid_inputs (x : inputs_t) : bool = valid_inputs x.

  type prover_rand_t.
  type verifier_rand_t.
  type rands_t = prover_rand_t * verifier_rand_t.

  op valid_rand_prover : prover_rand_t -> prover_input_t -> bool.
  op valid_rand_verifier : verifier_rand_t -> verifier_input_t -> bool.
  op valid_rands (r : rands_t) (x : inputs_t) : bool =
    let (rp,rv) = r in
    let (xp,xv) = x in
    valid_rand_prover rp xp /\ valid_rand_verifier rv xv.

  type prover_output_t = unit.
  type verifier_output_t = bool.
  type outputs_t = prover_output_t * verifier_output_t.

  type trace_t.

  op accepting_conversation : statement_t -> trace_t -> bool.

  op protocol : rands_t -> inputs_t -> trace_t * outputs_t.

  axiom correct (r : rands_t) (x : inputs_t) :
    valid_inputs x =>
    valid_rands r x =>
    snd (protocol r x) = ZKFunctionality.f x.

  type prover_leakage_t.
  type verifier_leakage_t.
  type leakage_t = prover_leakage_t * verifier_leakage_t.

  op prover_phi : prover_input_t -> prover_leakage_t.
  op verifier_phi : verifier_input_t -> verifier_leakage_t.

  clone import TwoPartyProtocol with

    type pid_t = pid_t,

    type input1_t = prover_input_t,
    type input2_t = verifier_input_t,
    op valid_inputs = valid_inputs,

    type rand1_t = prover_rand_t,
    type rand2_t = verifier_rand_t,
    op valid_rands = valid_rands,

    type output1_t = prover_output_t,
    type output2_t = verifier_output_t,

    op Functionality.f x = ZKFunctionality.f x,

    type trace_t = trace_t,

    op protocol = protocol,

    type leakage1_t = prover_leakage_t,
    type leakage2_t = verifier_leakage_t,

    op phi1 = prover_phi,
    op phi2 = verifier_phi
  proof *.
  realize correct by move => r x *; rewrite /protocol (correct r x) //.

end ZKPProtocol.
