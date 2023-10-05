(**
  Formalization of the list-based LPZK prover on top of the RAM model. Briefly, this file
  implements the LPZK prover as a RAM machine, following the RAM formalization given in
  file *ARAM.ec*. 

  The inputs of the RAM prover are the witness, statement and the required randomness to compute
  the commitment. Then, the RAM prover uses *step* to produce the [z] structure and the final 
  commitment message ([z] together with the field value corresponding to the [a] random value of 
  the output gate of the circuit) are constructed when [get_output] is invoked.
*)
from Semantics require import ALanguage.
from RAM require import ARAM FunctionalRAM.
from Zarith require import PrimeField.
from LPZK require import LPZK.

import LPZK.
import ArithmeticCircuit.
import Circuit.

theory RAMProver.

  (** We first import the LPZK definitions, already proven secure *)
  import LPZK.

  (** We define the language that is going to be used in the RAM version of the LPZK prover: 
      descriptions are provided as arithmetic circuits, with the instance constituting the public
      inputs and the witness and randomness constituting the secret inputs. The output type is
      set to be the commitment type *)
  clone import Language with
    type L = circuit_t,
    type public_t = instance_t,
    type secret_t = witness_t * prover_rand_t,
    type input_t = secret_t * public_t,
    type output_t = commitment_t.

  (** The information revealed by the RAM machine is the [z] structure *)
  type execution_info_t = z_t.

  (** The state of the RAM machine will be comprised of the circuit being evaluated, the prover
      input and randomness, and the [z] structure as the final output of the RAM machine *)
  type state_t = { circ : L option ; w : witness_t option ; r : prover_rand_t option ; 
                   inst : instance_t option ; zo : execution_info_t option }.

  (** The empty state is a state where none of the elements has yet been defined *)
  op empty_state : state_t = {| circ = None ; w = None ; r = None ; inst = None ; zo = None |}.

  (** A state is initialized by being given a circuit to be evaluated by the RAM machine *)
  op init_state (P : L) : state_t = {| circ = Some P ; w = None ; r = None ; inst = None ; zo = None |}.

  (** A state is initialized by being given a circuit to be evaluated by the RAM machine *)
  op set_input (st : state_t) (x : input_t) : state_t = 
    let (xs, inst) = x in let (w, r) = xs in
    {| circ = st.`circ ; w = Some w ; r = Some r ; inst = Some inst ; zo = st.`zo |}.

  (** The state has input if the witness, statement and randomness have been initialized *)
  op has_input (st : state_t) : bool = st.`w <> None /\ st.`r <> None /\ st.`inst <> None.
  (** The state has output if the [z] structure has been computed *)
  op has_output (st : state_t) : bool = st.`zo <> None.

  (** Step procedure, that executes the [gen_z] function given by the LPZK specification *)
  op step (st : state_t) : state_t * execution_info_t option = 
    if has_input st then
      let c' = add_final_mul (oget st.`circ) in
      let zc = LPZK.gen_z (oget st.`r) c'.`gates (oget st.`inst) (oget st.`w) in
      ({| circ = st.`circ ; w = st.`w ; r = st.`r ; inst = st.`inst ; zo = Some zc |}, Some zc)
    else (st, None).

  (** Gets the input from the state, if input has been previously given *)
  op get_input (st : state_t) : input_t option = 
    if st.`w <> None /\ st.`r <> None /\ st.`inst <> None then
      Some ((oget st.`w, oget st.`r), oget st.`inst)
    else None.

  (** Gets the output from the state, if output has been previously computed *)
  op get_output (st : state_t) : output_t option = 
    if st.`zo <> None then
      let z = oget st.`zo in
      let z' = (LPZK.get_a (oget st.`r) (oget st.`circ).`gates) in
      Some (z, z')
    else None.

  (** The state has a circuit if it has been previously initialized *)
  op has_circuit (st : state_t) : bool = st.`circ <> None.

  (** Gets the circuit from the state, if circuit has been previously given *)
  op get_circuit (st : state_t) : L option = st.`circ.

  (** Output event type. This type does not represent the type of the outputs per se. Instead, its
      goal is to represent that the computation has finished *)
  type output_event_t.

  (** Instantiation of the functional RAM syntax with the concrete LPZK prover types and 
      operators.

      It defines the LPZK prover as a RAM machine *)  
  clone import FunctionalRAM with
    theory Language = Language,
    type state_t = state_t,
    type execution_info_t = execution_info_t,
    type output_event_t = output_event_t,
    op empty_state = empty_state,
    op init_state = init_state,
    op set_input = set_input,
    op step = step,
    op get_input = get_input,
    op get_output = get_output,
    op get_circuit = get_circuit,
    op has_input = has_input,
    op has_output = has_output,
    op has_circuit = has_circuit
  proof * by smt().

  (** Concrete list-based prover in the RAM model *)
  module RAMProver (Z : RAM.Environment) (A : RAM.Adversary) = RAM.Eval(FRAM, Z, A).

end RAMProver.
