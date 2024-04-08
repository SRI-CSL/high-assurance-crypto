(**
  Formalization of the optimized array-based LPZK verifier on top of the RAM model. Briefly, this 
  file implements the LPZK optimized verifier as a RAM machine, following the RAM formalization 
  given in file *ARAM.ec*. 

  The inputs of the RAM verifier are the statement and the required randomness to compute
  the [f] structure. Then, the RAM verifier uses *step* to produce the [f] structure and the 
  final decision is given when [get_output] is invoked.
*)
from Semantics require import ALanguage.
from RAM require import ARAM FunctionalRAM.
from Zarith require import PrimeField.
from LPZK require import LPZK LPZKEfficient.

import LPZK.
import ArithmeticCircuit.
import Circuit.
import LPZKEfficient.

theory RAMVerifier.

  (** We first import the optimized LPZK definitions, already proven secure *)
  import LPZKEfficient.

  (** We define the language that is going to be used in the RAM version of the LPZK verifier: 
      descriptions are provided as arithmetic circuits, with the instance constituting the public
      inputs and the randomness constituting the secret inputs. The output type is set to be 
      a boolean, indicating if the verifier accepts the proof or not *)
  clone import Language with
    type L = circuit_t * commitment_t,
    type public_t = instance_t,
    type secret_t = verifier_rand_t,
    type input_t = secret_t * public_t,
    type output_t = bool.

  (** The information revealed by the RAM machine is the [f] structure *)
  type execution_info_t = bool * LPZKEfficient.f_t.

  (** The state of the RAM machine will be comprised of the circuit being evaluated, the verifier
      input and randomness, and the [f] structure as the final output of the RAM machine *)
  type state_t = { circ : L option ; r : verifier_rand_t option ; 
                   inst : instance_t option ; zo : execution_info_t option }.

  (** The empty state is a state where none of the elements has yet been defined *)
  op empty_state : state_t = {| circ = None ; r = None ; inst = None ; zo = None |}.

  (** A state is initialized by being given a circuit to be evaluated by the RAM machine *)
  op init_state (P : L) : state_t = {| circ = Some P ; r = None ; inst = None ; zo = None |}.

  (** A state is initialized by being given a circuit to be evaluated by the RAM machine *)
  op set_input (st : state_t) (x : input_t) : state_t = 
    let (r, inst) = x in
    {| circ = st.`circ ; r = Some r ; inst = Some inst ; zo = st.`zo |}.

  (** The state has input if the statement and randomness have been initialized *)
  op has_input (st : state_t) : bool = st.`r <> None /\ st.`inst <> None.
  (** The state has output if the [f] structure has been computed *)
  op has_output (st : state_t) : bool = st.`zo <> None.

  (** Invokes the optimized [gen_f] function, that checks for commitment consistency at the same
      time it computes [f] *)
  op step_exec (circ : circuit_t) (r : verifier_rand_t) (x : instance_t) (c : commitment_t) =
    let (z, z') = c in
    LPZKEfficient.gen_f r circ.`gates z.

  (** Step procedure, that executes the [gen_f] function given by the LPZK specification *)
  op step (st : state_t) : state_t * execution_info_t option = 
    if has_input st then
      let (circ, c) = oget (st.`circ) in
      let zc = step_exec circ (oget st.`r) (oget st.`inst) c in
      ({| circ = st.`circ ; r = st.`r ; inst = st.`inst ; zo = Some zc |}, Some zc)
    else (st, None).

  (** Gets the input from the state, if input has been previously given *)
  op get_input (st : state_t) : input_t option = 
    if st.`r <> None /\ st.`inst <> None then
      Some (oget st.`r, oget st.`inst)
    else None.
    
  (** Gets the output from the state, if output has been previously computed *)
  op get_output (st : state_t) : output_t option = 
    if st.`zo <> None then
      let c = snd (oget st.`circ) in
      let (z, z') = c in
      let n = z' in
      let (b, f) = oget st.`zo in

      Some (if n <> fzero /\ b then LPZK.get_e f = fmul n (oget st.`r).`alpha else false)
    else None.

  (** The state has a circuit if it has been previously initialized *)
  op has_circuit (st : state_t) : bool = st.`circ <> None.

  (** Gets the circuit from the state, if circuit has been previously given *)
  op get_circuit (st : state_t) : L option = st.`circ.

  (** Output event type. This type does not represent the type of the outputs per se. Instead, its
      goal is to represent that the computation has finished *)
  type output_event_t.

  (** Instantiation of the functional RAM syntax with the concrete LPZK verifier types and 
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

  (** Concrete verifier in the RAM model *)
  module RAMVerifier (Z : RAM.Environment) (A : RAM.Adversary) = RAM.Eval(FRAM, Z, A).

end RAMVerifier.
