(**
  RAM definition, with the RAM interface defined in the *ARAM.ec* file being defined by functional
  operators. Briefly, for every procedure disclosed by RAM, we define a functional operator and
  then realize the RAM interface using those functional operators. Having a functional definiton
  of the RAM model allows us to use the EasyCrypt to OCaml extraction tool, unlocking the
  possibility of extracting concrete implementations defined in the RAM model.

  The behavior of each operator is axiomatized, which means such axioms need to be proven for
  all instantiations of the RAM functional model. In a way, the functional RAM model was tailored
  to work with our parallelism framework and, therefore, the axiomatize behavior that we define
  here may be to strict for other use-cases. A more generic and simple functional RAM definition 
  can be done, but that would just shift the complexity to the RAM module interface. Moreover,
  the function RAM formalization doesn't model an iterative program evaluation. Instead, we assume
  that, after the RAM state has been initialized with a program and an input, performing a single
  **step** would result in the evaluation of the entire program and, therefore, would be possible
  to collect outputs right after.
*)
require import AllCore List.

from Semantics require import ALanguage.
from RAM require import ARAM.

theory FunctionalRAM.

  (** Cloning an abstract language *)
  clone import Language.

  (** The state that is maintained by the RAM machine *)
  type state_t.

  (** Information that can be revealed as the program evaluation progresses *)
  type execution_info_t.
  (** Output event type. This type does not represent the type of the outputs per se. Instead, its
      goal is to represent that the computation has finished *)
  type output_event_t.

  (** Importing the RAM model, with the concrete data types and language defined above *)
  clone import RAM with
    theory Language = Language,
    type execution_info_t = execution_info_t,
    type output_event_t = output_event_t.

  (** The empty state, which will be starting point of the RAM machine *)
  op empty_state : state_t.
  (** State initialization. The state is initialized with the program that is going to be 
      evaluated *)
  op init_state : L -> state_t.
  (** Provides input to the evaluation, that is stored in the state *)
  op set_input : state_t -> input_t -> state_t.
  (** Consumes one instruction of the program, producing a new state and potentially some 
      execution leakage *)
  op step : state_t -> state_t * execution_info_t option.
  (** Extracts the input from the state (if any) *)
  op get_input : state_t -> input_t option.  
  (** Generates the output from the state *)
  op get_output : state_t -> output_t option.  

  (** Checks if input has already been provided to the evaluation *)
  op has_input : state_t -> bool.
  (** Checks if output is ready to be collected (the evaluation has finished) *)
  op has_output : state_t -> bool.
  
  (** Checks if the state has been initialized with a concrete program *)
  op has_circuit : state_t -> bool.
  (** Extracts the program from the state (if any) *)
  op get_circuit : state_t -> L option.

  (** Axiomatization of the behavior of the operators above *)

  (** Establishes that the **empty_state** doesn't have input *)
  axiom has_input_empty_state : !has_input empty_state.
  (** Establishes that the **empty_state** doesn't have a program *)
  axiom has_circuit_empty_state : !has_circuit empty_state.
  (** Establishes that the **empty_state** doesn't have output *)
  axiom has_output_empty_state : !has_output empty_state.

  (** Establishes that a state will have a circuit after initialized with **init_state** *)
  axiom has_circuit_init_state (L : L) : has_circuit (init_state L).
  (** Establishes that if a state has a circuit, then the **get_circuit** operation must produce
      an output *)
  axiom has_circuit_get_circuit (st : state_t) : has_circuit st => get_circuit st <> None.
  (** Establishes that if a state doesn't have a circuit, then the **get_circuit** operation must
      not produce an output *)
  axiom has_circuit_get_circuitN (st : state_t) : !has_circuit st => get_circuit st = None.
  (** Establishes the behavior of the **init_state** operator *)
  axiom get_circuit_has_circuitN (L : L) : get_circuit (init_state L) = Some L.

  (** Establishes that providing input to the state doesn't modify the program being evaluated *)
  axiom get_circuit_set_input (st : state_t) x : get_circuit (set_input st x) = get_circuit st.
  (** Establishes that performing a **step** doesn't modify the program being evaluated *)
  axiom get_circuit_step (st : state_t) : get_circuit (step st).`1 = get_circuit st.

  (** Establishes that if a state has input, then the **get_input** operation must produce
      an output *)
  axiom has_input_get_input (st : state_t) : has_input st => get_input st <> None.
  (** Establishes that if a state doesn't have a input, then the **get_input** operation must
      not produce an output *)
  axiom has_input_get_inputN (st : state_t) : !has_input st => get_input st = None.

  (** Establishes that a state has input after it has been provided by **set_input** *)
  axiom has_input_set_input (st : state_t) x : has_input (set_input st x).

  (** Establishes the behavior of the **set_input** operator *)
  axiom get_input_set_input (st : state_t) x : get_input (set_input st x) = Some x.

  (** Establishes that performing a **step** doesn't modify the input *)
  axiom has_input_step (st : state_t) : has_input (step st).`1 = has_input st.
  (** Establishes that performing a **step** doesn't modify the input *)
  axiom get_input_step (st : state_t) : get_input (step st).`1 = get_input st.

  (** Establishes that, if the RAM state has already been initialized and given inputs, then
      performing a **step** evaluates the entire program and, therefore, the state would 
      already have outputs to be collected *)
  axiom has_output_step (st : state_t) : has_input st => has_output (step st).`1.

  (** Establishes that, if the RAM doesn't have inputs yet, then performing **step** will do
      nothing and, therefore, the state will not be modified *)
  axiom step_has_inputN (st : state_t) : !has_input st => (step st).`1 = st.
  (** Establishes that, if a **step** has already been performed, then performing a new **step**
      will do nothing and, therefore, the state will not be modified. This requirement is due to
      the fact that we are not modelling the iterative execution of a program *)
  axiom step_step (st : state_t) : step (step st).`1 = step st.

  (** Establishes that providing input to the state does not modify the existence of outputs *)
  axiom has_output_set_input (st : state_t) x : has_output (set_input st x) = has_output st.

  (** Establishes that if a state has outputs, then the **get_output** operation must produce
      an output *)
  axiom has_output_get_output (st : state_t) : has_output st => get_output st <> None.
  (** Establishes that if a state doesn't have outputs, then the **get_output** operation must
      not produce an output *)
  axiom has_output_get_outputN (st : state_t) : !has_output st => get_output st = None.

  (** Establishes that inputs cannot be overwritten, i.e., if inputs have been provided to the
      evaluation, then providing new inputs would not alter the state *)
  axiom set_input_set_input st x y : set_input (set_input st y) x = set_input st x.

  (** Establishes that the state still has no input after being initialized with a program *)
  axiom has_input_init_state L : !has_input (init_state L).
  (** Establishes that the state still has no output after being initialized with a program *)
  axiom has_output_init_state L : !has_output (init_state L).

  (** Instantiation of the **RAM** interface from file *ARAM.ec* with the functional operators 
      above *)
  module FRAM = {
    var st : state_t

    proc init(P : L) : unit = {
      st <- init_state P;
    }

    proc step() : execution_info_t option = {
      var r;

      r <- None;
      if (has_input st) {
        (st, r) <- step st;
      }

      return r;
    }

    proc setInput(x : input_t) : bool = {
      var r : bool;

      r <- false;
      if (!has_input st) {
        st <- set_input st x;
        r <- true;
      }

      return r;
    }

    proc getOutput() : output_t option = {
      var r;
      
      r <- None;
      if (has_output st) {
        r <- get_output st;
      }

      return r;
    }
  }.

end FunctionalRAM.
