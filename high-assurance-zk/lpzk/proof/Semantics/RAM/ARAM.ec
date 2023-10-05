(**
  Definition of the *RAM* execution model. In *RAM*, a machine keeps some local state state and 
  has read/write access to some memory tape. The computation is defined using a function **step**,
  which has the following syntax:

    (state', L') = step (L, state, x)

  Specifically, **step** takes a description of the machine (program) **L**, the current state and
  the inputs **x** and outputs a new state and advances with the program evaluation, also
  producing a new machine description.

  We model the RAM execution model by means of EasyCrypt modules, which are constructions where
  one can specify a state. We view RAM as *semantics* that evaluates programs written in a
  language via **step** and include two special procedures:
    - **setInput** - provides input to the program being evaluated
    - **getOutput** - collects output after the program is evaluated

  Our model was motivated by the definition of *program-based secure computation* framework, that
  could be used to capture program evaluation and also its security. Our framework considers
  two entities: an environment Z and an adversary A, that collude while in teracting with the 
  system. Both entities have access to the RAM interface, but they are only allowed to perform
  specific tasks. Concretely, the environment is responsible to provide the inputs to the 
  evaluation and to collect outputs a the end of it. To progress the program, Z *activates* the
  adversary A, that is able to invoke the **step** procedure. Performing **step** can *leak*
  some information as a side-effect, which is captured by the **execution_info_t** type. When the
  adversary is done advancing the program, the control shifts back to the environment, who then
  can decide to collect outputs (if they exist) or give the control back to the adversary, so
  that it can keep advancing with the program execution.
*)
require import AllCore List.

from Semantics require import ALanguage.

theory RAM.

  (** Cloning an abstract language. **RAM** will then define how programs in this language can 
      be evaluated following a RAM model *)
  clone import Language.

  (** Information that can be revealed as the program evaluation progresses *)
  type execution_info_t.

  (** RAM interface. Discloses 4 procedures:
        - init - initializes the state for the executio of program P
        - step - advances the execution of program P, one instruction at a time
        - setInput - provides inputs to the program evaluation
        - getOutput - collects outputs when the evaluation is completed

      Note that we include the *option* tag to the output type of **step** and **getOutput**,
      since it may be the case where the program execution does not leak any information and also
      it may be the case where there are no outputs to be collected (for example, when the program
      has not reached its end) *)
  module type RAM = {
    proc init(P : L) : unit
    proc step() : execution_info_t option
    proc setInput(x : input_t) : bool
    proc getOutput() : output_t option
  }.

  (** Interface used by the environment to interact with the RAM semantics *)
  module type EnvSemInterface = {
    proc setInput(x : input_t) : bool
    proc getOutput(): output_t option
    proc activate(): execution_info_t option
  }.

  (** Output event type. This type does not represent the type of the outputs per se. Instead, its
      goal is to represent that the computation has finished *)
  type output_event_t.

  (** Enviornment type. Following a cryptographic-based approach, the environment has oracle
      access to its RAM semantics interface, meaning that it can make a polynomial number of 
      queries to the RAM semantics *)
  module type Environment (ESI: EnvSemInterface) = {
    proc animate(): output_event_t 
  }.

  (** Interface used by the adversary to interact with the RAM semantics *)
  module type AdvSemInterface = {
    proc step(): execution_info_t option
  }.

  (** Adversary type. Following a cryptographic-based approach, the adversary has oracle
      access to its RAM semantics interface, meaning that it can make a polynomial number of 
      queries to the RAM semantics *)
  module type Adversary (ASI : AdvSemInterface) = {
    proc step() : execution_info_t option
  }.

  (** Concrete realization of the environment RAM interface, which defines the execution of a
      program. The **EnvironmentSemanticsInterface** module is parameterized by a RAM semantics
      and an adversary, and its behavior is formalized as follows:
        - to provide inputs to the evaluation, invokes the corresponding **setInput** method
          disclosed by the RAM semantics
        - to collect outputs from the evaluation, invokes the corresponding **getOutput** method
          disclosed by the RAM semantics 
        - to evaluate the program, invokes the **step** adversary interface *)
  module EnvironmentSemanticsInterface (Sem : RAM) (A : Adversary) = {
    proc init = Sem.init
    proc setInput(x : input_t): bool = {
      var r;
      r <@ Sem.setInput(x);
      return r;
    }
    proc getOutput(): output_t option = {
      var r;
      r <@ Sem.getOutput();
      return r;
    }
    proc activate(): execution_info_t option = {
      var r;
      r <@ A(Sem).step();
      return r;
    }
  }.

  (** Program evaluation module, that evaluates program **P** according to the RAM semantics 
      **Sem**. The **Eval** module starts by initializing the program execution and then invokes
      the enviroment/adversary interface described above to evaluate it. If the evaluation is
      successful, it will return an output event, that constitutes its output. *)
  module Eval(Sem : RAM, Z : Environment, A : Adversary) = {
    proc eval(P : L) = {
      var b;

      EnvironmentSemanticsInterface(Sem,A).init(P);
      b <@ Z(EnvironmentSemanticsInterface(Sem,A)).animate();

      return (b);
    }
  }.

end RAM.
