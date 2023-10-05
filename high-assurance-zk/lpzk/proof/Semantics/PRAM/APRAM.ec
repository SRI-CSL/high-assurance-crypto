(**
  Definition of the *PRAM* execution model. *PRAM* can be seen as generalization of the *RAM* 
  model, where the computation can potentially branch multiple processes that have access to the 
  same memory. Similarly to *RAM*, *PRAM* can be defined via a function **step** but, instead of 
  just outputing one (state', L') tuple, it outputs multiple tuples (state', L'), each associated
  with a process identifier specifying the process to continue the computation from that state. 
  Then, each process continues by running step at each step, as above. The computation halts when
  there are no running processes. This is captured by the **parallel-step** operation bellow

    ([state'], [L']) = parallel-step ([L], [state], x)

  which runs step for all active processes. Specifically, **step** takes multiple descriptions of   the machine (program) **[L]**, the current states of all processes [state] and the inputs **x**
  and outputs a new set of states and advances with the programs evaluation, also producing a new
  set of machine descriptions.

  We model the PRAM execution model by means of EasyCrypt modules, which are constructions where
  one can specify a state. We view PRAM as *semantics* that evaluates programs written in a
  language via **stepP** and **stepS**: **stepP** models the asynchronous evaluation evaluation of
  the program, where **stepS** models its synchronous evaluation. Informally, **stepP** is used
  to capture a single core execution and **stepS** captures the scenario where all cores execute
  at the same time. We also include two special procedures:
    - **setInput** - provides input to the program being evaluated
    - **getOutput** - collects output after the program is evaluated

  Our model was motivated by the definition of *program-based secure computation* framework, that
  could be used to capture program evaluation and also its security. Our framework considers
  two entities: an environment Z and an adversary A, that collude while in teracting with the 
  system. Both entities have access to the RAM interface, but they are only allowed to perform
  specific tasks. Concretely, the environment is responsible to provide the inputs to the 
  evaluation and to collect outputs a the end of it. To progress the program, Z *activates* the
  adversary A, that is able to invoke the **stepP** or **stepS** procedures. Performing **stepS**   can *leak* some information as a side-effect, which is captured by the **execution_info_t** 
  type. When the adversary is done advancing the program, the control shifts back to the 
  environment, who then can decide to collect outputs (if they exist) or give the control back to
  the adversary, so that it can keep advancing with the program execution.
*)
require import AllCore List.

from Semantics require import ALanguage.

theory PRAM.

  (** Cloning an abstract language. **PRAM** will then define how programs in this language can 
      be evaluated following a PRAM model *)
  clone import Language.

  (** Information that can be revealed as the program evaluation progresses. This information may
      only be leaked when all cores execute at the same time (following the **stepS** procedure).
      Single core execution is not considered to have execution information leaked. *)
  type execution_info_t.

  (** ID of the processores that comprise the evaluation core *)
  type processorId_t.

  (** In a parallel execution, the original program (or circuit) is split into *smaller* 
      programs (or circuits) and each one of them is given to a core to be computed. The 
      **meta_information_t** type will store auxiliar data allows the reconstruction of the
      original program (or circuit) and also to aggregate the outputs of the parallel cores
      into a single output value *)
  type meta_information_t.

  (** Number of parallel cores *)
  op nprocesses : int.

  (** PRAM interface. Discloses 5 procedures:
        - init - initializes the state for the executio of program P
        - stepP - asynchronous program evaluation, modeling the execution of a single core
        - stepS - synchronous program evaluation, modeling the execution of all cores at the same
        time
        - setInput - provides inputs to the program evaluation
        - getOutput - collects outputs when the evaluation is completed

      Note that we include the *option* tag to the output type of **stepS** and **getOutput**,
      since it may be the case where the program execution does not leak any information and also
      it may be the case where there are no outputs to be collected (for example, when the program
      has not reached its end) *)
  module type PRAM = {
    proc init(meta : meta_information_t, Ps : L list) : unit
    proc stepP(id : processorId_t) : bool
    proc stepS() : execution_info_t option
    proc setInput(x : input_t) : bool
    proc getOutput() : output_t option
  }.

  (** Interface used by the environment to interact with the PRAM semantics *)
  module type EnvSemInterface = {
    proc setInput(x: input_t): bool
    proc getOutput(): output_t option
    proc activate(): execution_info_t option
  }.

  (** Output event type. This type does not represent the type of the outputs per se. Instead, its
      goal is to represent that the computation has finished *)
  type output_event_t.

  (** Enviornment type. Following a cryptographic-based approach, the environment has oracle
      access to its PRAM semantics interface, meaning that it can make a polynomial number of 
      queries to the PRAM semantics *)
  module type Environment (ESI: EnvSemInterface) = {
    proc animate(): output_event_t 
  }.

  (** Interface used by the adversary to interact with the PRAM semantics *)
  module type AdvSemInterface = {
    proc stepP(id : processorId_t): bool
    proc stepS(): execution_info_t option
  }.

  (** Adversary type. Following a cryptographic-based approach, the adversary has oracle
      access to its PRAM semantics interface, meaning that it can make a polynomial number of 
      queries to the PRAM semantics *)
  module type Adversary (ASI : AdvSemInterface) = {
    proc step() : execution_info_t option
  }.

  (** Concrete realization of the environment PRAM interface, which defines the execution of a
      program. The **EnvironmentSemanticsInterface** module is parameterized by a PRAM semantics
      and an adversary, and its behavior is formalized as follows:
        - to provide inputs to the evaluation, invokes the corresponding **setInput** method
          disclosed by the PRAM semantics
        - to collect outputs from the evaluation, invokes the corresponding **getOutput** method
          disclosed by the PRAM semantics 
        - to evaluate the program, invokes the **step** adversary interface *)
  module EnvironmentSemanticsInterface (Sem : PRAM) (A : Adversary) = {
    include Sem [-init, setInput, getOutput]
    proc init = Sem.init
    proc setInput (x: input_t): bool = {
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

  (** Program evaluation module, that evaluates program **P** according to the PRAM semantics 
      **Sem**. The **Eval** module starts by initializing the program execution and then invokes
      the enviroment/adversary interface described above to evaluate it. If the evaluation is
      successful, it will return an output event, that constitutes its output. *)
  module Eval(Sem : PRAM, Z : Environment, A : Adversary) = {
    proc eval(meta : meta_information_t, Ps : L list) = {
      var b;

      EnvironmentSemanticsInterface(Sem,A).init(meta,Ps);
      b <@ Z(EnvironmentSemanticsInterface(Sem,A)).animate();
      return b;
    }
  }.

end PRAM.
