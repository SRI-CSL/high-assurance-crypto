(**
  This file provides a generic *map-reduce* like framework. Briefly, we define an arbitrary
  number of cores using the function RAM definition given in the *FRAM.ec* file. The parallel
  execution of these cores is then modeled using the PRAM semantics given in the *PRAM.ec* file.

  Our framework provides a generic equivalence result, that attests that any sequential evaluation
  carried out following the RAM model can be securely transformed into a parallel evaluation 
  carried out following the PRAM model. The following operators need to be provided when 
  instantiating the parallel framework:
    - **split_circuit** - that describes how programs (circuits) are splitted into
    smaller programs that are then given to the parallel cores to be evaluated separately
    - **aggregate_circuit** - that describes how the smaller programs can be put back
    together into the original program
    - **aggregate** - that describes how the outputs of the parallel cores can be aggregated into
    a single output

  Note that we require that the type of the programs that is distributed to the parallel cores to
  be the same as the original program. This restriction removes the use-case where programs
  could be transformed when being splitted, but still covers a considerable amount of parallelism
  use-cases.

  Our main result attests that aggregating the output of the parallel cores yields the same output
  of the sequential evaluation, and that there is no security breach when parallel cores evaluate
  the respective part of the program. Consequently, this means that the security properties 
  verified by the RAM execution will also be verified by the PRAM evaluation.

  In order to do so, the user needs to provide concrete instantiations of the afore mentioned 
  operators and prove the following properties about them, who are axiomatized in the 
  **MapReduce** theory:
    - **split_circuit** generates the same number of smaller circuits as there are parallel cores
    - **aggregate** is independent from the order of how the parallel states are maintained
    - if all parallel cores follow the FRAM step-based syntax, then **aggregate** produces the 
      same output of the sequential evaluation

  Armed with these properties, we formalize a *program-based secure computation* framework in 
  which one can simultaneously reason about program transformations and cryptographic protocol 
  security. Intuitively, no attacker shall distinguish a real world from an ideal world, even 
  when this attacker is collaborating with an adversarial environment that can control inputs 
  and observe outputs produced by the protocol. In the real world, an attacker interacts directly
  with the PRAM execution, according to a set of rules that define the attack model. In the ideal
  world, the attacker interacts with an ideal functionality that emulates the RAM execution. The
  PRAM evaluation is secure if there exists a simulator that can emulate the real-world view 
  observable by the attacker, while interacting with the ideal functionality.
*)
require import AllCore List.

from Semantics require import ALanguage.
from PRAM require import APRAM.
from RAM require import FunctionalRAM.
from Utilities require import ListExt.

theory MapReduce.

  (** Cloning an abstract language *)
  clone import Language.

  (** Information that can be revealed as the program evaluation progresses *)
  type execution_info_t.
  (** Output event type. This type does not represent the type of the outputs per se. Instead, its
      goal is to represent that the computation has finished *)
  type output_event_t.

  (** Instantiating the functional RAM with the language and types above. This functional RAM 
      interface will model the execution of each parallel core *)
  clone import FunctionalRAM with
    theory Language = Language,
    type execution_info_t = execution_info_t,
    type output_event_t = output_event_t.

  (** In a parallel execution, the original program (or circuit) is split into *smaller* 
      programs (or circuits) and each one of them is given to a core to be computed. The 
      **meta_information_t** type will store auxiliar data allows the reconstruction of the
      original program (or circuit) and also to aggregate the outputs of the parallel cores
      into a single output value *)
  type meta_information_t.

  (** Number of parallel cores *)
  op nprocesses : int.
  (** We require at least one parallel cores *)
  axiom nprocesses_pos (c : L) : 1 <= nprocesses.

  (** Instantiating the PRAM model with the same language as the functional RAM, the same
      execution leakage data type, the same output event and with the given number of parallel
      cores. Using the instantiated PRAM theory, one can now define a PRAM interface based on
      the execution of the parallel cores given by the functional RAM semantics *)
  clone import PRAM with
    theory Language = Language,
    type execution_info_t = execution_info_t,
    type processorId_t = int,
    type meta_information_t = meta_information_t,
    op nprocesses = nprocesses,
    type output_event_t = output_event_t.

  (** Splits a circuit into **nprocesses** smaller circuits *)
  op split_circuit : L -> meta_information_t * L list.

  (** Ensures that the circuit is split into **nprocesses** smaller circuits *)
  axiom split_circuit_size (L : L) : size (split_circuit L).`2 = nprocesses.

  (** Concrete PRAM evaluation module. Essentially, this module is a calling interface, that 
      invokes the parallel semantics after the circuit is split *)
  module Eval(Sem : PRAM, Z : Environment, A : Adversary) = {
    proc eval(L : L) = {
      var b;

      b <@ PRAM.Eval(Sem,Z,A).eval(split_circuit L);
      return b;
    }
  }.

  (** Parallel state. The parallel state maps the IDs of the cores to their corresponding state *)
  type pstate_t = (processorId_t * state_t) list.

  (** Parallel version of the **has_input** operator: the parallel evaluation has input iff all
      paralle cores have input *)
  op has_input (pst : pstate_t) : bool =
    all (fun id => has_input (odflt empty_state (assoc pst id))) (iota_ 0 nprocesses).
  (** Parallel version of the **has_output** operator: the parallel evaluation has output iff all
      paralle cores have input *)
  op has_output (pst : pstate_t) : bool =
    all (fun id => has_output (odflt empty_state (assoc pst id))) (iota_ 0 nprocesses).

  (** Collects output from the parallel state *)
  op get_output : meta_information_t -> pstate_t -> output_t option.

  (** Establishes that if the parallel state has output, then the **get_output** operation must 
      produce an output *)
  axiom has_output_get_output (meta : meta_information_t) 
                              (pst : pstate_t) : has_output pst => get_output meta pst <> None.
  (** Establishes that if the parallel state doesn't have output, then the **get_output** 
      operation must not produce an output *)
  axiom has_output_get_outputN (meta : meta_information_t) 
                               (pst : pstate_t) : !has_output pst => get_output meta pst = None.

  (** Ensures that **get_output** is order agnostic *)
  axiom get_output_perm_eq (meta : meta_information_t) (pst pst' : pstate_t) :
    uniq (unzip1 pst) => perm_eq pst pst' => get_output meta pst = get_output meta pst'.

  (** Establishes that if the parallel state has output, then the all parallel cores have 
      output *)
  axiom get_output_none meta pst :
    get_output meta pst <> None => 
    forall (x : int), x \in iota_ 0 nprocesses => has_output (odflt empty_state (assoc pst x)).

  (** Aggregates the small circuits into one big circuit *)
  op aggregate_circuit : meta_information_t * L list -> L.

  (** Aggregates the outputs of the parallel cores *)
  op aggregate : meta_information_t -> pstate_t -> execution_info_t option.

  (** Ensures that **aggregate** is order-agnostic *)
  axiom aggregate_perm_eq meta (pst pst' : pstate_t) :
    uniq (unzip1 pst) => perm_eq pst pst' => 
    aggregate meta pst = aggregate meta pst'.

  (** Ensures that, if the PRAM evaluation has output, then aggregating must produce an output *)
  axiom aggregate_none meta pst : has_output pst <=> aggregate meta pst <> None.

  (** Correctness of **aggregate**: if all parallel cores follow the FRAM step-based syntax, then
      **aggregate** produces the same output of the sequential evaluation *)
  axiom aggregate_correct (meta : meta_information_t) (cs : L list) 
                          (st : state_t) (pst : pstate_t) :
    has_input st =>
    has_input pst =>
    perm_eq (unzip1 pst) (iota_ 0 nprocesses) =>
    aggregate meta (map (fun k => (k, (step (set_input (init_state (nth witness cs k)) (oget (get_input (odflt empty_state (assoc pst k)))))).`1)) (iota_ 0 nprocesses)) = 
    (step (set_input (init_state (aggregate_circuit (meta, cs))) (oget (get_input st)))).`2.

  (** Equivalence between the RAM **get_output** and the PRAM **get_output** operators *)
  axiom get_output_correct (meta : meta_information_t) (cs : L list) (st : state_t) (pst : pstate_t) :
    size cs = nprocesses =>
    has_input st =>
    has_input pst =>
    (forall k, 0 <= k < nprocesses => 
      get_input (odflt empty_state (assoc pst k)) = get_input st) =>
    (forall k, 0 <= k < nprocesses => 
      get_circuit (odflt empty_state (assoc pst k)) = Some (nth witness cs k)) =>
    get_circuit st = Some (aggregate_circuit (meta, cs)) =>
    get_output meta (map (fun k => (k, (step (set_input (init_state (nth witness cs k)) (oget (get_input (odflt empty_state (assoc pst k)))))).`1)) (iota_ 0 nprocesses)) = 

    get_output (step (set_input (init_state (aggregate_circuit (meta, cs))) (oget (get_input st)))).`1.

  (** Map-reduce semantics, defined by means of the PRAM model. We use the terminology 
      "map-reduce" since the behavior that we formalize closely reseambles a map-reduce execution:
        1 - first, circuit is split into smaller tasks, one for each core
        2 - then each parallel core executes the given task
        3 - finally, the outputs of each core are aggregated into a single output *)
  module MapReduceSemantics = {

    var meta : meta_information_t
    var pst : pstate_t
    var ps : L list

    proc init(meta_ : meta_information_t, Ps : L list) : unit = { 
      var i, st_i; 

      pst <- [];
      meta <- meta_;
      i <- 0;
      ps <- Ps;
      while (i < nprocesses) {
        st_i <- init_state (nth witness ps i);
        pst <- (i, st_i) :: pst;
        i <- i + 1;
      }

    }

    proc stepP(id : processorId_t) : bool = {
      var r, st_i, execi;
      
      st_i <- odflt empty_state (assoc pst id);
      r <- false;
      if (0 <= id < nprocesses /\ has_input st_i /\ !has_output st_i) {
        (st_i, execi) <- step st_i;
        r <- true;
        pst <- (id, st_i) :: (assoc_rem id pst);
      }

      return r;
    }

    proc stepS() : execution_info_t option = {
      var i, b, st_i, y;

      i <- 0;
      while (i < nprocesses) {
        b <@ stepP(i);
        st_i <- odflt empty_state (assoc pst i);
        pst <- (i, st_i) :: (assoc_rem i pst);
        i <- i + 1;
      }
      y <- aggregate meta pst;
      
      return y;
    }

    proc setInput(x : input_t) : bool = {
      var b, st_i, i;

      i <- 0;
      b <- false;
      if (!has_input pst) {
        while (i < nprocesses) {
          st_i <- odflt empty_state (assoc pst i);
          st_i <- set_input st_i x;
          pst <- (i, st_i) :: (assoc_rem i pst);
          i <- i + 1;
        }
        b <- true;
      }

      return b;
    }

    proc getOutput() : output_t option = {
      var r;

      r <- None;
      if (has_output pst) {
        r <- get_output meta pst;
      }

      return r;
    }

  }.

  (** Interface used by the simulator to interact with the PRAM semantics. It is the same 
      interface available to the adversary *)
  module type SimulatorInterface = {
    include PRAM.AdvSemInterface
  }.

  (** The **Equivalence** section encompasses the secure equivalence proof between the a
      sequential RAM evaluation and a parallel PRAM evaluation *)
  section Equivalence.

    (** First, we define the sequential execution as the functional RAM interface *)
    module Sequential = FunctionalRAM.FRAM.
    (** The parallel execution is the map-reduce semantics interface above *)
    module Parallel = MapReduceSemantics.
    
    (** Simulator module. Intuitively, the goal of the simulator S is to intercept queries made 
        by the adversary A, and construct answers that will trick A into thinking it is dealing 
        with a distributed program evaluation. In practice, it amounts to constructing a 
        simulated real semantics, that shall keep in its internal state a full picture of 
        (a emulation of) the real-world parallel semantics. The most clear challenge when 
        defining the simulator is to ensure that the parallel execution is synchronized with the
        sequential one, making sure that:
          - if inputs are provided to the parallel execution, they are also provided to the 
            sequential execution 
          - when the set of cores finishes the parallel evaluation, the sequential evaluation 
            should also terminate at the same time 
          - if the environment requests outputs, either both evaluations have output or none of
            them has *)
    module Simulator = {

      var meta : meta_information_t

      proc init(meta_ : meta_information_t, Ps : L list) : unit = {
        meta <- meta_;
        Sequential.init(aggregate_circuit(meta, Ps));
      }

      proc stepP(id : processorId_t) : bool = {
        var r, x;
        r <@ Parallel.stepP(id);
        if (r /\ aggregate meta Parallel.pst <> None) {
          x <@ Sequential.step();
        }
        return r;
      }

      proc stepS() : execution_info_t option = {
        var r, x;
        r <@ Parallel.stepS();
        x <- None;
        if (r <> None) { x <@ Sequential.step(); }
        return x;
      }
    }.

    (** The parallel game is an instantiation of the **Eval** module with the map-reduce
        semantics interface *)
    module ParallelGame (Z : PRAM.Environment) (A : PRAM.Adversary) = Eval(Parallel, Z, A).

    (** Environment interface for the ideal game. This interface coordinates how the environment
        interacts with the simulator when it receives execution requests. Note that this
        interface also maintains a copy of the parallel PRAM exeuction and that is responsible
        to keep both evaluations synchronized *)
    module EnvironmentSemanticsInterface1 (Sem : PRAM) (A : Adversary) = {
      include Sem [-init, setInput, getOutput]

      proc init(meta : meta_information_t, Ps : L list) : unit = {
        Sem.init(meta, Ps);
        Simulator.init(meta, Ps);
      }

      proc setInput (x: input_t): bool = {
        var r;
        r <@ Sem.setInput(x);
        if (r) { Sequential.setInput(x); }
        return r;
      }

      proc getOutput(): output_t option = {
        var r, r';
        r' <- None;
        r <@ Sem.getOutput();
        if (r <> None) { r' <@ Sequential.getOutput(); }
        return r';
      }

      proc activate(): execution_info_t option = {
        var r;
        r <@ A(Simulator).step();
        return r;
      }
    }.

    (** Ideal evaluation model, who evaluates the program following the interaction with the
        simulator *)
    module IEval(Sem : PRAM, Z : Environment, A : Adversary) = {
      proc eval(L : L) = {
        var b;
        EnvironmentSemanticsInterface1(Sem,A).init(split_circuit L);
        b <@ Z(EnvironmentSemanticsInterface1(Sem,A)).animate();
        return (b);
      }
    }.

    (** Ideal *world* experience, that we dub **Sequential Game** *)
    module SequentialGame (Z: PRAM.Environment) (A: PRAM.Adversary) = 
      IEval(MapReduceSemantics,Z,A).    

    (** Auxiliar lemmas used to prove induction proof goals on association lists *)

    (** Proves that application of boolean AND to a list of booleans yields FALSE if the base
        case is FALSE *)
    lemma foldr_false bs : !foldr (/\) false bs.
    proof. by elim bs => //= b bs ->. qed.

    (** Proves that there are no repeated elements in integer lists that are equal up to 
        permutation to the *iota* list *)
    lemma perm_eq_iota_uniq s i j :
      perm_eq s (iota_ i j) => uniq s.
    proof. by progress; rewrite (perm_eq_uniq s (iota_ i j)) //= Iota.iota_uniq. qed.

    (** Proves that all elements in an integer list that is equal up to permutation to the
        *iota i j* list are in the [i;j] range *)
    lemma perm_eq_iota_mem s i j :
      perm_eq s (iota_ i j) => (forall k, i <= k < i+j => k \in s) by smt(@List).

    (** Proves that if the domain of an association list is equal up to permutation to some
        list [s'], then removing an element from it and adding it back results in a list that
        is still equal up to permutation to  [s'] *)
    lemma perm_eq_unzip1_assoc_rem (s : ('a * 'b) list) s' x :
      x \in unzip1 s =>
      perm_eq (unzip1 s) s' =>
      perm_eq (x :: unzip1 (assoc_rem x s)) s'.
    proof.
      move => H H0.
      have : perm_eq (x :: unzip1 (assoc_rem x s)) (unzip1 s).
        move : (unzip1_assoc_rem_cons x (oget (assoc s x)) s).
        by rewrite H /=; smt(@List).
      by move => H2; smt(@List).
    qed.

    (** Proves that all members of an association list that are different than [x] remain in the
        association list after removing [x]  *)
    lemma mem_unzip1_assoc_rem x y (s : ('a * 'b) list) : 
      x \in unzip1 s => y \in unzip1 s => y <> x =>
      y \in unzip1 (assoc_rem x s).
    proof. by rewrite !mapP; smt(@List). qed.

    (** Proves that an element of a list where there are no repetitions occurs one time in that
        list *)
    lemma mem_uniq_count (x : 'a) (s : 'a list) : 
      x \in s => uniq s => count (transpose (=) x) s = 1. 
    proof. elim s => //=; move => x' s; smt(@List). qed.

    (** Proves that an element that is not a member of a list where there are no repetitions 
        occurs zero times in that list *)
    lemma mem_uniq_count0 (x : 'a) (s : 'a list) : 
      !(x \in s) => count (transpose (=) x) s = 0. 
    proof. elim s => //=; move => x' s; smt(@List). qed.

    (** Proves that an element [x] of an association list where there are no repetitions occurs 
        the same number of times in an association list where an element [x'] such that [x <> x']
        is removed from it *)
    lemma mem_uniq_count_rem_assoc (x x' : 'a) (s : ('a * 'b) list) :
      uniq (unzip1 s) => (x, oget (assoc s x)) \in s => x' <> x => 
      count (transpose (=) x') (unzip1 (rem (x, oget (assoc s x)) s)) = 
      count (transpose (=) x') (unzip1 s).
    proof.
      progress.
      move : H H0; elim s => //=.
      move => xy s; progress.
      case ((x, oget (assoc (xy :: s) x)) = xy); progress; first by smt(mem_uniq_count).
      have ->: xy = (x, oget (assoc (xy :: s) x)) <=> false by smt().
      simplify; case (x' = xy.`1); progress.
        have ->: xy = (xy.`1, xy.`2) by smt().
        rewrite assoc_cons /=.
        have ->: x = xy.`1 <=> false by smt().
        simplify; case (xy.`1 \in unzip1 s); progress.
        by rewrite !mem_uniq_count0 //=; smt(@List).
      by smt(@List).
    qed.

    (** Proves that an element [x] of an association list where there are no repetitions occurs 
        the same number of times in an association list where an element [x'] such that [x <> x']
        is removed from it *)
    lemma mem_uniq_count_rem_assoc2 (x x' : 'a) (s : ('a * 'b) list) :
      uniq (unzip1 s) => !(x' \in unzip1 s) => x' <> x => 
      count (transpose (=) x') (unzip1 (rem (x, oget (assoc s x)) s)) = 
      count (transpose (=) x') (unzip1 s).
    proof.
      progress.
      move : H H0; elim s => //=.
      move => xy s; progress.
      case ((x, oget (assoc (xy :: s) x)) = xy); progress; first by smt(mem_uniq_count).
      have ->: xy = (x, oget (assoc (xy :: s) x)) <=> false by smt().
      simplify; case (x' = xy.`1); progress.
        have ->: xy = (xy.`1, xy.`2) by smt().
        rewrite assoc_cons /=.
        have ->: x = xy.`1 <=> false by smt().
        by simplify; case (xy.`1 \in unzip1 s).
      by rewrite !mem_uniq_count0 //=; smt(@List).
    qed.

    (** Proves that the domain of an association list remains the same after removing an element
        from it and then adding the same element back *)
    lemma perm_eq_unzip1_unzip1_assoc_rem (s : ('a * 'b) list) x y :
      uniq (unzip1 s) =>
      x \in unzip1 s => 
      perm_eq (unzip1 ((x,y) ::  assoc_rem x s)) (unzip1 s).
    proof.
      move => H H0.
      rewrite /assoc_rem /=.
      move : H H0; elim s => //=.
      move => xy. 
      elim xy => x' y' s Hind hxx hxx'.
      case (x = x'); progress; first by rewrite allP /=.
        have ->: x = x' <=> false by smt().
        simplify; move : Hind.
        have ->: x \in unzip1 s by smt().
        progress.
        have ->: x' = x <=> false by smt().
        by smt(@List). 
      move : Hind.
      have ->: x \in unzip1 s by smt().
      progress.
      have ->: x' = x <=> false by smt().
      rewrite !allP /=; progress.
      rewrite /b2i /pred1 /=.
      case (x = x0); progress.
        case (x' = x0); progress; first by smt().
        have : uniq (unzip1 s) by smt().
        progress.
        case (x0 \in unzip1 s); progress.
          have ->: count (transpose (=) x0) (unzip1 s) = 1 by rewrite mem_uniq_count //=.
          by smt(@List).
        move : H1.
        rewrite mem_cat; progress.
        case (x0 \in unzip1 (rem (x0, oget (assoc ((x', y') :: s) x0)) s)).
          rewrite mapP; progress.
          by move : H5 => /#.
        by smt().
      case (x' = x0); progress.
        have : uniq (unzip1 s) by smt().
        progress.
        case (x0 \in unzip1 s); progress.
          have ->: count (transpose (=) x0) (unzip1 s) = 1 by rewrite mem_uniq_count.
          by smt(@List).
        move : H1. 
        rewrite mem_cat; progress.
        rewrite assoc_cons /= H /= mem_uniq_count_rem_assoc2 //=.
        by smt().
      case (x0 \in unzip1 s); progress.
        have ->: count (transpose (=) x0) (unzip1 s) = 1 by rewrite mem_uniq_count //=; smt().
        rewrite assoc_cons /= H /=.
        have ->: count (transpose (=) x0) (unzip1 (rem (x, oget (assoc s x)) s)) = 
                 count (transpose (=) x0) (unzip1 s) by
          rewrite mem_uniq_count_rem_assoc //=; smt(@List).
        by rewrite (mem_uniq_count x0 (unzip1 s)) //=; smt().
      by rewrite assoc_cons /= H /= mem_uniq_count_rem_assoc //=; smt(@List).
    qed.

    (** Proves that if an element is not a member of a list, then it is also not a member of
        another list that is equal up to permutation *)
    lemma perm_eq_memN x (s1 s2 : 'a list) :
      perm_eq s1 s2 => !(x \in s1) => !(x \in s2) by smt(@List).

    (** Declaration of the environment module. This declaration is similar to universally 
        quantify over the environment in the security lemma *)
    declare module Z <: Environment {-MapReduceSemantics, -Simulator}.
    (** Declaration of the adversary module. This declaration is similar to universally 
        quantify over the adversary in the security lemma *)
    declare module A <: Adversary {-Z, -MapReduceSemantics, -Simulator}.

    (** Parallel security evaluation lemma, that establishes the secure equivalence between the
        sequential (RAM) and parallel (PRAM) executions. Informally, we are proving that the
        simulator is able to mimic the parallel evaluation of a circuit given access to an ideal
        functionality that sequentially evaluates it. This means that the observable behavior of
        the execution is the same and, therefore, transforming a sequential execution into a 
        parallel one following our approach doesn't comprimise the security of the evaluation.

        This lemma is equivalent to prove
          | Pr [ ParallelGame(Z, A).eval(L) : res @ &m ] -
            Pr [ SequentialGame(Z, A).eval(L) : res @ &m ] | = 0 *)
    equiv parallel_sequential_equivalence :
      ParallelGame(Z, A).eval ~ SequentialGame(Z, A).eval : 
      ={L, glob Z, glob A} ==> ={res}.
    proof. 
proc.

inline*.
sp.

seq 1 1 : (#[/1:3, 5, 7:10, 12, 14:]pre /\ ={MapReduceSemantics.pst,i} /\
           (forall k, 0 <= k < nprocesses => assoc MapReduceSemantics.pst{2} k = Some (init_state (nth witness Ps{2} k))) /\
           perm_eq (unzip1 MapReduceSemantics.pst{2}) (iota_ 0 nprocesses)).

while (#[/1:3, 5, 7:10, 12, 14:]pre /\ ={i} /\ ={MapReduceSemantics.pst} /\ 0 <= i{2} <= nprocesses /\
           (forall k, 0 <= k < i{2} => assoc MapReduceSemantics.pst{2} k = Some (init_state (nth witness Ps{2} k))) /\
          (unzip1 MapReduceSemantics.pst{2}) = rev (iota_ 0 i{2})).
wp; skip; progress.
move : H H0.
by elim (split_circuit L{2}) => meta ps /=.
smt().
smt().
case (k = i{2}); progress.
search assoc.
rewrite assoc_cons.
rewrite H9 /=.
rewrite H3.
smt().
done.

rewrite H4.
smt.

skip; progress.
smt(nprocesses_pos).
smt().
smt.
smt.
smt.

sp. wp.


call (_ : Simulator.meta{2} = MapReduceSemantics.meta{2} /\
          (*FRAM.p{2} = aggregate_circuit (Simulator.meta{2}, MapReduceSemantics.ps{2}) /\*)

          ={glob A, glob MapReduceSemantics} /\ 
          size MapReduceSemantics.ps{2} = nprocesses /\
          (*(forall k, 0 <= k < nprocesses => assoc MapReduceSemantics.pst{2} k <> None) /\*)

(* structural invariants *)
(perm_eq (unzip1 MapReduceSemantics.pst{2}) (iota_ 0 nprocesses)) /\
(*(forall k, 0 <= k < nprocesses => k \in unzip1 MapReduceSemantics.pst{2}) /\
(uniq (unzip1 MapReduceSemantics.pst{2})) /\*)

(* circuit invariants *)
(!has_input FRAM.st{2} => !has_output FRAM.st{2} => FRAM.st{2} = init_state (aggregate_circuit (MapReduceSemantics.meta{2}, MapReduceSemantics.ps{2}))) /\
(forall k, 0 <= k < nprocesses => !has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => !has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => odflt empty_state (assoc MapReduceSemantics.pst{2} k) = init_state (nth witness MapReduceSemantics.ps{2} k)) /\

          (forall k, 0 <= k < nprocesses => get_circuit (odflt empty_state (assoc MapReduceSemantics.pst{2} k))= Some (nth witness MapReduceSemantics.ps{2} k)) /\
          (get_circuit FRAM.st{2} = Some (aggregate_circuit (MapReduceSemantics.meta{2}, MapReduceSemantics.ps{2}))) /\

(* input invariants *)
(*(exists k, 0 <= k < nprocesses => has_input (oget (assoc MapReduceSemantics.pst{2} k)) => (forall k', 0 <= k' < nprocesses => has_input (oget (assoc MapReduceSemantics.pst{2} k')))) /\ *)

(*(!has_input Semantics.st{2} => get_input Semantics.st{2} = None) /\ 

(has_input Semantics.st{2} => get_input Semantics.st{2} <> None) /\ *)

          (has_input FRAM.st{2} <=> has_input MapReduceSemantics.pst{2}) /\

(*(forall k, 0 <= k < nprocesses => has_input (oget (assoc MapReduceSemantics.pst{2} k)) => get_input (oget (assoc MapReduceSemantics.pst{2} k)) <> None) /\ *)

(*(forall k, 0 <= k < nprocesses => !has_input (oget (assoc MapReduceSemantics.pst{2} k)) => get_input (oget (assoc MapReduceSemantics.pst{2} k)) = None) /\ *)

(has_input FRAM.st{2} => !has_output FRAM.st{2} => 
   FRAM.st{2} = set_input (init_state (aggregate_circuit (MapReduceSemantics.meta{2}, MapReduceSemantics.ps{2}))) (oget (get_input FRAM.st{2}))) /\
((forall k, 0 <= k < nprocesses => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => !has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => odflt empty_state (assoc MapReduceSemantics.pst{2} k) = set_input (init_state (nth witness MapReduceSemantics.ps{2} k)) (oget (get_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))) /\

(*(has_input Semantics.st{2} => (forall k, 0 <= k < nprocesses => has_input (oget (assoc MapReduceSemantics.pst{2} k)) => get_input (oget (assoc MapReduceSemantics.pst{2} k)) = get_input Semantics.st{2})) /\*)

(forall k k', 0 <= k < nprocesses => 0 <= k' < nprocesses => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k'))) /\

(* output invariants *)
(has_output FRAM.st{2} => has_input FRAM.st{2}) /\
(*(!has_output Semantics.st{2} => get_output Semantics.st{2} = None) /\
(has_output Semantics.st{2} => get_output Semantics.st{2} <> None) /\*)

(has_output FRAM.st{2} <=> has_output MapReduceSemantics.pst{2}) /\

(forall k, 0 <= k < nprocesses => has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k))) /\
(forall k, 0 <= k < nprocesses => !has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => !has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k))) /\

(has_output FRAM.st{2} => FRAM.st{2} = (step (set_input (init_state (aggregate_circuit (MapReduceSemantics.meta{2}, MapReduceSemantics.ps{2}))) (oget (get_input FRAM.st{2})))).`1) /\


(forall k, 0 <= k < nprocesses => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => 
  assoc MapReduceSemantics.pst{2} k = Some (step (set_input (init_state (nth witness MapReduceSemantics.ps{2} k)) (oget (get_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1) /\

(has_input MapReduceSemantics.pst{2} => has_input FRAM.st{2} => 
  forall k, 0 <= k < nprocesses => get_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) = get_input FRAM.st{2})


(*(forall k, 0 <= k < nprocesses => !has_output (oget (assoc MapReduceSemantics.pst{2} k)) => get_execution_info (oget (assoc MapReduceSemantics.pst{2} k)) = None) /\
(forall k, 0 <= k < nprocesses => has_output (oget (assoc MapReduceSemantics.pst{2} k)) => get_execution_info (oget (assoc MapReduceSemantics.pst{2} k)) <> None) /\*)
(*(forall k, 0 <= k < nprocesses => !has_output (oget (assoc MapReduceSemantics.pst{2} k)) => get_output (oget (assoc MapReduceSemantics.pst{2} k)) = None) /\
(forall k, 0 <= k < nprocesses => has_output (oget (assoc MapReduceSemantics.pst{2} k)) => get_output (oget (assoc MapReduceSemantics.pst{2} k)) <> None) *)

(*(has_output MapReduceSemantics.pst{2} => (forall k, 0 <= k < nprocesses => has_output (oget (assoc MapReduceSemantics.pst{2} k)))) /\*)

(*(has_output MapReduceSemantics.pst{2} => has_output Semantics.st{2}) /\*)

(*(has_output MapReduceSemantics.pst{2} => get_output MapReduceSemantics.pst{2} <> None) /\
(!has_output MapReduceSemantics.pst{2} => get_output MapReduceSemantics.pst{2} = None) /\*)
(*(has_output Semantics.st{2} => get_execution_info Semantics.st{2} = aggregate MapReduceSemantics.meta{2} MapReduceSemantics.pst{2}) /\*)
(*(has_output Semantics.st{2} => has_output MapReduceSemantics.pst{2} => get_output Semantics.st{2} = get_output MapReduceSemantics.pst{2}) *)

(*(forall k, 0 <= k < nprocesses => has_input (oget (assoc MapReduceSemantics.pst{2} k)) => has_input (step (nth witness MapReduceSemantics.ps{2} k) (oget (assoc MapReduceSemantics.pst{2} k))).`1) /\
(forall k, 0 <= k < nprocesses => get_input (step (nth witness MapReduceSemantics.ps{2} k) (oget (assoc MapReduceSemantics.pst{2} k))).`1 = get_input (oget (assoc MapReduceSemantics.pst{2} k)))*)

).

proc.
inline*.
sp.

if => //=; last first.
wp; skip; progress.

rcondt{2} 4.
progress.
wp.
while (true).
wp; skip; progress.
done.

wp.

while (#[/1,4,7:18,23:27]pre /\ ={i, x0} /\ 0 <= i{2} <= nprocesses /\
(forall k, 0 <= k < i{2} => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k))) /\
(forall k, 0 <= k < i{2} => get_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) = Some x0{2}) /\
(forall k, 0 <= k < i{2} => odflt empty_state (assoc MapReduceSemantics.pst{2} k) = set_input (init_state (nth witness MapReduceSemantics.ps{2} k)) x0{2}) /\
(has_input FRAM.st{2} => has_input MapReduceSemantics.pst{2}) /\
(forall k, 0 <= k < i{2} => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => 
! has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => odflt empty_state (assoc MapReduceSemantics.pst{2} k) = set_input (init_state (nth witness MapReduceSemantics.ps{2} k)) x0{2}) /\
(forall k, 0 <= k < nprocesses => !has_output(odflt empty_state (assoc  MapReduceSemantics.pst{2} k))) /\
(forall k, 0 <= k < i{2} => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => 
  assoc MapReduceSemantics.pst{2} k = Some (step (set_input (init_state (nth witness MapReduceSemantics.ps{2} k)) x0{2})).`1) /\
(forall k k', 0 <= k < i{2} => 0 <= k' < i{2} => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k'))) /\ 
(forall k, !(k < i{2}) => k < nprocesses => odflt empty_state (assoc MapReduceSemantics.pst{2} k) = init_state (nth witness MapReduceSemantics.ps{2} k))
(*(forall k k', 0 <= k < i{2} => 0 <= k' < k => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k'))))*)
).

wp; skip; progress.

have : perm_eq (i{2} :: unzip1 (assoc_rem (i{2}) MapReduceSemantics.pst{2})) (iota_ 0 MapReduce.nprocesses).
rewrite perm_eq_unzip1_assoc_rem.
print perm_eq_iota_mem.
rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses).
done.
smt().
done.
smt().

have : perm_eq (i{2} :: unzip1 (assoc_rem (i{2}) MapReduceSemantics.pst{2})) (iota_ 0 MapReduce.nprocesses).
rewrite perm_eq_unzip1_assoc_rem.
print perm_eq_iota_mem.
rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses).
done.
smt().
done.
rewrite /perm_eq. smt().

move : H25 H26.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
move : H25.
rewrite has_input_set_input /=.
done.
smt().

rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
rewrite get_circuit_set_input /=.
smt().
smt().

have : has_output MapReduceSemantics.pst{2}.
smt().
rewrite /has_output /= !allP /=.
progress.
have : has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} (i{2}))).
rewrite H24.
smt.
rewrite assoc_rem_cons /=.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (x2 = i{2}); progress.
rewrite has_output_set_input /=.
done.
smt().

move : H23.
rewrite /has_output /= !allP /=.
progress.
have : has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} (i{2}))).
move : (H23 i{2}).
have ->: i{2} \in iota_ 0 MapReduce.nprocesses.
smt.
simplify.
rewrite assoc_rem_cons /=.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
rewrite has_output_set_input /=.
done.
smt().

move : H25.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
rewrite has_input_set_input /=.
smt().

move : H25.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
move : H25.
rewrite has_input_set_input /=.
smt().

smt().
smt().
smt().

rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
rewrite has_input_set_input.
smt().

rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
rewrite get_input_set_input.
smt().
smt().

rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

rewrite /has_input !allP /=.
progress.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (x2 = i{2}); progress.
rewrite has_input_set_input.
have : has_input MapReduceSemantics.pst{2} by smt().
rewrite /has_input /= allP; progress.
by rewrite H26. 

move : H25 H26.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
rewrite has_output_set_input /=.
smt().
smt().

move : H25 H26.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt.
smt().

move : H27.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
case (k' = i{2}); progress.
rewrite H14.
smt().
by rewrite has_input_set_input /=.
case (k' = i{2}); progress.
by rewrite has_input_set_input /=.
smt().

rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

skip; progress.
smt(nprocesses_pos).
smt().
smt().
smt().
smt().
smt().

case (has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k))); progress.
have : has_input MapReduceSemantics.pst{2}.
rewrite /has_input allP /=.
progress.
move : (H8 k x2).
have ->: 0 <= k && k < MapReduce.nprocesses. smt().
have ->: 0 <= x2 && x2 < MapReduce.nprocesses. smt.
simplify.
rewrite H19.
done.
done.
smt().

smt().
smt().

case (has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k))); progress.
have : has_input MapReduceSemantics.pst{2}.
rewrite /has_input allP /=.
progress.
move : (H8 k x2).
have ->: 0 <= k && k < MapReduce.nprocesses. smt().
have ->: 0 <= x2 && x2 < MapReduce.nprocesses. smt.
simplify.
rewrite H19.
done.
done.
smt().

move : H42.
rewrite has_input_set_input /=.
done.

rewrite get_circuit_set_input.
smt().

rewrite /has_input allP /=.
progress.
smt.

rewrite has_input_set_input /=.

rewrite -H1.
done.
move : H43.
rewrite has_output_set_input.
smt().
rewrite get_input_set_input.
smt().

smt().
smt().

move : H42.
rewrite has_output_set_input /=.
smt().

move : H42.
rewrite has_output_set_input /=.
smt().

rewrite has_output_set_input /=.
smt().

move : H42.
rewrite has_output_set_input /=.
smt().

smt().
smt.
smt().
smt().
smt().
smt().
smt().

proc; inline *.
sp 1 2.
case (has_output MapReduceSemantics.pst{2}); last first.
if => //=.
exfalso => /#.
rcondf{2} 2.
progress. wp; skip; progress.
by wp.

if => //=; last by exfalso => /#.
rcondt{2} 3.
progress. wp; skip; progress.
by rewrite has_output_get_output.

sp 0 3.
if{2} => //; last first.
exfalso => /#.

wp; skip; progress.
move : (get_output_correct MapReduceSemantics.meta{2} MapReduceSemantics.ps{2} FRAM.st{2} MapReduceSemantics.pst{2}).
rewrite H /=.
have ->: (forall (k : int),
    0 <= k && k < MapReduce.nprocesses =>
    get_circuit (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) =
    Some (nth witness MapReduceSemantics.ps{2} k)) <=> true.
done.
simplify.
rewrite H4 /=.
progress.
rewrite (get_output_perm_eq MapReduceSemantics.meta{2} MapReduceSemantics.pst{2} (map
          (fun (k : int) =>
             (k,
              (step
                 (set_input
                    (init_state (nth witness MapReduceSemantics.ps{2} k))
                    (oget
                       (get_input
                          (odflt empty_state
                             (assoc MapReduceSemantics.pst{2} k)))))).`1))
          (iota_ 0 MapReduce.nprocesses))).
rewrite (perm_eq_iota_uniq (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses).
done.

have H20 : perm_eq (unzip1 MapReduceSemantics.pst{2}) (unzip1 (map
     (fun (k : int) =>
        (k,
         (step
            (set_input (init_state (nth witness MapReduceSemantics.ps{2} k))
               (oget
                  (get_input
                     (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1))
     (iota_ 0 MapReduce.nprocesses))).
rewrite -map_comp /(\o) /= map_id.
done.
have H21 : forall x, x \in iota_ 0 MapReduce.nprocesses => assoc MapReduceSemantics.pst{2} x = assoc (map
     (fun (k : int) =>
        (k,
         (step
            (set_input (init_state (nth witness MapReduceSemantics.ps{2} k))
               (oget
                  (get_input
                     (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1))
     (iota_ 0 MapReduce.nprocesses)) x.
progress.
rewrite map_assoc.
done.
simplify.
rewrite -H14.
smt(@List).
smt(@List).
smt(@List).
done.
rewrite assoc_is_perm_eq.
rewrite (perm_eq_iota_uniq (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses).
done.
done.
progress.
rewrite H21.
smt(@List).
done.

rewrite H19.
smt().
smt().
progress.
rewrite H14 /=.
done.
have : has_input MapReduceSemantics.pst{2}.
smt().
rewrite /has_input /= allP.
progress.
rewrite H22 /=.
smt(@List).
move : H16.
rewrite /has_output /= allP.
progress.
rewrite H16 /=.
smt(@List).
rewrite H13.
smt().
rewrite !get_input_step !get_input_set_input.
rewrite H13.
smt().
smt().
smt().

proc.

call (_ : Simulator.meta{2} = MapReduceSemantics.meta{2} /\
          (*FRAM.p{2} = aggregate_circuit (Simulator.meta{2}, MapReduceSemantics.ps{2}) /\*)

          ={glob MapReduceSemantics} /\ 
          size MapReduceSemantics.ps{2} = nprocesses /\
          (*(forall k, 0 <= k < nprocesses => assoc MapReduceSemantics.pst{2} k <> None) /\*)

(* structural invariants *)
(perm_eq (unzip1 MapReduceSemantics.pst{2}) (iota_ 0 nprocesses)) /\
(*(forall k, 0 <= k < nprocesses => k \in unzip1 MapReduceSemantics.pst{2}) /\
(uniq (unzip1 MapReduceSemantics.pst{2})) /\*)

(* circuit invariants *)
(!has_input FRAM.st{2} => !has_output FRAM.st{2} => FRAM.st{2} = init_state (aggregate_circuit (MapReduceSemantics.meta{2}, MapReduceSemantics.ps{2}))) /\
(forall k, 0 <= k < nprocesses => !has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => !has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => odflt empty_state (assoc MapReduceSemantics.pst{2} k) = init_state (nth witness MapReduceSemantics.ps{2} k)) /\

          (forall k, 0 <= k < nprocesses => get_circuit (odflt empty_state (assoc MapReduceSemantics.pst{2} k))= Some (nth witness MapReduceSemantics.ps{2} k)) /\
          (get_circuit FRAM.st{2} = Some (aggregate_circuit (MapReduceSemantics.meta{2}, MapReduceSemantics.ps{2}))) /\

(* input invariants *)
(*(exists k, 0 <= k < nprocesses => has_input (oget (assoc MapReduceSemantics.pst{2} k)) => (forall k', 0 <= k' < nprocesses => has_input (oget (assoc MapReduceSemantics.pst{2} k')))) /\ *)

(*(!has_input Semantics.st{2} => get_input Semantics.st{2} = None) /\ 

(has_input Semantics.st{2} => get_input Semantics.st{2} <> None) /\ *)

          (has_input FRAM.st{2} <=> has_input MapReduceSemantics.pst{2}) /\

(*(forall k, 0 <= k < nprocesses => has_input (oget (assoc MapReduceSemantics.pst{2} k)) => get_input (oget (assoc MapReduceSemantics.pst{2} k)) <> None) /\ *)

(*(forall k, 0 <= k < nprocesses => !has_input (oget (assoc MapReduceSemantics.pst{2} k)) => get_input (oget (assoc MapReduceSemantics.pst{2} k)) = None) /\ *)

(has_input FRAM.st{2} => !has_output FRAM.st{2} => 
   FRAM.st{2} = set_input (init_state (aggregate_circuit (MapReduceSemantics.meta{2}, MapReduceSemantics.ps{2}))) (oget (get_input FRAM.st{2}))) /\
((forall k, 0 <= k < nprocesses => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => !has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => odflt empty_state (assoc MapReduceSemantics.pst{2} k) = set_input (init_state (nth witness MapReduceSemantics.ps{2} k)) (oget (get_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))) /\

(*(has_input Semantics.st{2} => (forall k, 0 <= k < nprocesses => has_input (oget (assoc MapReduceSemantics.pst{2} k)) => get_input (oget (assoc MapReduceSemantics.pst{2} k)) = get_input Semantics.st{2})) /\*)

(forall k k', 0 <= k < nprocesses => 0 <= k' < nprocesses => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k'))) /\

(* output invariants *)
(has_output FRAM.st{2} => has_input FRAM.st{2}) /\
(*(!has_output Semantics.st{2} => get_output Semantics.st{2} = None) /\
(has_output Semantics.st{2} => get_output Semantics.st{2} <> None) /\*)

(has_output FRAM.st{2} <=> has_output MapReduceSemantics.pst{2}) /\

(forall k, 0 <= k < nprocesses => has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k))) /\
(forall k, 0 <= k < nprocesses => !has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => !has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k))) /\

(has_output FRAM.st{2} => FRAM.st{2} = (step (set_input (init_state (aggregate_circuit (MapReduceSemantics.meta{2}, MapReduceSemantics.ps{2}))) (oget (get_input FRAM.st{2})))).`1) /\


(forall k, 0 <= k < nprocesses => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => 
  assoc MapReduceSemantics.pst{2} k = Some (step (set_input (init_state (nth witness MapReduceSemantics.ps{2} k)) (oget (get_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1) /\

(has_input MapReduceSemantics.pst{2} => has_input FRAM.st{2} => 
  forall k, 0 <= k < nprocesses => get_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) = get_input FRAM.st{2})


(*(forall k, 0 <= k < nprocesses => !has_output (oget (assoc MapReduceSemantics.pst{2} k)) => get_execution_info (oget (assoc MapReduceSemantics.pst{2} k)) = None) /\
(forall k, 0 <= k < nprocesses => has_output (oget (assoc MapReduceSemantics.pst{2} k)) => get_execution_info (oget (assoc MapReduceSemantics.pst{2} k)) <> None) /\*)
(*(forall k, 0 <= k < nprocesses => !has_output (oget (assoc MapReduceSemantics.pst{2} k)) => get_output (oget (assoc MapReduceSemantics.pst{2} k)) = None) /\
(forall k, 0 <= k < nprocesses => has_output (oget (assoc MapReduceSemantics.pst{2} k)) => get_output (oget (assoc MapReduceSemantics.pst{2} k)) <> None) *)

(*(has_output MapReduceSemantics.pst{2} => (forall k, 0 <= k < nprocesses => has_output (oget (assoc MapReduceSemantics.pst{2} k)))) /\*)

(*(has_output MapReduceSemantics.pst{2} => has_output Semantics.st{2}) /\*)

(*(has_output MapReduceSemantics.pst{2} => get_output MapReduceSemantics.pst{2} <> None) /\
(!has_output MapReduceSemantics.pst{2} => get_output MapReduceSemantics.pst{2} = None) /\*)
(*(has_output Semantics.st{2} => get_execution_info Semantics.st{2} = aggregate MapReduceSemantics.meta{2} MapReduceSemantics.pst{2}) /\*)
(*(has_output Semantics.st{2} => has_output MapReduceSemantics.pst{2} => get_output Semantics.st{2} = get_output MapReduceSemantics.pst{2}) *)

(*(forall k, 0 <= k < nprocesses => has_input (oget (assoc MapReduceSemantics.pst{2} k)) => has_input (step (nth witness MapReduceSemantics.ps{2} k) (oget (assoc MapReduceSemantics.pst{2} k))).`1) /\
(forall k, 0 <= k < nprocesses => get_input (step (nth witness MapReduceSemantics.ps{2} k) (oget (assoc MapReduceSemantics.pst{2} k))).`1 = get_input (oget (assoc MapReduceSemantics.pst{2} k)))*)

).

proc.
inline Parallel.stepP.
inline Sequential.step.
sp 2 3.

if => //; last first.
sp 0 1.
if{2} => //.
exfalso => /#.

sp 3 4.
if{2} => //; last first.
skip; progress.

(*rewrite assoc_rem_cons.
rewrite H3.
smt().
smt().*)
smt().

have : perm_eq (id{2} :: unzip1 (assoc_rem id{2} pst_R)) (iota_ 0 MapReduce.nprocesses).
rewrite perm_eq_unzip1_assoc_rem.
print perm_eq_iota_mem.
rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses).
done.
smt().
done.
smt().

have : perm_eq (id{2} :: unzip1 (assoc_rem id{2} pst_R)) (iota_ 0 MapReduce.nprocesses).
rewrite perm_eq_unzip1_assoc_rem.
print perm_eq_iota_mem.
rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses).
done.
smt().
done.
rewrite /perm_eq. smt().

move : H25 H26.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
smt().

rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
rewrite get_circuit_step.
smt().
smt().

have : has_input pst_R.
smt().
rewrite /has_input !allP /=.
progress.
move : (H24 x0).
rewrite H25/=.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (x0 = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
rewrite has_input_step.
done.

have : has_input pst_R.
move : H23.
rewrite /has_input !allP /=.
progress.
move : (H23 x0).
rewrite H24/=.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (x0 = id{2}); progress.
smt().

move : H25 H26.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
have ->: st_i{2} = (step 
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
smt().

move : H27.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
case (k' = id{2}); progress.
smt().
case (k' = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
smt().

have : !has_output pst_R.
have : !has_output ((id{2}, st_i{2}) :: assoc_rem id{2} pst_R).
smt(aggregate_none).
rewrite /has_output /= !allP /=.
progress.
smt.
smt().

smt(aggregate_none).

move : H25.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
smt().

move : H25.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
smt().

move : H25 H26.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
move : H25 H26.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
rewrite has_input_step.
progress.
case (has_output (odflt empty_state (assoc pst_R id{2}))); progress.
rewrite H9.
smt().
done.
done.
smt.
smt().

move : H23.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
smt().

rcondt{2} 2.
progress.
wp; skip; progress.

have : has_input pst_R.
rewrite /has_input allP /=. 
progress.
rewrite (H10 id{hr} x0).
smt().
smt.
done.
smt().

wp; skip; progress.

smt().

have : perm_eq (id{2} :: unzip1 (assoc_rem id{2} pst_R)) (iota_ 0 MapReduce.nprocesses).
rewrite perm_eq_unzip1_assoc_rem.
print perm_eq_iota_mem.
rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses).
done.
smt().
done.
smt().

have : perm_eq (id{2} :: unzip1 (assoc_rem id{2} pst_R)) (iota_ 0 MapReduce.nprocesses).
rewrite perm_eq_unzip1_assoc_rem.
print perm_eq_iota_mem.
rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses).
done.
smt().
done.
rewrite /perm_eq. smt().

move : H23 H24.
rewrite has_input_step /=.
progress.
rewrite step_has_inputN.
smt.
smt().

move : H25 H26.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
smt().

rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
rewrite get_circuit_step.
smt().
smt().

rewrite get_circuit_step.
smt().

have : has_input pst_R.
move : H23.
rewrite /has_input !allP /=.
progress.
move : H23.
rewrite has_input_step.
smt.
progress.
rewrite /has_input !allP /=.
progress.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (x0 = id{2}); progress.
have ->: st_i{2} = (step (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
move : H23.
rewrite has_input_step.
progress.
smt.

have : has_input pst_R.
move : H23.
rewrite /has_input !allP /=.
progress.
move : (H23 x0).
rewrite H24 /=.
smt.
smt.

move : H24.
rewrite has_output_step.
smt.
done.


move : H25 H26.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
move : H25 H26.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
rewrite has_input_step.
progress.
case (has_output (odflt empty_state (assoc pst_R id{2}))); progress.
rewrite H9.
smt().
done.
done.
smt.
smt().

move : H27.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
case (k' = id{2}); progress.
smt().
case (k' = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
smt().

rewrite has_input_step.
smt.

smt(aggregate_none).

move : H23.
rewrite /has_output /= allP /=.
progress.
move : (H23 id{2}).
have ->: id{2} \in iota_ 0 MapReduce.nprocesses.
smt.
simplify.
progress.
rewrite has_output_step.
rewrite H7.
rewrite /has_input /= allP /=.
progress.
smt.

move : H25.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
smt().

move : H25.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
smt().

rewrite get_input_step /=.
have : has_input pst_R.
smt.
rewrite -H7.
progress.
case (has_output FRAM.st{2}); progress.
have : has_output pst_R.
smt().
rewrite /has_output /= allP /=.
progress.
move : (H26 id{2}).
have ->: id{2} \in iota_ 0 MapReduce.nprocesses by smt.
simplify.
done.
smt().

move : H25 H26.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
move : H25 H26.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
rewrite has_input_step.
progress.
case (has_output (odflt empty_state (assoc pst_R id{2}))); progress.
rewrite H9.
smt().
done.
done.
smt.
smt().

move : H23.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 pst_R) 0 nprocesses) => /#.
case (k = id{2}); progress.
have ->: st_i{2} = (step
     (odflt empty_state (assoc pst_R id{2}))).`1 by smt().
smt.
smt.

proc.
inline Parallel.stepS.
inline Sequential.step.
sp 1 1.

seq 1 1 : (#[/4:16, 18:]pre /\ (forall k, 0 <= k < nprocesses => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))).
            (*(forall k, 0 <= k < ProverParallelSemantics.nprocessors{1} => !has_output (oget (assoc ProverParallelSemantics.pst{2} k)) => assoc ys{2} k = None)*)

while (#[/4:16, 18:]pre /\ ={i} /\ 0 <= i{2} <= nprocesses /\

(forall k, 0 <= k < i{2} => has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k))) /\

(forall k, 0 <= k < i{2} => has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) => assoc MapReduceSemantics.pst{2} k =
    Some
      (step
         (set_input (init_state (nth witness MapReduceSemantics.ps{2} k))
            (oget
               (get_input
                  (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1) /\

(has_output FRAM.st{2} => has_input MapReduceSemantics.pst{2}) /\
(has_output FRAM.st{2} => has_output MapReduceSemantics.pst{2}) /\

(forall (k : int),
     0 <= k && k < i{2} =>
     has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) =>
     has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k))) /\

(has_output FRAM.st{2} =>
   FRAM.st{2} =
   (step
      (set_input
         (init_state
            (aggregate_circuit
               (MapReduceSemantics.meta{2}, MapReduceSemantics.ps{2})))
         (oget (get_input FRAM.st{2})))).`1) /\

(forall (k : int),
    0 <= k && k < i{2} =>
    has_input (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) =>
    has_output (odflt empty_state (assoc MapReduceSemantics.pst{2} k)) =>
    assoc MapReduceSemantics.pst{2} k =
    Some
      (step
         (set_input (init_state (nth witness MapReduceSemantics.ps{2} k))
            (oget
               (get_input
                  (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1)).

inline MapReduceSemantics.stepP.

sp 3 3.
if => //; last first.
wp; skip; progress.

have : perm_eq (i{2} :: unzip1 (assoc_rem i{2} MapReduceSemantics.pst{2})) (iota_ 0 MapReduce.nprocesses).
rewrite perm_eq_unzip1_assoc_rem.
print perm_eq_iota_mem.
rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses).
done.
smt().
done.
smt().

have : perm_eq (i{2} :: unzip1 (assoc_rem i{2} MapReduceSemantics.pst{2})) (iota_ 0 MapReduce.nprocesses).
rewrite perm_eq_unzip1_assoc_rem.
print perm_eq_iota_mem.
rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses).
done.
smt().
done.
rewrite /perm_eq. smt().

move : H29 H30.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

have : has_input MapReduceSemantics.pst{2}.
smt().
rewrite /has_input !allP /=.
progress.
move : (H28 x0).
rewrite H29/=.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (x0 = i{2}); progress.

have : has_input MapReduceSemantics.pst{2}.
move : H27.
rewrite /has_input !allP /=.
progress.
move : (H27 x0).
rewrite H28 /=.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (x0 = i{2}); progress.
smt().

move : H29 H30.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

move : H31.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
case (k' = i{2}); progress.
smt().
case (k' = i{2}); progress.
smt().
smt().

move : H29.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

move : H29.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

move : H29 H30.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

move : H27.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

smt().
smt().

move : H29.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

move : H29.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

have : has_output
            (odflt empty_state (assoc MapReduceSemantics.pst{2} i{2})).
have : has_output MapReduceSemantics.pst{2}.
smt().
rewrite /has_output /= !allP /=.
progress.
rewrite H28 /=.
smt.
progress.
have : has_input
            (odflt empty_state (assoc MapReduceSemantics.pst{2} i{2})).
have : has_output MapReduceSemantics.pst{2}.
smt().
progress.
have : has_input MapReduceSemantics.pst{2}.
smt().
rewrite /has_input /= !allP /=.
progress.
rewrite H30 /=.
smt.
progress.
rewrite /has_input /= allP /=.
progress.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (x0 = i{2}); progress.
smt.

have : has_output MapReduceSemantics.pst{2}.
smt().
rewrite /has_output /= !allP /=.
progress.
move : (H28 x0).
rewrite H29 /=.
progress.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (x0 = i{2}); progress.

move : H29.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

move : H29 H30.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt().
smt().

wp; skip; progress.

have : perm_eq (i{2} :: unzip1
                (assoc_rem i{2}
                   ((i{2},
                     (step
                        (odflt empty_state
                           (assoc MapReduceSemantics.pst{2} i{2}))).`1) :: 
                   assoc_rem i{2} MapReduceSemantics.pst{2})))(iota_ 0 MapReduce.nprocesses).
rewrite perm_eq_unzip1_assoc_rem.
smt.
move : (perm_eq_unzip1_unzip1_assoc_rem MapReduceSemantics.pst{2} i{2} ((step
          (odflt empty_state (assoc MapReduceSemantics.pst{2} i{2}))).`1)).
have ->: uniq (unzip1 MapReduceSemantics.pst{2}).
smt.
have ->: i{2} \in unzip1 MapReduceSemantics.pst{2}.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
smt.
smt().

have : perm_eq (i{2} :: unzip1
                (assoc_rem i{2}
                   ((i{2},
                     (step
                        (odflt empty_state
                           (assoc MapReduceSemantics.pst{2} i{2}))).`1) :: 
                   assoc_rem i{2} MapReduceSemantics.pst{2})))(iota_ 0 MapReduce.nprocesses).
rewrite perm_eq_unzip1_assoc_rem.
smt.
move : (perm_eq_unzip1_unzip1_assoc_rem MapReduceSemantics.pst{2} i{2} ((step
          (odflt empty_state (assoc MapReduceSemantics.pst{2} i{2}))).`1)).
have ->: uniq (unzip1 MapReduceSemantics.pst{2}).
smt.
have ->: i{2} \in unzip1 MapReduceSemantics.pst{2}.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
smt.
rewrite /perm_eq. smt().

move : H32 H33.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
case (k = i{2}); progress.
move : H33.
rewrite has_output_step.
done.
done.
smt().

rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
case (k = i{2}); progress.
rewrite get_circuit_step.
smt().
smt().

rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
rewrite /has_input allP /=.
progress.
have : has_input MapReduceSemantics.pst{2}.
smt().
rewrite /has_input allP /=.
progress.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (x0 = i{2}); progress.
rewrite has_input_step.
smt().
smt().

move : H30.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
rewrite /has_input allP /=.
progress.
have : has_input MapReduceSemantics.pst{2}.
rewrite /has_input allP /=.
progress.
move : (H30 x0).
rewrite H31 /=.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (x0 = i{2}); progress.
smt().

move : H32 H33.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
case (k = i{2}); progress.
move : H33.
rewrite has_output_step.
done.
done.
smt().

move : H34.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
case (k = i{2}); progress.
case (k' = i{2}); progress.
smt().
case (k' = i{2}); progress.
rewrite has_input_step.
smt().
smt().

move : H32.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
case (k = i{2}); progress.
move : H32.
rewrite has_input_step.
done.
smt().

move : H32.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
case (k = i{2}); progress.
move : H32.
rewrite has_input_step.
done.
smt().

move : H32 H33.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
case (k = i{2}); progress.
smt.
smt().

move : H30.
rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
smt(perm_eq_unzip1_unzip1_assoc_rem).
smt(@List).
simplify.
case (k = i{2}); progress.
smt.
smt().

smt().
smt().

move : H32.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt.
smt().

move : H32.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
smt.
smt().

rewrite !assoc_rem_cons.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
simplify.
have : has_output
            (odflt empty_state (assoc MapReduceSemantics.pst{2} i{2})).
have : has_output MapReduceSemantics.pst{2}.
smt().
rewrite /has_output /= !allP /=.
progress.
rewrite H31 /=.
smt.
progress.

have : has_output MapReduceSemantics.pst{2}.
smt().
rewrite /has_output /= !allP /=.
progress.
move : (H31 i{2}).
have ->: i{2} \in iota_ 0 MapReduce.nprocesses by smt.
done.

move : H32.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
rewrite has_input_step.
done.
smt().

move : H32 H33.
rewrite !assoc_rem_cons.
smt(perm_eq_unzip1_unzip1_assoc_rem).
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
by rewrite (perm_eq_iota_mem (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses) => /#.
case (k = i{2}); progress.
rewrite get_input_step.
smt().
smt().

skip; progress.
smt(nprocesses_pos).
smt().
smt().
smt().
smt().
smt().
smt().
smt().

case (aggregate MapReduceSemantics.meta{2} MapReduceSemantics.pst{2} <> None); last first.
rcondf{2} 4.
progress.
wp; skip; progress.
wp; skip; progress.

have : has_input FRAM.st{2}.
smt().
progress.
have : has_input MapReduceSemantics.pst{2}.
smt().
rewrite /has_input /has_output !allP /=.
progress.
move : (H19 x0).
rewrite H20 /=.
progress.
rewrite H15.
smt.
done.

smt(aggregate_none).

rcondt{2} 4.
progress.
wp; skip; progress.
rcondt{2} 5.
progress.
wp; skip; progress.

have : has_output MapReduceSemantics.pst{hr}.
smt(aggregate_none). 
progress.
case (has_input MapReduceSemantics.pst{hr}); last first; progress.
move : H17 H18.
rewrite /has_input /has_output !allP /=.
progress.
smt.
smt().

wp; skip; progress.

have : has_output MapReduceSemantics.pst{2}.
smt(aggregate_none). 
progress.
case (has_input MapReduceSemantics.pst{2}); last first; progress.
move : H17 H18.
rewrite /has_input /has_output !allP /=.
progress.
smt.

print aggregate_correct.
move : (aggregate_correct MapReduceSemantics.meta{2} MapReduceSemantics.ps{2} FRAM.st{2}  MapReduceSemantics.pst{2}).
rewrite H18 /=.
have ->: has_input FRAM.st{2}.
smt().
rewrite H0 /=.
progress.
case (has_output FRAM.st{2}); progress.
rewrite H12 //=.
rewrite step_step /=.
rewrite -H19.
rewrite (aggregate_perm_eq MapReduceSemantics.meta{2} MapReduceSemantics.pst{2} (map
     (fun (k : int) =>
        (k,
         (step
            (set_input (init_state (nth witness MapReduceSemantics.ps{2} k))
               (oget
                  (get_input
                     (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1))
     (iota_ 0 MapReduce.nprocesses))).
smt.

have H21 : perm_eq (unzip1 MapReduceSemantics.pst{2}) (unzip1 (map
     (fun (k : int) =>
        (k,
         (step
            (set_input (init_state (nth witness MapReduceSemantics.ps{2} k))
               (oget
                  (get_input
                     (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1))
     (iota_ 0 MapReduce.nprocesses))).
rewrite -map_comp /(\o) /= map_id.
done.
have H22 : forall x, x \in iota_ 0 MapReduce.nprocesses => assoc MapReduceSemantics.pst{2} x = assoc (map
     (fun (k : int) =>
        (k,
         (step
            (set_input (init_state (nth witness MapReduceSemantics.ps{2} k))
               (oget
                  (get_input
                     (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1))
     (iota_ 0 MapReduce.nprocesses)) x.
progress.
rewrite map_assoc.
done.
simplify.
rewrite -H13.
smt(@List).
smt(@List).
smt(@List).
done.
rewrite assoc_is_perm_eq.
rewrite (perm_eq_iota_uniq (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses).
done.
done.
progress.
rewrite H22.
smt(@List).
done.

done.
rewrite H6.
smt().
done.
rewrite -H19 /=.
rewrite (aggregate_perm_eq MapReduceSemantics.meta{2} MapReduceSemantics.pst{2} (map
     (fun (k : int) =>
        (k,
         (step
            (set_input (init_state (nth witness MapReduceSemantics.ps{2} k))
               (oget
                  (get_input
                     (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1))
     (iota_ 0 MapReduce.nprocesses))).
smt.

have H21 : perm_eq (unzip1 MapReduceSemantics.pst{2}) (unzip1 (map
     (fun (k : int) =>
        (k,
         (step
            (set_input (init_state (nth witness MapReduceSemantics.ps{2} k))
               (oget
                  (get_input
                     (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1))
     (iota_ 0 MapReduce.nprocesses))).
rewrite -map_comp /(\o) /= map_id.
done.
have H22 : forall x, x \in iota_ 0 MapReduce.nprocesses => assoc MapReduceSemantics.pst{2} x = assoc (map
     (fun (k : int) =>
        (k,
         (step
            (set_input (init_state (nth witness MapReduceSemantics.ps{2} k))
               (oget
                  (get_input
                     (odflt empty_state (assoc MapReduceSemantics.pst{2} k)))))).`1))
     (iota_ 0 MapReduce.nprocesses)) x.
progress.
rewrite map_assoc.
done.
simplify.
rewrite -H13.
smt(@List).
smt(@List).
smt(@List).
done.
rewrite assoc_is_perm_eq.
rewrite (perm_eq_iota_uniq (unzip1 MapReduceSemantics.pst{2}) 0 nprocesses).
done.
done.
progress.
rewrite H22.
smt(@List).
done.

done.

smt.

smt.

smt.

smt.

smt.

smt.

smt.

have : has_input MapReduceSemantics.pst{2}.
move : H17.
rewrite /has_input /has_output !allP /=.
progress.
move : (H17 x0).
rewrite H18 /=.
progress.
rewrite H10.
smt.
done.
progress.
have : has_input FRAM.st{2}.
smt().
progress.
rewrite has_output_step.
done.

smt.
smt.

skip; progress.

skip; progress.
move : H H0.
by elim (split_circuit L{2}) => //=.
move : H H0.
by elim (split_circuit L{2}) => //=.
have ->: Ps{2} = (split_circuit L{2}).`2.
move : H H0.
by elim (split_circuit L{2}) => //=.
smt.
smt().

rewrite H1.
done.
simplify.
rewrite get_circuit_has_circuitN.
done.

rewrite get_circuit_has_circuitN.
done.

move : H3.
rewrite has_input_init_state.
done.

move : H3.
rewrite /has_input /= allP /=.
progress.
move : (H3 0).
have ->: 0 \in iota_ 0 MapReduce.nprocesses by smt.
simplify.
rewrite H1 /=.
smt(nprocesses_pos).
rewrite has_input_init_state /=.
done.

move : H3.
rewrite has_input_init_state.
done.

move : H5.
rewrite H1 /=.
smt(nprocesses_pos).
rewrite has_input_init_state /=.
done.

move : H7.
rewrite H1 /=.
smt(nprocesses_pos).
rewrite has_input_init_state /=.
done.

move : H3.
rewrite has_output_init_state /=.
done.

move : H3.
rewrite has_output_init_state /=.
done.

move : H3.
rewrite /has_output /= allP /=.
progress.
move : (H3 0).
have ->: 0 \in iota_ 0 MapReduce.nprocesses by smt.
simplify.
rewrite H1 /=.
smt(nprocesses_pos).
rewrite has_output_init_state /=.
done.

move : H5.
rewrite H1 /=.
smt(nprocesses_pos).
rewrite has_output_init_state /=.
done.

rewrite H1 /=.
smt(nprocesses_pos).
rewrite has_output_init_state /=.
done.

move : H3.
rewrite has_output_init_state /=.
done.

move : H5.
rewrite H1 /=.
smt(nprocesses_pos).
rewrite has_input_init_state /=.
done.

smt.
qed.

end section Equivalence.

end MapReduce.
