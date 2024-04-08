require import AllCore List SmtMap.

from Semantics require import ALanguage.
from RAM require import FunctionalRAM.
from PRAM require import APRAM MapReduce.
from Zarith require import PrimeField.
from LPZK require import LPZK LPZKFaster.
from Utilities require import ListExt.

from RAMLPZK require import RAMLPZKFasterVerifier.

import LPZK.
import ArithmeticCircuit.
import Circuit.
import LPZKFaster.

theory PRAMVerifier.

  type meta_information_t.
  op nprocesses : int.
  axiom nprocesses_pos : 2 <= nprocesses.

  import RAMVerifier.Language.

  op split_circuit : L -> meta_information_t * L list.

  axiom split_circuit_size (L : L) : size (split_circuit L).`2 = nprocesses.
    
  op aggregate_circuit (m_cs : meta_information_t * L list) : L.

  type processorId_t = int.
  type pstate_t = (processorId_t * RAMVerifier.state_t) list.

  op aggregate (m : meta_information_t) (cs : pstate_t) : RAMVerifier.execution_info_t option.

  axiom aggregate_perm_eq meta (pst pst' : pstate_t) :
    uniq (unzip1 pst) => perm_eq pst pst' => aggregate meta pst = aggregate meta pst'.

  op has_input (pst : pstate_t) : bool =
    all (fun id => RAMVerifier.has_input (odflt RAMVerifier.empty_state (assoc pst id))) (iota_ 0 nprocesses).
  op has_output (pst : pstate_t) : bool =
    all (fun id => RAMVerifier.has_output (odflt RAMVerifier.empty_state (assoc pst id))) (iota_ 0 nprocesses).

  axiom aggregate_none meta pst :
    has_output pst <=> aggregate meta pst <> None.

  axiom aggregate_correct (meta : meta_information_t) (cs : L list) (st : RAMVerifier.state_t) (pst : pstate_t) :
    RAMVerifier.has_input st =>
    has_input pst =>
    perm_eq (unzip1 pst) (iota_ 0 nprocesses) =>
    aggregate meta (map (fun k => (k, (RAMVerifier.step (RAMVerifier.set_input (RAMVerifier.init_state (nth witness cs k)) (oget (RAMVerifier.get_input (odflt RAMVerifier.empty_state (assoc pst k)))))).`1)) (iota_ 0 nprocesses)) = (RAMVerifier.step (RAMVerifier.set_input (RAMVerifier.init_state (aggregate_circuit (meta, cs))) (oget (RAMVerifier.get_input st)))).`2.

  op get_output : meta_information_t -> pstate_t -> output_t option.

  axiom has_output_get_output (meta : meta_information_t) (pst : pstate_t) : 
    has_output pst => get_output meta pst <> None.
  axiom has_output_get_outputN (meta : meta_information_t) (pst : pstate_t) : 
    !has_output pst => get_output meta pst = None.

  axiom get_output_perm_eq (meta : meta_information_t) (pst pst' : pstate_t) :
    uniq (unzip1 pst) => perm_eq pst pst' => 
    get_output meta pst = get_output meta pst'.

  axiom get_output_none meta pst :
    get_output meta pst <> None => 
    forall (x : int), x \in iota_ 0 nprocesses => RAMVerifier.has_output (odflt RAMVerifier.empty_state (assoc pst x)).

  axiom get_output_correct (meta : meta_information_t) (cs : L list) (st : RAMVerifier.state_t) (pst : pstate_t) :
    size cs = nprocesses =>
    RAMVerifier.has_input st =>
    has_input pst =>
    (forall k, 0 <= k < nprocesses => 
      RAMVerifier.get_input (odflt RAMVerifier.empty_state (assoc pst k)) = RAMVerifier.get_input st) =>
    (forall k, 0 <= k < nprocesses => 
      RAMVerifier.get_circuit (odflt RAMVerifier.empty_state (assoc pst k)) = Some (nth witness cs k)) =>
    RAMVerifier.get_circuit st = Some (aggregate_circuit (meta, cs)) =>
    get_output meta (map (fun k => (k, (RAMVerifier.step (RAMVerifier.set_input (RAMVerifier.init_state (nth witness cs k)) (oget (RAMVerifier.get_input (odflt RAMVerifier.empty_state (assoc pst k)))))).`1)) (iota_ 0 nprocesses)) = 

    RAMVerifier.get_output (RAMVerifier.step (RAMVerifier.set_input (RAMVerifier.init_state (aggregate_circuit (meta, cs))) (oget (RAMVerifier.get_input st)))).`1.

  clone import MapReduce with
    theory Language = RAMVerifier.Language,
    type execution_info_t = RAMVerifier.execution_info_t,
    type output_event_t = RAMVerifier.output_event_t,
    type meta_information_t = meta_information_t,
    op nprocesses = nprocesses,

    (* functional RAM instantiation *)
    type FunctionalRAM.state_t = RAMVerifier.state_t,
    op FunctionalRAM.empty_state = RAMVerifier.empty_state,
    op FunctionalRAM.init_state = RAMVerifier.init_state,
    op FunctionalRAM.set_input = RAMVerifier.set_input,
    op FunctionalRAM.step = RAMVerifier.step,
    op FunctionalRAM.get_input = RAMVerifier.get_input,
    op FunctionalRAM.get_output = RAMVerifier.get_output,
    op FunctionalRAM.get_circuit = RAMVerifier.get_circuit,
    op FunctionalRAM.has_input = RAMVerifier.has_input,
    op FunctionalRAM.has_output = RAMVerifier.has_output,
    op FunctionalRAM.has_circuit = RAMVerifier.has_circuit,

    op split_circuit = split_circuit,
    op aggregate_circuit = aggregate_circuit,
    op aggregate = aggregate,
    op get_output = get_output,
    op has_input = has_input,
    op has_output = has_output
  proof *.
  realize FunctionalRAM.has_input_empty_state by smt().
  realize FunctionalRAM.has_circuit_empty_state by smt().
  realize FunctionalRAM.has_output_empty_state by smt().
  realize FunctionalRAM.has_circuit_init_state by smt().
  realize FunctionalRAM.has_circuit_get_circuit by smt().
  realize FunctionalRAM.has_circuit_get_circuitN by smt().
  realize FunctionalRAM.get_circuit_has_circuitN by smt().
  realize FunctionalRAM.get_circuit_set_input by smt().
  realize FunctionalRAM.get_circuit_step by smt().
  realize FunctionalRAM.has_input_get_input by smt().
  realize FunctionalRAM.has_input_get_inputN by smt().
  realize FunctionalRAM.has_input_set_input by smt().
  realize FunctionalRAM.get_input_set_input by smt().
  realize FunctionalRAM.has_input_step by smt().
  realize FunctionalRAM.get_input_step by smt().
  realize FunctionalRAM.has_output_step by smt().
  realize FunctionalRAM.step_has_inputN by smt().
  realize FunctionalRAM.step_step by smt().
  realize FunctionalRAM.has_output_set_input by smt().
  realize FunctionalRAM.has_output_get_output by smt().
  realize FunctionalRAM.has_output_get_outputN by smt().
  realize FunctionalRAM.set_input_set_input by smt().
  realize FunctionalRAM.has_input_init_state by smt().
  realize FunctionalRAM.has_output_init_state by smt().
  realize nprocesses_pos by smt(nprocesses_pos).
  realize split_circuit_size by smt(split_circuit_size).
  realize aggregate_perm_eq by smt(aggregate_perm_eq).
  realize aggregate_none by smt(aggregate_none).
  realize has_output_get_output by smt(has_output_get_output).
  realize has_output_get_outputN by smt(has_output_get_outputN).
  realize get_output_perm_eq by smt(get_output_perm_eq).
  realize get_output_none by smt(get_output_none).
  realize aggregate_correct by progress; move : (aggregate_correct meta cs st pst H H0 H1). 
  realize get_output_correct. 
    progress; move : (get_output_correct meta cs st pst).
    rewrite H /MapReduce.nprocesses /=.
    move : H0; rewrite /FunctionalRAM.has_input /= => H0; rewrite H0 /=.
    move : H1; rewrite /MapReduce.has_input /= => H1; rewrite H1 /=.
    have ->: (forall (k : int), 0 <= k && k < PRAMVerifier.nprocesses =>
                                RAMVerifier.get_input (odflt RAMVerifier.empty_state (assoc pst k)) = RAMVerifier.get_input st) <=> 
                                true by done.
    have ->:  (forall (k : int), 0 <= k && k < PRAMVerifier.nprocesses =>
                                 RAMVerifier.get_circuit (odflt RAMVerifier.empty_state (assoc pst k)) = 
                                   Some (nth witness cs k)) <=> true by done.
    by move : H4; rewrite /FunctionalRAM.get_circuit /= => H4; rewrite H4 /=.
  qed.

  print parallel_sequential_equivalence.

end PRAMVerifier.
