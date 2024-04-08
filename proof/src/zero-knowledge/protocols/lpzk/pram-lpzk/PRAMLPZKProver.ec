(**
  Formalization of the list-based LPZK prover on top of the PRAM model. Briefly, this file
  implements the LPZK prover as a RAM machine, following the PRAM formalization given in
  file *APRAM.ec*, yielding a parallel implementation of the list-based LPZK prover.

  The inputs of the PRAM prover are the witness, statement and the required randomness to compute
  the commitment. Then, the PRAM prover starts by splitting the circuit into **nprocesses**
  smaller, independent, circuits. This circuits are then given to different parallel processes
  to be evaluated by them using [step], with each parallel core computing the corresponding
  [z] structure. At the end, [get_output] aggregates the all [z] produced by the cores into
  a single [z] structure, according to the circuit meta data produced when the circuit is 
  splitted.
*)
require import AllCore List SmtMap.

from Semantics require import ALanguage.
from RAM require import FunctionalRAM.
from PRAM require import APRAM MapReduce.
from Zarith require import PrimeField.
from LPZK require import LPZK.
from Utilities require import ListExt Array.

from RAMLPZK require import RAMLPZKProver.

import LPZK.
import ArithmeticCircuit.
import Circuit.

theory PRAMProver.

  (** In a parallel execution, the original program (or circuit) is split into *smaller* 
      programs (or circuits) and each one of them is given to a core to be computed. The 
      **meta_information_t** type will store auxiliar data allows the reconstruction of the
      original program (or circuit) and also to aggregate the outputs of the parallel cores
      into a single output value *)
  type meta_information_t = topology_t * output_wires_t.
  (** Number of parallel cores *)
  op nprocesses : int.

  import RAMProver.
  import Language.

  (** Assumes that at least two parallel cores exist *)
  axiom nprocesses_pos (c : L) : 1 <= nprocesses /\ nprocesses = size c.`out_wires.

  (** Splits a circuit into **nprocesses** smaller circuits *)
  op split_circuit (c : L) : meta_information_t * L list =
    let ys = c.`out_wires in
    let topo = c.`topo in
    let gg = c.`gates in

    ((topo, ys), map (fun y => {| topo = topo ; 
                                  gates = oget (get_gate gg y) ; 
                                  out_wires = [y] |}) ys).
  
  (** Ensures that the circuit is split into **nprocesses** smaller circuits *)
  lemma split_circuit_size (L : L) : size (split_circuit L).`2 = nprocesses.
  proof. by rewrite /split_circuit /= size_map (nprocesses_pos L). qed.

  (** Aggregates the small circuits into one big circuit *)
  op aggregate_circuit (m_cs : meta_information_t * L list) : L =
    let (m, cs) = m_cs in
    let (topo, ys) = m in
    let id = topo.`ngates - topo.`noutputs in
    let hd = (head witness cs).`gates in
    let reconstruct = foldl (fun st c => let (i, acc) = st in
                                         (i+1, Addition i acc c.`gates)) (id, hd) cs in
    {| topo = topo ; gates = snd reconstruct ; out_wires = ys |}.

  (** Processes are indexed by integers in the [0; nprocesses[ range *)
  type processorId_t = int.

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

  (** Aggregates the outputs of the parallel cores *)
  op aggregate (m : meta_information_t) (cs : pstate_t) : execution_info_t option =
    if has_output cs then
      let (topo, ys) = m in
      let c_0 = oget (oget (assoc cs 0)).`zo in
      let id = topo.`ngates - topo.`noutputs in
      let reorganize = map (fun id => (id, oget (assoc cs id))) (iota_ 0 nprocesses) in
      let aggregation = foldl (fun st c => let (i, acc) = st in
                                           let (id, com) = c in
                                           (i+1, 
                                            AdditionZ i {| m = fzero; m' = fzero; c = fzero; |} 
                                                        acc (oget com.`zo))) 
            (id, c_0) reorganize in
      Some (snd aggregation)
    else None.

  (** Ensures that aggregate is order-agnostic *)
  lemma aggregate_perm_eq meta (pst pst' : pstate_t) :
    uniq (unzip1 pst) => perm_eq pst pst' => 
    aggregate meta pst = aggregate meta pst'.
  proof.
    progress; rewrite /aggregate /=.
    have : uniq (unzip1 pst') by smt(@List).
    progress.
    have ->: (fun (st : int * z_t) (c : processorId_t * state_t) =>
           let (i, acc) = st in
           let (_, com) = c in
           (i + 1,
            AdditionZ i {| m = fzero; m' = fzero; c = fzero; |} acc
              (oget com.`zo))) = 
            (fun (st : int * z_t) (c : processorId_t * state_t) =>
           (st.`1 + 1,
            AdditionZ st.`1 {| m = fzero; m' = fzero; c = fzero; |} st.`2
              (oget c.`2.`zo))) by smt().
    case (has_output pst); progress; last first.
      have ->: !has_output pst'.
        move : H2; rewrite /has_output /= !allP.
        have ->: ! (forall (x : processorId_t),
                      x \in iota_ 0 nprocesses =>
                      (fun (id : processorId_t) =>
                        (odflt empty_state (assoc pst id)).`zo <> None) x) 
                        <=> 
                      (exists (x : processorId_t),
                        !(x \in iota_ 0 nprocesses =>
                         (fun (id : processorId_t) =>
                        (odflt empty_state (assoc pst id)).`zo <> None) x))
          by smt().
        progress.
        have ->: ! (forall (x : processorId_t),
                      x \in iota_ 0 nprocesses =>
                      (fun (id : processorId_t) =>
                        (odflt empty_state (assoc pst' id)).`zo <> None) x) 
                        <=> 
                      (exists (x : processorId_t),
                        !(x \in iota_ 0 nprocesses =>
                         (fun (id : processorId_t) =>
                        (odflt empty_state (assoc pst' id)).`zo <> None) x))
          by smt().
        progress.
        by exists x; have ->: assoc pst' x = assoc pst x by rewrite (perm_eq_assoc pst pst').
      by simplify.
    have ->: has_output pst'.
      move : H2; rewrite /has_output /= !allP; progress.
      move : (H2 x); rewrite H3 /=; progress.
      by have ->: assoc pst' x = assoc pst x by rewrite (perm_eq_assoc pst pst').
    simplify; elim meta => topo ys /=.
    have ->: assoc pst' 0 = assoc pst 0 by rewrite (perm_eq_assoc pst' pst 0); smt(@List).
    congr. congr.
    rewrite -eq_in_map; progress.
     by rewrite (perm_eq_assoc pst' pst x); smt(@List).
  qed.

  (** Ensures that, if the PRAM evaluation has output, then aggregating must produce an output *)
  lemma aggregate_none meta pst :
    has_output pst <=> aggregate meta pst <> None.
  proof.
    split; progress.
    rewrite /aggregate /= H /=; first by elim meta => topo ys /=.
    move : H; rewrite /aggregate /=.
    by case (has_output pst). 
  qed.

  (** Correctness of **aggregate**: if all parallel cores follow the FRAM step-based syntax, then
      **aggregate** produces the same output of the sequential evaluation *)
  axiom foldl_assumption (topo : topology_t) (cs : circuit_t list) (ys : output_wires_t)
                         (pst : pstate_t) (st : state_t) :
    (foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (gen_z (oget (odflt empty_state (assoc pst x)).`r) (add_final_mul (nth witness cs x)).`gates (oget (odflt empty_state (assoc pst x)).`inst) (oget (odflt empty_state (assoc pst x)).`w)))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (nth witness cs 0)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses)).`2 =
    gen_z (oget st.`r) (add_final_mul {| topo = topo; gates = (foldl (fun (st0 : int * ArithmeticCircuit.gates_t) (c : circuit_t) => (st0.`1 + 1, Addition st0.`1 st0.`2 c.`gates)) (topo.`ngates - topo.`noutputs, (nth witness cs 0).`gates) cs).`2; out_wires = ys; |}).`gates (oget st.`inst) (oget st.`w).

  lemma aggregate_correct (meta : meta_information_t) (cs : L list) 
                          (st : state_t) (pst : pstate_t) :
    has_input st =>
    has_input pst =>
    perm_eq (unzip1 pst) (iota_ 0 nprocesses) =>
    aggregate meta (map (fun k => (k, (step (set_input (init_state (nth witness cs k)) (oget (get_input (odflt empty_state (assoc pst k)))))).`1)) (iota_ 0 nprocesses)) = (step (set_input (init_state (aggregate_circuit (meta, cs))) (oget (get_input st)))).`2.
  proof.
    rewrite /has_input allP /=; progress.
    rewrite /aggregate /=.
    have ->: has_output (map (fun (k : int) => (k, ((step ((set_input ((init_state (nth witness cs k))) (oget ((get_input (odflt empty_state (assoc pst k))))))))).`1)) (iota_ 0 nprocesses)).
      rewrite /has_output /= allP; progress.
      rewrite map_assoc //= /set_input /= /get_input /=.
      move : (H2 x).
      rewrite H4 /=; progress.
      by rewrite H5 H6 H7 /= /init_state /= /empty_state /= /step /= /has_input /=.
    simplify; elim meta => topo ys /=.
    rewrite map_assoc /=; first by rewrite mem_iota; smt(nprocesses_pos).
    have ->: oget (step (set_input (init_state (nth witness cs 0)) (oget (get_input (odflt empty_state (assoc pst 0)))))).`1.`zo = gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w).
      rewrite /set_input /= /get_input /=.
      have ->: (odflt empty_state (assoc pst 0)).`w <> None by
        move : (H2 0); have ->: 0 \in iota_ 0 nprocesses by rewrite mem_iota; smt(nprocesses_pos).
      have ->: (odflt empty_state (assoc pst 0)).`r <> None by
        move : (H2 0); have ->: 0 \in iota_ 0 nprocesses by rewrite mem_iota; smt(nprocesses_pos).
      have ->: (odflt empty_state (assoc pst 0)).`inst <> None by
        move : (H2 0); have ->: 0 \in iota_ 0 nprocesses by rewrite mem_iota; smt(nprocesses_pos).
      simplify.
      rewrite /step /=.
      by have ->: has_input
              {| circ = (init_state (nth witness cs 0)).`circ; w =
                  Some (oget (odflt empty_state (assoc pst 0)).`w); r =
                  Some (oget (odflt empty_state (assoc pst 0)).`r); inst =
                  Some (oget (odflt empty_state (assoc pst 0)).`inst); zo =
                  (init_state (nth witness cs 0)).`zo; |} by rewrite /has_input /=.
    have ->: (map (fun (id : processorId_t) => (id, oget (assoc (map (fun (k : int) => (k, (step (set_input (init_state (nth witness cs k)) (oget (get_input (odflt empty_state (assoc pst k)))))).`1)) (iota_ 0 nprocesses)) id))) (iota_ 0 nprocesses)) = (List.map (fun (id : processorId_t) => (id, oget (Some (step (set_input (init_state (nth witness cs id)) (oget (get_input (odflt empty_state (assoc pst id)))))).`1)))) (iota_ 0 nprocesses) by rewrite -eq_in_map; progress; rewrite map_assoc.
    have ->:  (fun (st0 : int * z_t) (c : processorId_t * state_t) => let (i, acc) = st0 in let (_, com) = c in (i + 1, AdditionZ i {| m = fzero; m' = fzero; c = fzero; |} acc (oget com.`zo))) = (fun (st0 : int * z_t) (c : processorId_t * state_t) => (st0.`1 + 1, AdditionZ st0.`1 {| m = fzero; m' = fzero; c = fzero; |} st0.`2 (oget c.`2.`zo))) by rewrite fun_ext /(==); progress => /#.
    simplify; rewrite foldl_map //= /step /=.
    have ->: (foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (oget (if has_input (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))) then ({| circ = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ; w = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w; r = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r; inst = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst; zo = Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)); |}, Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w))) else (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x)))), None)).`1.`zo))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses)).`2 = 
             (foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (oget ( ({| circ = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ; w = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w; r = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r; inst = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst; zo = Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input(odflt empty_state (assoc pst x))))).`w)); |}, Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)))).`1.`zo))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses)).`2.
      rewrite (eq_in_foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (oget (if has_input (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))) then ({| circ = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ; w = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w; r = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r; inst = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst; zo = Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)); |}, Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w))) else (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x)))), None)).`1.`zo))) (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (oget ( ({| circ = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ; w = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w; r = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r; inst = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst; zo = Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input(odflt empty_state (assoc pst x))))).`w)); |}, Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)))).`1.`zo))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses) (iota_ 0 nprocesses)) //=.
        progress. 
        by have ->: has_input (set_input (init_state (nth witness cs y)) (oget (get_input (odflt empty_state (assoc pst y))))) by rewrite /has_input /= /set_input => /#.
    simplify.
    have ->: Some (foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses)).`2 = 
             Some (foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (gen_z (oget (odflt empty_state (assoc pst x)).`r) (add_final_mul (oget (init_state (nth witness cs x)).`circ)).`gates (oget (odflt empty_state (assoc pst x)).`inst) (oget (odflt empty_state (assoc pst x)).`w)))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses)).`2.
      rewrite (eq_in_foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)))) (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (gen_z (oget (odflt empty_state (assoc pst x)).`r) (add_final_mul (oget (init_state (nth witness cs x)).`circ)).`gates (oget (odflt empty_state (assoc pst x)).`inst) (oget (odflt empty_state (assoc pst x)).`w)))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses) (iota_ 0 nprocesses)) //=.
        progress.
        by rewrite /set_input /= /get_input /= H2.
    have ->: has_input (set_input (init_state (aggregate_circuit ((topo, ys), cs))) (oget (get_input st))) by smt().
    simplify.
    rewrite /set_input /= /get_input /= H H0 H1 /= /init_state /= /aggregate_circuit /=.
    have ->: (fun (st0 : int * ArithmeticCircuit.gates_t) (c : circuit_t) => let (i, acc) = st0 in (i + 1, Addition i acc c.`gates)) = (fun (st0 : int * ArithmeticCircuit.gates_t) (c : circuit_t) => (st0.`1 + 1, Addition st0.`1 st0.`2 c.`gates)).
      rewrite fun_ext /(==); progress.
      rewrite fun_ext /(==); progress.
      by smt().
    simplify.
    have ->: (head witness cs).`gates = (nth witness cs 0).`gates by smt(@List).
    by rewrite (foldl_assumption topo cs ys pst st).
  qed.

  (** Collects output from the parallel state *)
  op get_output (meta : meta_information_t) (pst : pstate_t) : output_t option =
    if has_output pst then
      let z = oget (aggregate meta pst) in
      let c = aggregate_circuit (meta, map (fun id => oget (odflt empty_state (assoc pst id)).`circ) (iota_ 0 nprocesses)) in
      let r = oget (odflt empty_state (assoc pst 0)).`r in
      Some (z, get_a r c.`gates)
    else None.


  (** Establishes that if the parallel state has output, then the **get_output** operation must 
      produce an output *)
  lemma has_output_get_output (meta : meta_information_t) (pst : pstate_t) : has_output pst => get_output meta pst <> None.
  proof. by rewrite /has_output /=; progress; rewrite /get_output /= /has_output /= H. qed.

  (** Establishes that if the parallel state doesn't have output, then the **get_output** 
      operation must not produce an output *)
  lemma has_output_get_outputN (meta : meta_information_t) (pst : pstate_t) : !has_output pst => get_output meta pst = None.
  proof. by rewrite /has_output /=; progress; rewrite /get_output /= /has_output /= H. qed.

  (** Ensures that **get_output** is order agnostic *)
  lemma get_output_perm_eq (meta : meta_information_t) (pst pst' : pstate_t) :
    uniq (unzip1 pst) => perm_eq pst pst' => get_output meta pst = get_output meta pst'.
  proof.
    progress.
    have : uniq (unzip1 pst') by smt(@List).
    progress.
    rewrite /get_output /=.
    case (has_output pst); progress; last first.
      have : ! has_output pst'.
        move : H2; rewrite /has_output /= !allP.
        have ->: ! (forall (x : processorId_t),
                      x \in iota_ 0 nprocesses =>
                      (fun (id : processorId_t) =>
                        (odflt empty_state (assoc pst id)).`zo <> None) x) 
                        <=> 
                      (exists (x : processorId_t),
                        !(x \in iota_ 0 nprocesses =>
                         (fun (id : processorId_t) =>
                        (odflt empty_state (assoc pst id)).`zo <> None) x))
          by smt().
        progress.
        have ->: ! (forall (x : processorId_t),
                      x \in iota_ 0 nprocesses =>
                      (fun (id : processorId_t) =>
                        (odflt empty_state (assoc pst' id)).`zo <> None) x) 
                        <=> 
                      (exists (x : processorId_t),
                        !(x \in iota_ 0 nprocesses =>
                         (fun (id : processorId_t) =>
                        (odflt empty_state (assoc pst' id)).`zo <> None) x))
          by smt().
        progress.
        by exists x; have ->: assoc pst' x = assoc pst x by rewrite (perm_eq_assoc pst pst').
      by progress; rewrite H3 /=.
    have ->: has_output pst'.
      move : H2; rewrite /has_output /= !allP; progress.
      move : (H2 x); rewrite H3 /=; progress.
      by have ->: assoc pst' x = assoc pst x by rewrite (perm_eq_assoc pst pst').
    simplify; split.
      by rewrite (aggregate_perm_eq meta pst pst').
    have ->: assoc pst 0 = assoc pst' 0.
      by rewrite (perm_eq_assoc pst pst' 0).
    do congr.
    rewrite fun_ext /(==); progress.
    by rewrite (perm_eq_assoc pst pst' x).
  qed.

  (** Establishes that if the parallel state has output, then the all parallel cores have 
      output *)
  lemma get_output_none meta pst :
    get_output meta pst <> None => 
    forall (x : int), x \in iota_ 0 nprocesses => has_output (odflt empty_state (assoc pst x)).
  proof.
    rewrite /get_output /=; progress.
    have : has_output pst by smt().
    rewrite /has_output /= allP; progress.
    move : (H1 x).
    by rewrite H0.
  qed.

  (** Equivalence between the RAM **get_output** and the PRAM **get_output** operators *)
  lemma get_output_correct (meta : meta_information_t) (cs : L list) (st : state_t) (pst : pstate_t) :
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
  proof.
    rewrite /get_circuit /= /has_input allP /=; progress.
    rewrite /get_output /=.
    have H7 : has_output (map (fun (k : int) => (k, (step (set_input (init_state (nth witness cs k)) (oget (get_input (odflt empty_state (assoc pst k)))))).`1)) (iota_ 0 nprocesses)).
      rewrite /has_output /= allP; progress.
      by rewrite map_assoc //= /#.
    rewrite H7 /=.
    have -> : (step (set_input (init_state (aggregate_circuit (meta, cs))) (oget (get_input st)))).`1.`zo <> None by smt().
    simplify.
    rewrite !map_assoc /=; first by rewrite mem_iota; smt(nprocesses_pos).
    have ->: map (fun (id : processorId_t) => oget (odflt empty_state (assoc (map (fun (k : int) => (k, (step (set_input (init_state (nth witness cs k)) (oget (get_input (odflt empty_state (assoc pst k)))))).`1)) (iota_ 0 nprocesses)) id)).`circ) (iota_ 0 nprocesses) = map (fun (id : processorId_t) => oget (odflt empty_state (Some ((step (set_input (init_state (nth witness cs id)) (oget (get_input (odflt empty_state (assoc pst id)))))).`1))).`circ) (iota_ 0 nprocesses)
      by rewrite -eq_in_map; progress; rewrite map_assoc //=.
    simplify; split.
      move : H6; elim meta => topo ys /=.
      progress.
      have ->: oget (aggregate (topo, ys) (map (fun (k : int) => (k, (step (set_input (init_state (nth witness cs k)) (oget (get_input (odflt empty_state (assoc pst k)))))).`1)) (iota_ 0 nprocesses))) =               
               (foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (gen_z (oget (odflt empty_state (assoc pst x)).`r) (add_final_mul (nth witness cs x)).`gates (oget (odflt empty_state (assoc pst x)).`inst) (oget (odflt empty_state (assoc pst x)).`w)))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (nth witness cs 0)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses)).`2.
        rewrite /aggregate /= H7 /=.
        rewrite map_assoc /=; first by rewrite mem_iota; smt(nprocesses_pos).
        have ->: oget (step (set_input (init_state (nth witness cs 0)) (oget (get_input (odflt empty_state (assoc pst 0)))))).`1.`zo = gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w).
          rewrite /set_input /= /get_input /=.
          have ->: (odflt empty_state (assoc pst 0)).`w <> None by
            move : (H3 0); have ->: 0 \in iota_ 0 nprocesses by rewrite mem_iota; smt(nprocesses_pos).
          have ->: (odflt empty_state (assoc pst 0)).`r <> None by
            move : (H3 0); have ->: 0 \in iota_ 0 nprocesses by rewrite mem_iota; smt(nprocesses_pos).
          have ->: (odflt empty_state (assoc pst 0)).`inst <> None by
            move : (H3 0); have ->: 0 \in iota_ 0 nprocesses by rewrite mem_iota; smt(nprocesses_pos).
          simplify.
          rewrite /step /=.
          by have ->: has_input
                  {| circ = (init_state (nth witness cs 0)).`circ; w =
                      Some (oget (odflt empty_state (assoc pst 0)).`w); r =
                      Some (oget (odflt empty_state (assoc pst 0)).`r); inst =
                      Some (oget (odflt empty_state (assoc pst 0)).`inst); zo =
                      (init_state (nth witness cs 0)).`zo; |} by rewrite /has_input /=.
        have ->: (map (fun (id : processorId_t) => (id, oget (assoc (map (fun (k : int) => (k, (step (set_input (init_state (nth witness cs k)) (oget (get_input (odflt empty_state (assoc pst k)))))).`1)) (iota_ 0 nprocesses)) id))) (iota_ 0 nprocesses)) = (List.map (fun (id : processorId_t) => (id, oget (Some (step (set_input (init_state (nth witness cs id)) (oget (get_input (odflt empty_state (assoc pst id)))))).`1)))) (iota_ 0 nprocesses) by rewrite -eq_in_map; progress; rewrite map_assoc.
        have ->:  (fun (st0 : int * z_t) (c : processorId_t * state_t) => let (i, acc) = st0 in let (_, com) = c in (i + 1, AdditionZ i {| m = fzero; m' = fzero; c = fzero; |} acc (oget com.`zo))) = (fun (st0 : int * z_t) (c : processorId_t * state_t) => (st0.`1 + 1, AdditionZ st0.`1 {| m = fzero; m' = fzero; c = fzero; |} st0.`2 (oget c.`2.`zo))) by rewrite fun_ext /(==); progress => /#.
        simplify; rewrite foldl_map //= /step /=.
        have ->: (foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (oget (if has_input (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))) then ({| circ = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ; w = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w; r = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r; inst = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst; zo = Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)); |}, Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w))) else (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x)))), None)).`1.`zo))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses)).`2 = 
                 (foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (oget ( ({| circ = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ; w = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w; r = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r; inst = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst; zo = Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input(odflt empty_state (assoc pst x))))).`w)); |}, Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)))).`1.`zo))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses)).`2.
          rewrite (eq_in_foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (oget (if has_input (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))) then ({| circ = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ; w = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w; r = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r; inst = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst; zo = Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)); |}, Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w))) else (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x)))), None)).`1.`zo))) (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (oget ( ({| circ = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ; w = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w; r = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r; inst = (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst; zo = Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input(odflt empty_state (assoc pst x))))).`w)); |}, Some (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)))).`1.`zo))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses) (iota_ 0 nprocesses)) //=.
            progress. 
            by have ->: has_input (set_input (init_state (nth witness cs y)) (oget (get_input (odflt empty_state (assoc pst y))))) by rewrite /has_input /= /set_input => /#.
        simplify.
        have ->: (foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses)).`2 = 
                 (foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (gen_z (oget (odflt empty_state (assoc pst x)).`r) (add_final_mul (oget (init_state (nth witness cs x)).`circ)).`gates (oget (odflt empty_state (assoc pst x)).`inst) (oget (odflt empty_state (assoc pst x)).`w)))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses)).`2.
          rewrite (eq_in_foldl (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (gen_z (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`r) (add_final_mul (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`circ)).`gates (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`inst) (oget (set_input (init_state (nth witness cs x)) (oget (get_input (odflt empty_state (assoc pst x))))).`w)))) (fun (z : int * z_t) (x : processorId_t) => (z.`1 + 1, AdditionZ z.`1 {| m = fzero; m' = fzero; c = fzero; |} z.`2 (gen_z (oget (odflt empty_state (assoc pst x)).`r) (add_final_mul (oget (init_state (nth witness cs x)).`circ)).`gates (oget (odflt empty_state (assoc pst x)).`inst) (oget (odflt empty_state (assoc pst x)).`w)))) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (topo.`ngates - topo.`noutputs, gen_z (oget (odflt empty_state (assoc pst 0)).`r) (add_final_mul (oget (init_state (nth witness cs 0)).`circ)).`gates (oget (odflt empty_state (assoc pst 0)).`inst) (oget (odflt empty_state (assoc pst 0)).`w)) (iota_ 0 nprocesses) (iota_ 0 nprocesses)) //=.
            progress.
            by rewrite /set_input /= /get_input /= H3.
        by rewrite /init_state /=.
      rewrite /step /= /has_input /= /set_input /= /get_input /= !H0 !H1 !H2 /= 
              (foldl_assumption topo cs ys pst st) /init_state /= /aggregate_circuit /=.
      do congr.
        rewrite fun_ext /(==); progress.
        rewrite fun_ext /(==); progress.
        by smt().
        by smt(@List).
    rewrite H4 /=; first by smt(nprocesses_pos).
    congr; first by smt().
    have ->: (oget (step (set_input (init_state (aggregate_circuit (meta, cs))) (oget (get_input st)))).`1.`circ).`gates = (aggregate_circuit (meta, cs)).`gates
      by rewrite /step /set_input /get_input /init_state /= !H0 !H1 !H2 /= /has_input /=.
    do congr.
    rewrite (eq_from_nth witness (map (fun (id : processorId_t) => oget (step (set_input (init_state (nth witness cs id)) (oget (get_input (odflt empty_state (assoc pst id)))))).`1.`circ) (iota_ 0 nprocesses)) cs) //=.
      rewrite size_map size_iota lez_maxr; first by smt(nprocesses_pos).
      by smt().
    rewrite size_map size_iota lez_maxr; first by smt(nprocesses_pos).
    progress.
    rewrite (nth_map witness witness _ _ _) //=. 
      by rewrite size_iota lez_maxr //=; first by smt(nprocesses_pos).
    rewrite nth_iota //=.
    rewrite /step /set_input /init_state /get_input /=.
    have ->: (odflt empty_state (assoc pst i)).`w <> None by
      move : (H3 i); have ->: i \in iota_ 0 nprocesses by rewrite mem_iota; smt(nprocesses_pos).
    have ->: (odflt empty_state (assoc pst i)).`r <> None by
      move : (H3 i); have ->: i \in iota_ 0 nprocesses by rewrite mem_iota; smt(nprocesses_pos).
    have ->: (odflt empty_state (assoc pst i)).`inst <> None by
      move : (H3 i); have ->: i \in iota_ 0 nprocesses by rewrite mem_iota; smt(nprocesses_pos).
    simplify.
    by rewrite /has_input /=.
  qed.

  (** Instantiaton of the generic map-reduce library with the PRAM list-based prover *)
  clone import MapReduce with
    theory Language = Language,
    type execution_info_t = execution_info_t,
    type output_event_t = output_event_t,
    type meta_information_t = meta_information_t,
    op nprocesses = nprocesses,

    (* functional RAM instantiation *)
    type FunctionalRAM.state_t = RAMLPZKProver.RAMProver.state_t,
    op FunctionalRAM.empty_state = RAMLPZKProver.RAMProver.empty_state,
    op FunctionalRAM.init_state = RAMLPZKProver.RAMProver.init_state,
    op FunctionalRAM.set_input = RAMLPZKProver.RAMProver.set_input,
    op FunctionalRAM.step = RAMLPZKProver.RAMProver.step,
    op FunctionalRAM.get_input = RAMLPZKProver.RAMProver.get_input,
    op FunctionalRAM.get_output = RAMLPZKProver.RAMProver.get_output,
    op FunctionalRAM.get_circuit = RAMLPZKProver.RAMProver.get_circuit,
    op FunctionalRAM.has_input = RAMLPZKProver.RAMProver.has_input,
    op FunctionalRAM.has_output = RAMLPZKProver.RAMProver.has_output,
    op FunctionalRAM.has_circuit = RAMLPZKProver.RAMProver.has_circuit,

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
    have ->: (forall (k : int), 0 <= k && k < PRAMProver.nprocesses =>
                                get_input (odflt empty_state (assoc pst k)) = get_input st) <=> 
                                true by done.
    have ->:  (forall (k : int), 0 <= k && k < PRAMProver.nprocesses =>
                                 get_circuit (odflt empty_state (assoc pst k)) = 
                                   Some (nth witness cs k)) <=> true by done.
    by move : H4; rewrite /FunctionalRAM.get_circuit /= => H4; rewrite H4 /=.
  qed.

  (** Because the secure equivalence between the RAM (sequential) and PRAM (parallel) 
      implementations was done *once and for all* inside our **MapReduce** library, we simply
      print the result instantiated with the RAM and PRAM LPZK *)
  print parallel_sequential_equivalence.

end PRAMProver.
