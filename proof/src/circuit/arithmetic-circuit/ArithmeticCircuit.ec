(**
  Arithmetic circuit definition, where the actual gates that form the circuit, are modeled as an 
  inductive tree, where the output of the circuit is given by the gate at the root of the tree, 
  nodes correspond to arithmetic gates, and the input and constant gates form the leaves.

  We choice to formalize the representation of gates via an inductive tree to reduce the effort
  of the verification process, since we could use induction techniques in our proof scripts. 
  However, we understand that this is not the most suitable format if one is targeting efficiency.

  Our arithmetic circuit definition is a direct instantiation of the abstract circuit syntax
  disclosed by the *ACircuit.ec* file and should serve as guide for future definitions of other
  types of circuits.
*)
require import Int List.

from Circuit require import ACircuit.
from Utilities require import Array.

(** We will use the generic field formalization in the *PrimeField.ec* file to define the type
    of circuit wires *)
from Zarith require import PrimeField.

theory ArithmeticCircuit.

  (** Wires are elements of a finite field, specified by the type **t** *)
  type wire_t = t.
  (** Converstion to boolean is simply done by checking if the field value is zero or different
      than zero *)
  op wire_to_bool (w : wire_t) : bool = if w = fzero then false else true.

  (** Wires will be indexed by integer values *)
  type wid_t = int.
  (** Gates will be indexed by integer values *)
  type gid_t = int.

  (** Inductive tree definition of the circuit gates. We consider the following gates:
        - PInput         - public input gate, with the corresponding wire ID 
        - SInput         - secret input gate, with the corresponding wire ID
        - Constant       - constant gate, with the corresponding gate ID and constant
        - Addition       - addition gate, with the corresponding gate ID, the left wire and
        the right wire
        - Multiplication - addition gate, with the corresponding gate ID, the left wire and
        the right wire *)
  type gates_t = [
    | PInput of wid_t
    | SInput of wid_t
    | Constant of gid_t & t (* all constant values of the circuit must be given via this gate *)
    | Addition of gid_t & gates_t & gates_t
    | Multiplication of gid_t & gates_t & gates_t
  ].

  (** Predicate that checks if the wire is a public input gate *)
  op is_pinput (g : gates_t) : bool =
    with g = PInput _ => true
    with g = SInput _ => false
    with g = Constant _ _ => false
    with g = Addition _ _ _ => false
    with g = Multiplication _ _ _ => false.
  (** Extracts the contents of a public input gate (the corresponding wire ID) *)
  op as_pinput (g : gates_t) : int =
    with g = PInput w => w
    with g = SInput _ => witness
    with g = Constant _ _ => witness
    with g = Addition _ _ _ => witness
    with g = Multiplication _ _ _ => witness.

  (** Predicate that checks if the wire is a secret input gate *)
  op is_sinput (g : gates_t) : bool =
    with g = PInput _ => false
    with g = SInput _ => true
    with g = Constant _ _ => false
    with g = Addition _ _ _ => false
    with g = Multiplication _ _ _ => false.
  (** Extracts the contents of a secret input gate (the corresponding wire ID) *)
  op as_sinput (g : gates_t) : int =
    with g = PInput _ => witness
    with g = SInput w => w
    with g = Constant _ _ => witness
    with g = Addition _ _ _ => witness
    with g = Multiplication _ _ _ => witness.

  (** Predicate that checks if the wire is a constant gate *)
  op is_constant (g : gates_t) : bool =
    with g = PInput _ => false
    with g = SInput _ => false
    with g = Constant _ _ => true
    with g = Addition _ _ _ => false
    with g = Multiplication _ _ _ => false.
  (** Extracts the contents of a constant gate (the corresponding wire ID and the field value) *)
  op as_constant (g : gates_t) : int * t =
    with g = PInput _ => witness
    with g = SInput _ => witness
    with g = Constant gid c => (gid, c)
    with g = Addition _ _ _ => witness
    with g = Multiplication _ _ _ => witness.

  (** Predicate that checks if the wire is an addition gate *)
  op is_addition (g : gates_t) : bool =
    with g = PInput _ => false
    with g = SInput _ => false
    with g = Constant _ _ => false
    with g = Addition _ _ _ => true
    with g = Multiplication _ _ _ => false.
  (** Extracts the contents of an addition gate (the corresponding wire ID and the left and
      right wires) *)
  op as_addition (g : gates_t) : gid_t * gates_t * gates_t =
    with g = PInput _ => witness
    with g = SInput _ => witness
    with g = Constant _ _ => witness
    with g = Addition gid wl wr => (gid, wl, wr)
    with g = Multiplication _ _ _ => witness.

  (** Predicate that checks if the wire is a multiplication gate *)
  op is_multiplication (g : gates_t) : bool =
    with g = PInput _ => false
    with g = SInput _ => false
    with g = Constant _ _ => false
    with g = Addition _ _ _ => false
    with g = Multiplication _ _ _ => true.
  (** Extracts the contents of a multiplication gate (the corresponding wire ID and the left and
      right wires) *)
  op as_multiplication (g : gates_t) : gid_t * gates_t * gates_t =
    with g = PInput _ => witness
    with g = SInput _ => witness
    with g = Constant _ _ => witness
    with g = Addition _ _ _ => witness
    with g = Multiplication gid wl wr => (gid, wl, wr).

  (** Extracts the wire or gate ID *)
  op get_gid (g : gates_t) : gid_t = 
    with g = PInput wid => wid
    with g = SInput wid => wid
    with g = Constant gid c => gid
    with g = Addition gid wl wr => gid
    with g = Multiplication gid wl wr => gid.

  (** [get_gate gg k] returns the gate with ID [k], if it exists *)
  op get_gate (gg : gates_t) (k : int) : gates_t option =
    with gg = PInput w => if w = k then Some gg else None
    with gg = SInput w => if w = k then Some gg else None
    with gg = Constant gid c => if gid = k then Some gg else None
    with gg = Addition gid wl wr => 
      if gid = k then Some gg 
      else 
        let ol = get_gate wl k in
        if ol <> None then ol
        else get_gate wr k
    with gg = Multiplication gid wl wr =>
      if gid = k then Some gg 
      else 
        let ol = get_gate wl k in
        if ol <> None then ol
        else get_gate wr k.

  (** Well-formation predicate for input (public and secret) gate IDs. 

      We consider input gate IDs valid if:
        - the first IDs correspond to public input gates
        - the IDs between the interval of **npinputs** and **npinputs + nspinputs** correspond to
          secret input wires 

      Consequently, constant, addition and multiplication gates IDs start at **npinputs + 
      nspinputs**, and range to **npinputs + nspinputs + ngates** *)
  op valid_input_gates (np : int) (ns : int) (gg : gates_t) : bool = 
    with gg = PInput w => 0 <= w < np
    with gg = SInput w => np <= w < np+ns
    with gg = Constant _ _ => true
    with gg = Addition _ wl wr => valid_input_gates np ns wl /\ valid_input_gates np ns wr
    with gg = Multiplication _ wl wr => valid_input_gates np ns wl /\ valid_input_gates np ns wr.

  (** Constant validity predicate. We accept all field values as valid constants *)
  op valid_constant (x : t) : bool = true.

  (** Constant gate validity predicate. Checks if all constant gates are defined with a valid
      constant *)
  op valid_constant_gates (np : int) (ns : int) (gg : gates_t) : bool =
    with gg = PInput w => true
    with gg = SInput w => true
    with gg = Constant gid c => valid_constant c
    with gg = Addition _ wl wr => valid_constant_gates np ns wl /\ valid_constant_gates np ns wr
    with gg = Multiplication _ wl wr => valid_constant_gates np ns wl /\ valid_constant_gates np ns wr.

  (** Checks if there exists any wire or gate with a given ID in the collection of gates *)
  op mem_gid (k : int) (gg : gates_t) : bool =
    with gg = PInput w => w = k
    with gg = SInput w => w = k
    with gg = Constant gid c => gid = k
    with gg = Addition gid wl wr => gid = k \/ mem_gid k wl \/ mem_gid k wr 
    with gg = Multiplication gid wl wr => gid = k \/ mem_gid k wl \/ mem_gid k wr.

  (** Valid gate ID predicate. 

      We consider a gate ID valid if:
        - gates IDs start at **npinputs + nspinputs**, and range to **npinputs + nspinputs + 
          ngates** 
        - for addition and multiplication gates:
          - the IDs of the left and right wires are smaller than the gate ID (avoid loops) 
          - the left and right wires are not calling repeated gates *)
  op valid_gids np ns q (gg : gates_t) : bool =  
    with gg = PInput _ => true
    with gg = SInput _ => true
    with gg = Constant gid _ => np+ns <= gid < np+ns+q
    with gg = Addition gid wl wr => np+ns <= gid < np+ns+q /\ 
                                    get_gid wl < gid /\ get_gid wr < gid /\
                                    !mem_gid gid wl /\ !mem_gid gid wr /\ 
                                    (forall k, mem_gid k wl => !mem_gid k wr) /\
                                    (forall k, mem_gid k wr => !mem_gid k wl) /\
                                    valid_gids np ns q wl /\ valid_gids np ns q wr
    with gg = Multiplication gid wl wr => np+ns <= gid < np+ns+q /\ 
                                          get_gid wl < gid /\ get_gid wr < gid /\
                                          !mem_gid gid wl /\ !mem_gid gid wr /\ 
                                          (forall k, mem_gid k wl => !mem_gid k wr) /\
                                          (forall k, mem_gid k wr => !mem_gid k wl) /\
                                          valid_gids np ns q wl /\ valid_gids np ns q wr.

  (** Proves that all wire and gate IDs will be in the interval [0; **npinputs + nsinputs + 
      ngates**] *)
  lemma valid_gid_pos (np ns m q : int) (gg : gates_t) : 
    0 <= np => 0 < ns /\ 0 < q =>
    valid_input_gates np ns gg => valid_gids np ns q gg => 
    0 <= get_gid gg /\ get_gid gg < np+ns+q.
  proof. by elim gg => // => /#. qed.

  (** The output wires are captured by an array with their IDs *)
  type output_wires_t = wid_t list.

  (** Instantiation of the abstract circuit syntax with the concrete datatypes and operators 
      defined above. *)
  clone import Circuit with
    type Domain.wire_t = wire_t,
    op Domain.wire_to_bool = wire_to_bool,
    type wid_t = wid_t,
    type gid_t = gid_t,
    type gates_t = gates_t,
    type output_wires_t = output_wires_t,
    op valid_out_wires (topo : topology_t) (ys : output_wires_t) = 
      size ys = topo.`noutputs /\
      (forall k, 0 <= k < size ys => 
        topo.`npinputs + topo.`nsinputs <= nth 0 ys k < topo.`npinputs + topo.`nsinputs + topo.`ngates),
    op valid_gates (topo : topology_t) (gg : gates_t) = 
      valid_input_gates topo.`npinputs topo.`nsinputs gg /\ 
      valid_constant_gates topo.`npinputs topo.`nsinputs gg /\ 
      valid_gids topo.`npinputs topo.`nsinputs topo.`ngates gg.

  (** Auxiliary lemma that proves that if a circuit is valid, than their wire and gate IDs are 
      defined in the correct interval *)
  lemma valid_circuit_gid c : 
    valid_circuit c =>
    0 <= get_gid c.`gates < c.`topo.`npinputs + c.`topo.`nsinputs + c.`topo.`ngates by smt().

  (** Auxiliary lemma that proves that if a an addition gate is a valid circuit, then the left
      wire is also a valid circuit *)
  lemma valid_circuit_addition_wl c : 
    valid_circuit c =>
    is_addition c.`gates => valid_circuit {| topo = c.`topo ; gates = (as_addition c.`gates).`2 ; out_wires = c.`out_wires |} by smt().

  (** Auxiliary lemma that proves that if a an addition gate is a valid circuit, then the right
      wire is also a valid circuit *)
  lemma valid_circuit_addition_wr c : 
    valid_circuit c =>
    is_addition c.`gates => valid_circuit {| topo = c.`topo ; gates = (as_addition c.`gates).`3 ; out_wires = c.`out_wires |} by smt().

  (** Auxiliary lemma that proves that if a amultiplication gate is a valid circuit, then the left
      wire is also a valid circuit *)
  lemma valid_circuit_multiplication_wl c : 
    valid_circuit c =>
    is_multiplication c.`gates => valid_circuit {| topo = c.`topo ; gates = (as_multiplication c.`gates).`2 ; out_wires = c.`out_wires |} by smt().

  (** Auxiliary lemma that proves that if a a multiplication gate is a valid circuit, then the 
      right wire is also a valid circuit *)
  lemma valid_circuit_multiplication_wr c : 
    valid_circuit c =>
    is_multiplication c.`gates => valid_circuit {| topo = c.`topo ; gates = (as_multiplication c.`gates).`3 ; out_wires = c.`out_wires |} by smt().

  (** Auxiliary lemma that proves that if a wire/gate ID is part of a valid circuit, then it is
      the correct value interval *)
  lemma mem_gid_range k c :
    valid_circuit c =>
    mem_gid k c.`gates => 0 <= k < c.`topo.`npinputs + c.`topo.`nsinputs + c.`topo.`ngates.
  proof.
    rewrite /valid_circuit /= /valid_topology /= /valid_gates; progress.
    
    move : H4 H5 H6 H7 H8; elim c.`gates.
      by move => wid => /#.
      by move => wid => /#.
      by move => gid x => /#.
      by move => gid wl wr => /#.
      by move => gid wl wr => /#.

    move : H4 H5 H6 H7 H8; elim c.`gates.
      by move => wid => /#.
      by move => wid => /#.
      by move => gid x => /#.
      by move => gid wl wr => /#.
      by move => gid wl wr => /#.
  qed.

  (** Evaluates a set of gates [gg], according to some public [xp] and secret [xs] inputs.

      This is the *plain* gates evaluation, without any security concerns, where inputs are
      provided as lists of field elements *)
  op eval_gates (gg : gates_t) (xp : t list) (xs : t list) : t =
    with gg = PInput w => nth fzero xp w
    with gg = SInput w => nth fzero xs w
    with gg = Constant gid c => c
    with gg = Addition gid wl wr => fadd (eval_gates wl xp xs) (eval_gates wr xp xs)
    with gg = Multiplication gid wl wr => fmul (eval_gates wl xp xs) (eval_gates wr xp xs).

  (** Circuit evaluation function. For our case, it is simply a call to the gates evaluation
      procedure defined above. *)
  op eval_circuit (c : circuit_t) (xp : t list) (xs : t list) : t =
    eval_gates c.`gates xp xs.

  (** Evaluates a set of gates [gg], according to some public [xp] and secret [xs] inputs.

      This is the *plain* gates evaluation, without any security concerns, where inputs are
      provided as arrays of field elements *)
  op eval_gates_array (gg : gates_t) (xp : t array) (xs : t array) : t =
    with gg = PInput w => get fzero xp w
    with gg = SInput w => get fzero xs w
    with gg = Constant gid c => c
    with gg = Addition gid wl wr => fadd (eval_gates_array wl xp xs) (eval_gates_array wr xp xs)
    with gg = Multiplication gid wl wr => fmul (eval_gates_array wl xp xs) (eval_gates_array wr xp xs).

  (** Similar to **eval_circuit**, but takes as input arrays of field values, instead of lists *)
  op eval_circuit_array (c : circuit_t) (xp : t array) (xs : t array) : t =
    eval_gates_array c.`gates xp xs.

  (** Establishes the equivalence between evaluating a circuit where inputs are represented as
      lists and where inputs are represented as arrays.

      Intuitively, given inputs as arrays, we are provind that evaluating a circuit using 
      **eval_gates_array** yields the same output as converting the arrays to lists and then
      evaluating the circuit using **eval_gates** *)
  lemma eval_gates_array_eq gg xp xs : 
    eval_gates_array gg xp xs = eval_gates gg (to_list xp) (to_list xs).
  proof.
    elim gg => //=.

    by move => wid; progress; rewrite nth_to_list.
    by move => wid; progress; rewrite nth_to_list.
    by move => l r => /#.
    by move => l r => /#.
  qed.

  (** Establishes the equivalence between evaluating a circuit where inputs are represented as
      lists and where inputs are represented as arrays. This lemma is the inverse of lemma
      **eval_gates_array_eq**: given inputs as lists, we are provind that evaluating a circuit 
      using **eval_gates** yields the same output as converting the lists to arrays and then
      evaluating the circuit using **eval_gates** *)
  lemma eval_gates_list_eq gg xp xs : 
    eval_gates gg xp xs = eval_gates_array gg (of_list xp) (of_list xs).
  proof.
    elim gg => //=.

    by move => wid; progress; rewrite get_of_list.
    by move => wid; progress; rewrite get_of_list.
    by move => l r => /#.
    by move => l r => /#.
  qed.

  (** Evaluates the gates of a circuit until the gate with a given ID is reached *)
  op eval_until (gg : gates_t) (xp : t list) (xs : t list) (id : gid_t) : t =
    with gg = PInput w => nth fzero xp w
    with gg = SInput w => nth fzero xs w
    with gg = Constant gid c => c 
    with gg = Addition gid wl wr => 
      if id = gid then fadd (eval_gates wl xp xs) (eval_gates wr xp xs)
      else
        if mem_gid id wl then eval_until wl xp xs id
        else eval_until wr xp xs id
    with gg = Multiplication gid wl wr => 
      if id = gid then fmul (eval_gates wl xp xs) (eval_gates wr xp xs)
      else
        if mem_gid id wl then eval_until wl xp xs id
        else eval_until wr xp xs id.

  (** Evaluates a specific gate of the circuit *)
  op eval_gate (id : gid_t) (gg : gates_t) (xp : t list) (xs : t list) : t =
    with gg = PInput w => if id = w then nth fzero xp w else fzero
    with gg = SInput w => if id = w then nth fzero xs w else fzero
    with gg = Constant gid c => if id = gid then c else fzero 
    with gg = Addition gid wl wr => 
      if id = gid then fadd (eval_gates wl xp xs) (eval_gates wr xp xs)
      else
        let el = eval_gate id wl xp xs in
        if el <> fzero then el else eval_gate id wr xp xs
    with gg = Multiplication gid wl wr => 
      if id = gid then fmul (eval_gates wl xp xs) (eval_gates wr xp xs)
      else
        let el = eval_gate id wl xp xs in
        if el <> fzero then el else eval_gate id wr xp xs.

  (** Proves that evaluating the root circuit gate using [eval_gate] is the same as evaluating
      the entire circuit using the [eval_gates] operator *)
  lemma eval_gate_gid gg xp xs : eval_gates gg xp xs = eval_gate (get_gid gg) gg xp xs.
  proof.  by elim gg => //=. qed.

end ArithmeticCircuit.
