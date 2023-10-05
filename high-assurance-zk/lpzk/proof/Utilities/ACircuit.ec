(**
  Syntax of circuits. The goal of this file is to provide an abstract interface type for circuits,
  defining the general architecture and syntax of circuits.

  The construction of circuits is quite modular, in the sense that we separate the **Domain** - 
  that captures the wire type - from the actual **Circuit** - the *sequence* of gates. 
  This allows interesting use-cases, such as having different gate representations for circuits
  with the same domain (for example, two boolean circuits where gates are represented differently)
  or having the same gate representation working with different domains.
*)

require import Int List.

(**
  The **Domain** theory parameterizes a **Circuit**, fixing the wire type of the circuit, defined
  by the **wire_t** type. For example, instantiating **wire_t** with a boolean field datatype
  would yield a boolean circuit.

  The **Domain** interface also provides a wire to boolean conversion, useful if the circuit has
  output gates that, for example, assert if some value is equal to zero.
*)
theory Domain.

  (** Wire type. This type needs to be made concrete when the circuit is instantiated *)
  type wire_t.

  (** Wire to boolean conversion. Defines how the boolean *true* and *false* values are 
      represented by the wire type. For example, on an arithmetic circuit, *true* would be 
      represented by the value *1* whereas *false* would be represented by the value *0*. 
      This operator needs to be made concrete when the circuit is instantiated. *)
  op wire_to_bool : wire_t -> bool.

end Domain.

(**
  Circuit syntax. We model circuits as a record with three elements. The first element is the 
  topology of the circuit, that comprises the number of public input wires **npinputs**, the 
  number of secret input wires **nsinputs**, the number of gates **ngates** and the number of 
  output wires **noutputs**. The second element comprises the actual gates that form the circuit,
  whose type is left underspecified in order to support multiple gate representations. Finally, 
  the circuit description also encompasses the concrete definition of the output wires, 
  represented by the **out_wires** record.

  When using the **Circuit** interface, the user must provide the types used to represent wire
  and gate indexes, how gates are represented and how are output wires defined in the circuit.
  Moreover, the theory also requires a well-formation predicate for the circuit gates and also
  for the output wires.

  We refer the reader to the *ArithmeticCircuit.ec* file for an instantiation example of this
  abstract circuit interface.
*)
theory Circuit.

  (** Cloning an abstract domain. When defining a concrete circuit, the domain of the wires must
      be provided. *)
  clone import Domain.
  
  (** Wire index type. This type needs to be made concrete when the protocol is instantiated *)
  type wid_t.
  (** Gate index type. This type needs to be made concrete when the protocol is instantiated *)
  type gid_t.
  (** Topology of a circuit. The topology record encompasses the number of public inputs, the
      number of secret inputs, the number of gates and the number of output wires of the 
      circuit *)
  type topology_t = { npinputs : int ; nsinputs : int ; ngates : int ; noutputs : int }.

  (** Gate representation type. This type needs to be made concrete when the protocol is 
      instantiated *)
  type gates_t.
  (** Output wires representation type. This type needs to be made concrete when the protocol is 
      instantiated *)
  type output_wires_t.

  (** Circuit type. The circuit type discloses the topology of the circuit, the gates that
      comprise it and which wires are outputs of the circuits. *)
  type circuit_t = { topo : topology_t ; gates : gates_t ; out_wires : output_wires_t }.

  (** Topology validity predicate. This predicate provides basic requirements for a circuit 
      topology: the circuit may not have public inputs, but it is required to have secret inputs,
      it must have at least one gate, at least one output wire, and the number of output wires
      must not be bigger than the total number of gates in the circuit *)
  op valid_topology (topo : topology_t) : bool =
    let np = topo.`npinputs in
    let ns = topo.`nsinputs in
    let q = topo.`ngates in
    let m = topo.`noutputs in
    0 <= np /\ 0 < ns /\ 0 < m /\ 0 < q /\ m <= q.

  (** Well-formation predicate for gates. This predicate needs to be made concrete when the 
      protocol is instantiated *)
  op valid_gates : topology_t -> gates_t -> bool.

  (** Well-formation predicate for output wires. This predicate needs to be made concrete when 
      the protocol is instantiated *)
  op valid_out_wires : topology_t -> output_wires_t -> bool.

  (** Circuit validity predicate. It aggregates the above well-formation predicates into a 
      single one *)
  op valid_circuit (c : circuit_t) : bool =
    let topo = c.`topo in
    let gg = c.`gates in
    let ys = c.`out_wires in
    valid_topology topo /\ valid_gates topo gg /\ valid_out_wires topo ys.

end Circuit.
