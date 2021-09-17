require import Int List.

from General require import ListExt.

theory Domain.

  type wire_t.

  op wire_to_bool : wire_t -> bool.

end Domain.

theory Circuit.

  clone import Domain.
   
  type wid_t = int.
  type gid_t = int.
  type topology_t = int * int * int * int.

  type gates_t.
  type circuit_t = topology_t * gates_t.

  op valid_gates : topology_t * gates_t -> bool.

  op valid_topology (topo : topology_t) : bool =
    let (np,ns,m,q) = topo in
    0 <= np /\ 0 < ns /\ 0 < m /\ 0 < q /\ m < q.

  op valid_circuit (c : circuit_t) : bool =
    let (np,ns,m,q) = fst c in
    let cc = snd c in
    valid_topology (np,ns,m,q) /\ valid_gates ((np,ns,m,q), cc).

end Circuit.
