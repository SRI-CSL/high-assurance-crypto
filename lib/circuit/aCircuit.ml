open EcList

module type Domain = sig

  type wire_t

  val wire_to_bool : wire_t -> bool

end


module type Gates = sig

  type gates_t

  val valid_gates : (Z.t * Z.t * Z.t * Z.t) * gates_t -> bool

  val eval_gates : gates_t -> Z.t list -> Z.t list -> Z.t

end

module Circuit (Dom : Domain) (G : Gates) = struct
   
  type wire_t = Dom.wire_t

  type wid_t = Z.t
  type gid_t = Z.t
  type topology_t = Z.t * Z.t * Z.t * Z.t

  type gates_t = G.gates_t

  type circuit_t = topology_t * gates_t

  let valid_topology (topo : topology_t) : bool =
    let (np,ns,m,q) = topo in
    Z.leq Z.zero np && Z.lt Z.zero ns && Z.lt Z.zero m && Z.lt Z.zero q && Z.lt m q

  let valid_circuit (c : circuit_t) : bool =
    let (np,ns,m,q) = fst c in
    let cc = snd c in
    valid_topology (np,ns,m,q) && G.valid_gates ((np,ns,m,q), cc)

  let eval_circuit (c : circuit_t) (xp : Z.t list) (xs : Z.t list) : Z.t = 
    if valid_circuit c then G.eval_gates (snd c) xp xs
    else Z.of_string "-1"

end