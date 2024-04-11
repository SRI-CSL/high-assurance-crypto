open EcList
open EcOption
open ACircuit

module ArithmeticDomain = struct

  type wire_t = Z.t
  let wire_to_bool (w : wire_t) : bool = if Z.equal w Z.zero then false else true

end

module ArithmeticGates = struct

  type gates_t = 
    | PInput of Z.t
    | SInput of Z.t
    | Constant of Z.t * Z.t
    | Addition of Z.t * gates_t * gates_t
    | Multiplication of Z.t * gates_t * gates_t
    | SMultiplication of Z.t * gates_t * gates_t

  let is_pinput (g : gates_t) : bool = 
    match g with
      | PInput _ -> true
      | SInput _ -> false
      | Constant _ -> false
      | Addition _ -> false
      | Multiplication _ -> false
      | SMultiplication _ -> false

  let is_constant (g : gates_t) : bool = 
    match g with
      | PInput _ -> false
      | SInput _ -> false
      | Constant _ -> true
      | Addition _ -> false
      | Multiplication _ -> false
      | SMultiplication _ -> false

  let as_constant (g : gates_t) = 
    match g with
      | PInput _ -> witness
      | SInput _ -> witness
      | Constant (gid,c) -> (gid,c)
      | Addition _ -> witness
      | Multiplication _ -> witness
      | SMultiplication _ -> witness

  let rec valid_input_gates (np : Z.t) (ns : Z.t) (g : gates_t) : bool = 
    match g with
      | PInput w -> Z.leq Z.zero w && Z.lt w np
      | SInput w -> Z.leq np w && Z.lt w (Z.add np ns)
      | Constant _ -> true
      | Addition (_, wl, wr) -> valid_input_gates np ns wl && valid_input_gates np ns wr
      | Multiplication (_, wl, wr) -> valid_input_gates np ns wl && valid_input_gates np ns wr
      | SMultiplication (_, wl, wr) -> valid_input_gates np ns wl && valid_input_gates np ns wr

  let rec valid_smultiplication_gates (g : gates_t) : bool =
    match g with
      | PInput _ -> true
      | SInput _ -> true
      | Constant _ -> true
      | Addition (_, wl, wr) -> valid_smultiplication_gates wl && valid_smultiplication_gates wr
      | Multiplication (_, wl, wr) -> valid_smultiplication_gates wl && valid_smultiplication_gates wr
      | SMultiplication (_, wl, wr) -> (is_constant wl) && valid_smultiplication_gates wr

  let rec valid_gids np ns q (g : gates_t) : bool =
    match g with
      | PInput _ -> true
      | SInput _ -> true
      | Constant _ -> true
      | Addition (gid, wl, wr) -> Z.leq (Z.add np ns) gid && Z.lt gid (Z.add np (Z.add ns q)) && valid_gids np ns q wl && valid_gids np ns q wr
      | Multiplication (gid, wl, wr) -> Z.leq (Z.add np ns) gid && Z.lt gid (Z.add np (Z.add ns q)) && valid_gids np ns q wl && valid_gids np ns q wr
      | SMultiplication (gid, wl, wr) -> Z.leq (Z.add np ns) gid && Z.lt gid (Z.add np (Z.add ns q)) && valid_gids np ns q wl && valid_gids np ns q wr

  let valid_gates (c : (Z.t * Z.t * Z.t * Z.t) * gates_t) : bool =
    let (np,ns,m,q) = fst c in
    let gg = snd c in
    valid_input_gates np ns gg && valid_smultiplication_gates gg && valid_gids np ns q gg

  let rec eval_gates (g : gates_t) (xp : Z.t list) (xs : Z.t list) : Z.t = 
    match g with
    | PInput w -> nth Z.zero xp w
    | SInput w -> nth Z.zero xs w
    | Constant (gid, c) -> c
    | Addition (gid, wl, wr) -> Z.add (eval_gates wl xp xs) (eval_gates wl xp xs)
    | Multiplication (gid, wl, wr) -> Z.mul (eval_gates wl xp xs) (eval_gates wl xp xs)
    | SMultiplication (gid, wl, wr) -> Z.mul (eval_gates wl xp xs) (eval_gates wl xp xs)

end

module ArithmeticCircuit = Circuit (ArithmeticDomain) (ArithmeticGates)