require import Int List.

from General require import PrimeField ListExt.

from Circuit require import ACircuit.

theory ArithmeticCircuit.

  type gates_t = [
    | PInput of int
    | SInput of int
    | Constant of int & t
    | Addition of int & gates_t & gates_t
    | Multiplication of int & gates_t & gates_t
    | SMultiplication of int & gates_t & gates_t
  ].

  op is_pinput (g : gates_t) : bool = 
    with g = PInput _ => true
    with g = SInput _ => false
    with g = Constant _ _ => false
    with g = Addition _ _ _ => false
    with g = Multiplication _ _ _ => false
    with g = SMultiplication _ _ _ => false.
  (*op as_input (g : gates_t) : int =
    with g = Input w => w
    with g = Constant _ => witness
    with g = Addition _ _ _ => witness
    with g = Multiplication _ _ _ => witness
    with g = SMultiplication _ _ _ => witness.*)

  op is_constant (g : gates_t) : bool = 
    with g = PInput _ => false
    with g = SInput _ => false
    with g = Constant _ _ => true
    with g = Addition _ _ _ => false
    with g = Multiplication _ _ _ => false
    with g = SMultiplication _ _ _ => false.
  op as_constant (g : gates_t) =
    with g = PInput _ => witness
    with g = SInput _ => witness
    with g = Constant gid c => (gid,c)
    with g = Addition _ _ _ => witness
    with g = Multiplication _ _ _ => witness
    with g = SMultiplication _ _ _ => witness.

  (*op is_addition (g : gates_t) : bool = 
    with g = Input _ => false
    with g = Constant _ => false
    with g = Addition _ _ _ => true
    with g = Multiplication _ _ _ => false
    with g = SMultiplication _ _ _ => false.
  op as_addition (g : gates_t) : int * gates_t * gates_t =
    with g = Input _ => witness
    with g = Constant _ => witness
    with g = Addition gid wl wr => (gid,wl,wr)
    with g = Multiplication _ _ _ => witness
    with g = SMultiplication _ _ _ => witness.

  op is_multiplication (g : gates_t) : bool = 
    with g = Input _ => false
    with g = Constant _ => false
    with g = Addition _ _ _ => false
    with g = Multiplication _ _ _ => true
    with g = SMultiplication _ _ _ => false.
  op as_multiplication (g : gates_t) : int * gates_t * gates_t =
    with g = Input _ => witness
    with g = Constant _ => witness
    with g = Addition _ _ _ => witness
    with g = Multiplication gid wl wr => (gid,wl,wr)
    with g = SMultiplication _ _ _ => witness.

  op is_smultiplication (g : gates_t) : bool = 
    with g = Input _ => false
    with g = Constant _ => false
    with g = Addition _ _ _ => false
    with g = Multiplication _ _ _ => false
    with g = SMultiplication _ _ _ => true.
  op as_smultiplication (g : gates_t) : int * gates_t * gates_t =
    with g = Input _ => witness
    with g = Constant _ => witness
    with g = Addition _ _ _ => witness
    with g = Multiplication _ _ _ => witness
    with g = SMultiplication gid wl wr => (gid,wl,wr).*)

  type topology_t = int * int * int * int.

  op valid_input_gates (np : int) (ns : int) (gg : gates_t) : bool = 
    with gg = PInput w => 0 <= w < np
    with gg = SInput w => np <= w < np+ns
    with gg = Constant _ _ => true
    with gg = Addition _ wl wr => valid_input_gates np ns wl /\ valid_input_gates np ns wr
    with gg = Multiplication _ wl wr => valid_input_gates np ns wl /\ valid_input_gates np ns wr
    with gg = SMultiplication gid wl wr => valid_input_gates np ns wl /\ valid_input_gates np ns wr.

  op valid_constant : t -> bool.

  op valid_constant_gates (np : int) (ns : int) (gg : gates_t) : bool = 
    with gg = PInput w => true
    with gg = SInput w => true
    with gg = Constant gid c => valid_constant c
    with gg = Addition _ wl wr => valid_constant_gates np ns wl /\ valid_constant_gates np ns wr
    with gg = Multiplication _ wl wr => valid_constant_gates np ns wl /\ valid_constant_gates np ns wr
    with gg = SMultiplication gid wl wr => valid_constant_gates np ns wl /\ valid_constant_gates np ns wr.

  op valid_smultiplication_gates (gg : gates_t) : bool =  
    with gg = PInput _ => true
    with gg = SInput _ => true
    with gg = Constant _ _ => true
    with gg = Addition _ wl wr => valid_smultiplication_gates wl /\ valid_smultiplication_gates wr
    with gg = Multiplication _ wl wr => valid_smultiplication_gates wl /\ valid_smultiplication_gates wr
    with gg = SMultiplication _ wl wr => (is_constant wl) /\ valid_smultiplication_gates wr.

  op valid_gids np ns q (gg : gates_t) : bool =  
    with gg = PInput _ => true
    with gg = SInput _ => true
    with gg = Constant _ _ => true
    with gg = Addition gid wl wr => np+ns <= gid < np+ns+q /\ valid_gids np ns q wl /\ valid_gids np ns q wr
    with gg = Multiplication gid wl wr => np+ns <= gid < np+ns+q /\ valid_gids np ns q wl /\ valid_gids np ns q wr
    with gg = SMultiplication gid wl wr => np+ns <= gid < np+ns+q /\ valid_gids np ns q wl /\ valid_gids np ns q wr.

  op valid_gates (c : topology_t * gates_t) = 
    let (np,ns,m,q) = fst c in
    let gg = snd c in
    valid_input_gates np ns gg /\ valid_constant_gates np ns gg /\ valid_smultiplication_gates gg /\ valid_gids np ns q gg.

  clone import Circuit with
    type Domain.wire_t = t,
    op Domain.wire_to_bool (x : wire_t) = if x = fzero then false else true,
    type gates_t = gates_t,
    op valid_gates = valid_gates.

end ArithmeticCircuit.
