val witness : 'a

val q : Z.t ref

type witness_t = (Z.t) array

type instance_t = (Z.t) array

type topology_t = {
  npinputs: Z.t;
  nsinputs: Z.t;
  ngates: Z.t;
  noutputs: Z.t;
  }

type gates_t =
  | PInput of (Z.t)
  | SInput of (Z.t)
  | Constant of (Z.t) * (Z.t)
  | Addition of (Z.t) * gates_t * gates_t
  | Multiplication of (Z.t) * gates_t * gates_t

val is_pinput : gates_t -> bool

val is_sinput : gates_t -> bool

type circuit_t = topology_t * gates_t

type statement_t = circuit_t * instance_t

val relation : witness_t -> statement_t -> bool

type prover_input_t = witness_t * statement_t

type verifier_input_t = statement_t

type ui_t = {
  a: Z.t;
  b: Z.t;
  a' : Z.t;
  b' : Z.t;
  }

val def_ui : ui_t

type u_t = ui_t array

type prover_rand_t = u_t

type yi_t = {
  v: Z.t;
  v' : Z.t;
  }

val def_yi : yi_t

type y_t = yi_t array

type verifier_rand_t = {
  alpha: Z.t;
  mutable y: yi_t array;
  }

type prover_output_t = unit

type verifier_output_t = bool

type zi_t = {
  m: Z.t;
  m' : Z.t; 
  c2 : Z.t;
  }

type zi_t1 = zi_t

type z_t =
  | PInputZ of (Z.t) * zi_t
  | SInputZ of (Z.t) * zi_t
  | ConstantZ of (Z.t) * zi_t
  | AdditionZ of (Z.t) * zi_t * z_t * z_t
  | MultiplicationZ of (Z.t) * zi_t * z_t * z_t

type commitment_t = z_t * Z.t

val commit : prover_rand_t -> prover_input_t -> commitment_t

type fi_t = {
  e: Z.t;
  e' : Z.t;
  e'' : Z.t;
  }

type f_t =
  | PInputF of fi_t
  | SInputF of fi_t
  | ConstantF of fi_t
  | AdditionF of fi_t * f_t * f_t
  | MultiplicationF of fi_t * f_t * f_t

val bad : f_t

val prove : verifier_rand_t -> verifier_input_t -> commitment_t -> bool

type trace_t = z_t * (Z.t)

val protocol : prover_rand_t * verifier_rand_t -> prover_input_t * verifier_input_t -> trace_t * (prover_output_t * verifier_output_t)