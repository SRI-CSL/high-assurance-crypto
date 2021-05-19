require import List Int.

from General require import ListExt.

from Circuit require import ACircuit.
from Functionalities require import AFunctionality.

theory ProtocolFunctionality.

  clone import Circuit.

  const n : {int | 2 <= n} as n_pos.
  const t : {int | 0 <= t < n} as t_pos.

  type pid_t.
  op pid_set : pid_t list.
  axiom pid_set_uniq : uniq pid_set.
  axiom pid_set_size : size pid_set = n.

  type pinput_t.
  type sinput_t.
  type input_t = pinput_t * sinput_t.
  type inputs_t = (pid_t * input_t) list.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t = snd (input pid xs).

  op valid_inputs_topology (topo : topology_t) (xs : inputs_t) : bool.
  op valid_inputs (c : circuit_t) (xs : inputs_t) : bool = 
    valid_circuit c /\ unzip1 xs = pid_set /\
    let (topo, gg) = c in valid_inputs_topology topo xs.

  type output_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (xs : outputs_t) : output_t = oget (assoc xs pid).

  op f : circuit_t -> inputs_t -> outputs_t. 

  (*clone import Functionality with
    type input_t = inputs_t,
    pred valid_input = valid_inputs,
    type output_t = outputs_t,
    op f = f.*)

end ProtocolFunctionality.
