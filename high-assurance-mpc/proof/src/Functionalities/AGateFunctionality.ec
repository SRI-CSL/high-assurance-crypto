require import List.

from General require import ListExt.

from Functionalities require import AFunctionality.

theory GateFunctionality.

  type pid_t.
  op pid_set : pid_t list.
  axiom pid_set_uniq : uniq pid_set.

  type pinput_t.
  type sinput_t.
  type input_t = pinput_t * sinput_t.
  type inputs_t = (pid_t * input_t) list.

  op valid_inputs (xs : inputs_t) : bool = size xs = size pid_set.
  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t = snd (input pid xs).

  type output_t.

  op f : inputs_t -> output_t. 

  clone import Functionality with
    type input_t = inputs_t,
    pred valid_input = valid_inputs,
    type output_t = output_t,
    op f = f.

end GateFunctionality.

(*theory GateFunctionality.

  type pid_t.
  op pid_set : pid_t list.
  axiom pid_set_uniq : uniq pid_set.

  type pinput_t.
  type sinput_t.
  type input_t = pinput_t * (sinput_t * sinput_t).
  type inputs_t = (pid_t * input_t) list.

  op valid_inputs (xs : inputs_t) : bool = size xs = size pid_set.
  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t * sinput_t = snd (input pid xs).

(*    (exists r s, valid_secret s /\ valid_rand r /\ share r s = x1) /\
    (exists r s, valid_secret s /\ valid_rand r /\ share r s = x2).
*)

  type output_t.

  op f : inputs_t -> output_t. 

  clone import Functionality with
    type input_t = inputs_t,
    pred valid_input = valid_inputs,
    type output_t = output_t,
    op f = f.

end GateFunctionality.*)
