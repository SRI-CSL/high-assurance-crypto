require import AllCore List.

from General require import ListExt.

from Functionalities require import AFunctionality.

theory GateFunctionality.

  const n : {int | 2 <= n} as n_pos.
  const t : {int | 0 <= t < n} as t_pos.

  type pid_t.
  op pid_set : pid_t list.
  axiom pid_set_uniq : uniq pid_set.
  axiom pid_set_size : size pid_set = n.

  type pinput_t.
  type sinput_t.
  type input_t = pinput_t * (sinput_t * sinput_t).
  type inputs_t = (pid_t * input_t) list.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t * sinput_t = snd (input pid xs).
  op valid_inputs (xs : inputs_t) : bool. 

  type output_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).
  op f : inputs_t -> outputs_t.

end GateFunctionality.
