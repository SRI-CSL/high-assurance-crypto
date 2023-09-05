require import List Int.

theory ProtocolFunctionality.

  type circuit_t.

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
  type pinputs_t = (pid_t * pinput_t) list.
  type sinputs_t = (pid_t * sinput_t) list.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t = snd (input pid xs).

  op mk_inputs (xp:pinput_t) (sx:(pid_t * sinput_t) list) = map (fun pid => (pid, (xp, oget (assoc sx pid)))) pid_set.

  op pinputs (xs : inputs_t) : pinputs_t = map (fun pid => (pid, fst (oget (assoc xs pid)))) pid_set.
  op sinputs (xs : inputs_t) : sinputs_t = map (fun pid => (pid, snd (oget (assoc xs pid)))) pid_set.

  op valid_circuit : circuit_t -> bool.
  op valid_inputs (c : circuit_t) (xs : inputs_t) : bool.

  type output_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (xs : outputs_t) : output_t = oget (assoc xs pid).

  op f : circuit_t -> inputs_t -> outputs_t. 

end ProtocolFunctionality.
