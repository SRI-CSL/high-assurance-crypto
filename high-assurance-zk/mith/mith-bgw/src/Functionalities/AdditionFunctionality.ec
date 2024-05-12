require import List.

from General require import PrimeField.

from Functionalities require import AGateFunctionality.
from SecretSharing require import ASecretSharingScheme.

theory AdditionFunctionality.

  clone import SecretSharingScheme with type secret_t = t.

  type pinput_t = unit.
  type sinput_t = share_t * share_t.
  type input_t = pinput_t * sinput_t.
  type inputs_t = (pid_t * input_t) list.

  type pinputs_t = (pid_t * pinput_t) list.
  type sinputs_t = (pid_t * sinput_t) list.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t = snd (input pid xs).

  op mk_inputs (xp : pinput_t) (sx : (pid_t * sinput_t) list) = 
    map (fun pid => (pid, (xp, oget (assoc sx pid)))) pid_set.

  op pinputs (xs : inputs_t) : pinputs_t = 
    map (fun pid => (pid, fst (oget (assoc xs pid)))) pid_set.
  op sinputs (xs : inputs_t) : sinputs_t = 
    map (fun pid => (pid, snd (oget (assoc xs pid)))) pid_set.

  op valid_inputs (xs : inputs_t) : bool =
    unzip1 xs = pid_set /\
    let sec1 = map (fun pid => (pid, fst (sinput pid xs))) pid_set in
    let sec2 = map (fun pid => (pid, snd (sinput pid xs))) pid_set in
    (exists r s, valid_secret s /\ valid_rand r s /\ share r s = sec1) /\ 
    (exists r' s', valid_secret s' /\ valid_rand r' s' /\ share r' s' = sec2).

  type output_t = secret_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).
  op f (xs : inputs_t) : outputs_t = 
    let ssec1 = map (fun pid => (pid, fst (sinput pid xs))) pid_set in
    let ssec2 = map (fun pid => (pid, snd (sinput pid xs))) pid_set in
    let sec1 = reconstruct ssec1 in
    let sec2 = reconstruct ssec2 in 
    let y = fadd sec1 sec2 in map (fun pid => (pid, y)) pid_set.

   clone import GateFunctionality with
    op n = n,
    op t = t,

    type pid_t = pid_t,
    op pid_set = pid_set,

    type pinput_t = pinput_t,
    type sinput_t = sinput_t,

    op valid_inputs = valid_inputs,

    type output_t = output_t,

    op f = f.

end AdditionFunctionality.