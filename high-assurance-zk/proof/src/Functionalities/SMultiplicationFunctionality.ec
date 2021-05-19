require import List.

from General require import PrimeField.

from Functionalities require import AGateFunctionality.
from SecretSharing require import ASecretSharingScheme.

theory SMultiplicationFunctionality.

  clone import SecretSharingScheme with type secret_t = t.

  type pinput_t = share_t.
  type sinput_t = share_t.
  type input_t = pinput_t * (sinput_t * sinput_t).

  type inputs_t = (pid_t * input_t) list.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t * sinput_t = snd (input pid xs).
  op valid_inputs (xs : inputs_t) : bool =
    unzip1 xs = pid_set /\
    let pub = map (fun pid => (pid, pinput pid xs)) pid_set in
    let sec = map (fun pid => (pid, fst (sinput pid xs))) pid_set in
    (exists r s, valid_secret s /\ valid_rand r /\ share r s = sec) /\ 
    (exists s, pub = public_encoding s). 

  type output_t = secret_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).
  op f (xs : inputs_t) : outputs_t = 
    let ssec = map (fun pid => (pid, fst (sinput pid xs))) pid_set in
    let sec = reconstruct ssec in
    let pub = (oget (assoc xs (head witness pid_set))).`1 in
    let y = fmul (pub_reconstruct (head witness pid_set) pub) sec in map (fun pid => (pid, y)) pid_set.

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

end SMultiplicationFunctionality.
