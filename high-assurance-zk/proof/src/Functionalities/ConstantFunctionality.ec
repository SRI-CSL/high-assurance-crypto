require import List.

from General require import PrimeField ListExt.

from Functionalities require import AGateFunctionality.
from SecretSharing require import ASecretSharingScheme.

theory ConstantFunctionality.

  clone import SecretSharingScheme with type secret_t = t.

  type pinput_t = secret_t.
  type sinput_t = share_t.
  type input_t = pinput_t * (sinput_t * sinput_t).

  type inputs_t = (pid_t * input_t) list.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t * sinput_t = snd (input pid xs).
  op valid_inputs (xs : inputs_t) : bool =
    unzip1 xs = pid_set /\
    let pub = map (fun pid => (pid, pinput pid xs)) pid_set in
    (forall pid, pid \in pid_set => valid_secret (pinput pid xs)) /\
    (exists c, forall pid, pid \in pid_set => c = pinput pid xs). 

  type output_t = secret_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).
  op f (xs : inputs_t) : outputs_t = map (fun pid => (pid, pinput pid xs)) pid_set.

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

end ConstantFunctionality.
