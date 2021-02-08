require import List.

from General require import PrimeField ListExt.

from Functionalities require import AGateFunctionality.
from SecretSharing require import ASecretSharingScheme.

theory AdditionFunctionality.

  clone import SecretSharingScheme with type secret_t = t.

  type pinput_t = unit.
  type sinput_t = share_t * share_t.
  type input_t = pinput_t * sinput_t.
  type inputs_t = (pid_t * input_t) list.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t = snd (input pid xs).

  op valid_inputs (xs : inputs_t) : bool = 
    unzip1 xs = pid_set /\
    let sec1 = map (fun pid => (pid, fst (sinput pid xs))) pid_set in
    let sec2 = map (fun pid => (pid, snd (sinput pid xs))) pid_set in
    (exists r s, valid_secret s /\ valid_rand r /\ share r s = sec1) /\ 
    (exists r' s', valid_secret s' /\ valid_rand r' /\ share r' s' = sec2).

  type output_t = t.

  op f (xs : inputs_t) : output_t =
    let sec1 = map (fun pid => (pid, fst (sinput pid xs))) pid_set in
    let sec2 = map (fun pid => (pid, snd (sinput pid xs))) pid_set in
    let sec1 = odflt fzero (reconstruct sec1) in
    let sec2 = odflt fzero (reconstruct sec2) in
    fadd sec1 sec2.

  clone import GateFunctionality with
    type pid_t = pid_t,
    op pid_set = pid_set,
    type pinput_t = pinput_t,
    type sinput_t = sinput_t,
    op valid_inputs = valid_inputs,
    type output_t = output_t,
    op f = f
  proof *.
  realize pid_set_uniq by apply pid_set_uniq.

end AdditionFunctionality.
