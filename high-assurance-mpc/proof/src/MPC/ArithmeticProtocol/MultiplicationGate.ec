require import Int List.

from General require import PrimeField ListExt.
from SecretSharing require import ASecretSharingScheme.
from MPC require import AGate.
from Functionalities require import MultiplicationFunctionality.

theory MultiplicationGate.

  clone import SecretSharingScheme with type secret_t = t.
  clone import MultiplicationFunctionality with theory SecretSharingScheme <- SecretSharingScheme.

  type rand_t.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand : rand_t -> bool.
  op valid_rands (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ all (fun r => valid_rand (snd r)) rs.

  type output_t = share_t.
  type outputs_t = (pid_t * share_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  type msgs_t.
  type in_messages_t = (pid_t * msgs_t) list.
  type out_messages_t = (pid_t * msgs_t) list.

  op get_messages_to : pid_t -> out_messages_t -> msgs_t.
  op get_messages_from : pid_t -> in_messages_t -> msgs_t.
  
  type view_t = input_t * rand_t * in_messages_t.

  op out_messages : pid_t -> view_t -> out_messages_t.
  op local_output : pid_t -> view_t -> output_t.

  type trace_t = in_messages_t.
  type traces_t = (pid_t * trace_t) list.
  op trace (pid : pid_t) (trs : traces_t) : trace_t = oget (assoc trs pid).

  op gate : rands_t -> inputs_t -> traces_t * outputs_t.

  pred output_pred (y_fy : outputs_t * GateFunctionality.output_t) = 
    let (y,fy) = y_fy in reconstruct y = Some fy.

  clone import Gate with 
    type GateFunctionality.pid_t = pid_t,
    op GateFunctionality.pid_set = pid_set,
    type GateFunctionality.pinput_t = MultiplicationFunctionality.pinput_t,
    type GateFunctionality.sinput_t = MultiplicationFunctionality.sinput_t,
    op GateFunctionality.valid_inputs = MultiplicationFunctionality.valid_inputs,
    type GateFunctionality.output_t = MultiplicationFunctionality.output_t,
    op GateFunctionality.f = MultiplicationFunctionality.f,

    type rand_t = rand_t,
    op rand = rand,
    op valid_rand = valid_rand,

    type output_t = output_t,
    op output = output,

    type msgs_t = msgs_t,
    op get_messages_to = get_messages_to,
    op get_messages_from = get_messages_from,

    op out_messages = out_messages,
    op local_output = local_output,

    op trace = trace,

    op gate = gate,

    pred output_pred = output_pred
  proof GateFunctionality.pid_set_uniq by apply pid_set_uniq.

end MultiplicationGate.
