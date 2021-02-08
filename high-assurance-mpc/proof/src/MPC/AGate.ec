require import List.

from General require import ListExt Utils.

from Functionalities require import AGateFunctionality.

theory Gate.

  clone import GateFunctionality.

  type rand_t.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand : rand_t -> bool.
  op valid_rands (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ all (fun r => valid_rand (snd r)) rs.

  type output_t.
  type outputs_t = (pid_t * output_t) list.
  op output : pid_t -> outputs_t -> output_t.

  type msgs_t.
  type in_messages_t = (pid_t * msgs_t) list.
  type out_messages_t = (pid_t * msgs_t) list.

  op get_messages_to : pid_t -> in_messages_t -> msgs_t.
  op get_messages_from : pid_t -> out_messages_t -> msgs_t.
  
  type view_t = input_t * rand_t * in_messages_t.

  op out_messages : pid_t -> view_t -> out_messages_t.
  op local_output : pid_t -> view_t -> output_t.

  type trace_t = in_messages_t.
  type traces_t = (pid_t * trace_t) list.
  op trace (pid : pid_t) (trs : traces_t) : trace_t = oget (assoc trs pid).

  op gate : rands_t -> inputs_t -> traces_t * outputs_t.

  pred output_pred : outputs_t * Functionality.output_t.

  axiom correct (rs : rands_t) (xs : inputs_t) :
    Functionality.valid_input xs =>
    valid_rands rs =>
    output_pred ((snd (gate rs xs)), (f xs)).

  axiom local_output_correct (pid : pid_t) (xs : inputs_t) (rs : rands_t) :
    Functionality.valid_input xs =>
    valid_rands rs =>
    pid \in pid_set =>
    let (tr, y) = gate rs xs in
    output pid y = local_output pid (input pid xs, rand pid rs, trace pid tr). 

  axiom messages_consistency (i j : pid_t) (xs : inputs_t) (rs : rands_t) :
    Functionality.valid_input xs =>
    valid_rands rs =>
    i \in pid_set => j \in pid_set =>
    let (tr, y) = gate rs xs in
    get_messages_to j (out_messages i (input i xs, rand i rs, trace i tr)) = 
    get_messages_from i (trace j tr).

  op extract_inputs (xs : inputs_t) (pids : pid_t list) : input_t list =
    map (fun pid => input pid xs) pids.
  op extract_rands (rs : rands_t) (pids : pid_t list) : rand_t list =
    map (fun pid => rand pid rs) pids.
  op extract_traces (tr : traces_t) (pids : pid_t list) : trace_t list =
    map (fun pid => trace pid tr) pids.

end Gate.
