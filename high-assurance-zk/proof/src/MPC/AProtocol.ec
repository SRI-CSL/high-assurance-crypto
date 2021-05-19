require import List.

from General require import ListExt.
from Functionalities require import AProtocolFunctionality.

theory Protocol.

  clone import ProtocolFunctionality.
  import Circuit.

  type rand_t.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand : circuit_t -> rand_t -> bool.
  op valid_rands (c : circuit_t) (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ (forall pid, pid \in pid_set => valid_rand c (oget (assoc rs pid))).

  type msgs_t.
  type in_messages_t.
  type out_messages_t.

  op get_messages_from : pid_t -> in_messages_t -> msgs_t.
  op get_messages_to : pid_t -> out_messages_t -> msgs_t.

  type poutput_t.
  type poutputs_t = (pid_t * poutput_t) list.
  op poutput (pid : pid_t) (pouts : poutputs_t) : poutput_t = oget (assoc pouts pid).

  type trace_t = poutputs_t * in_messages_t.
  type traces_t = (pid_t * trace_t) list.
  op trace (pid : pid_t) (trs : traces_t) : trace_t = oget (assoc trs pid).

  type view_t = input_t * rand_t * trace_t.
  type views_t = (pid_t * view_t) list.
  op view (pid : pid_t) (vs : views_t) : view_t = oget (assoc vs pid).

  op out_messages : circuit_t -> pid_t -> view_t -> out_messages_t.
  op local_output : circuit_t -> pid_t -> view_t -> output_t.

  op protocol : circuit_t -> rands_t -> inputs_t -> traces_t * outputs_t.

  axiom correct (c : circuit_t) (rs : rands_t) (xs : inputs_t) :
    ProtocolFunctionality.valid_inputs c xs =>
    valid_rands c rs =>
    snd (protocol c rs xs) = f c xs.

  axiom correct_domain (c : circuit_t) (rs : rands_t) (xs : inputs_t) :
    unzip1 (snd (protocol c rs xs)) = pid_set /\
    unzip1 (fst (protocol c rs xs)) = pid_set.

  axiom local_output_correct (c : circuit_t) (pid : pid_t) (xs : inputs_t) (rs : rands_t) :
    pid \in pid_set =>
    let (tr, y) = protocol c rs xs in
    output pid y = local_output c pid (input pid xs, rand pid rs, trace pid tr). 

  axiom messages_consistency (c : circuit_t) (i j : pid_t) (xs : inputs_t) (rs : rands_t) :
    i \in pid_set => j \in pid_set =>
    let (tr, y) = protocol c rs xs in
    get_messages_to j (out_messages c i (input i xs, rand i rs, trace i tr)) = 
    get_messages_from i (trace j tr).`2.

  op extract_inputs (xs : inputs_t) (pids : pid_t list) : inputs_t =
    map (fun pid => (pid, input pid xs)) pids.
  op extract_rands (rs : rands_t) (pids : pid_t list) : rand_t list =
    map (fun pid => rand pid rs) pids.
  op extract_traces (tr : traces_t) (pids : pid_t list) : trace_t list =
    map (fun pid => trace pid tr) pids.

  op valid_circuit_trace : circuit_t -> in_messages_t -> bool.

  op consistent_views (c : circuit_t) (xp : pinput_t) (vi vj : view_t) (i j : pid_t) =
    let (xi, ri, ti) = vi in
    let (xj, rj, tj) = vj in
    let outj = out_messages c j vj in
    valid_rand c ri /\ valid_rand c rj /\
    xi.`1 = xp /\ xj.`1 = xp /\ valid_circuit_trace c ti.`2 /\ valid_circuit_trace c tj.`2 /\
    (fst vi.`1 = fst vj.`1 /\ fst vi.`1 = xp) /\ 
    get_messages_from j ti.`2 = get_messages_to i (out_messages c j vj) /\
    get_messages_from i tj.`2 = get_messages_to j (out_messages c i vi).

  axiom global_consistency (c : circuit_t) xp (vs : views_t) :
    (forall (i j : pid_t), i \in pid_set => j \in pid_set => 
      consistent_views c xp (oget (assoc vs i)) (oget (assoc vs j)) i j)
    <=>
    (exists rs sx, let xs = map (fun pid => (pid, (xp, oget (assoc sx pid)))) pid_set in 
                   valid_rands c rs /\ valid_inputs c xs /\
                   let (tr,y) = protocol c rs xs in
                   (forall pid, pid \in pid_set => oget (assoc vs pid) = 
                                                   ((input pid xs, rand pid rs, (trace pid tr))))).

end Protocol.
