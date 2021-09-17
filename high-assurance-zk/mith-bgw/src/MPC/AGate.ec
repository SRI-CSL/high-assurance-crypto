require import List Int.

from General require import ListExt Utils.

from Functionalities require import AGateFunctionality.

theory Gate.

  clone import GateFunctionality.

  type rand_t.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand : rand_t -> bool.
  op valid_rands (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ (forall pid, pid \in pid_set => valid_rand (oget (assoc rs pid))).

  type msgs_t.
  type in_messages_t = (pid_t * msgs_t) list.
  type out_messages_t = (pid_t * msgs_t) list.

  op get_messages_to : pid_t -> out_messages_t -> msgs_t.
  op get_messages_from : pid_t -> in_messages_t -> msgs_t.

  type poutput_t.
  type poutputs_t = (pid_t * poutput_t) list.
  op poutput (pid : pid_t) (pouts : poutputs_t) : poutput_t = oget (assoc pouts pid).

  type trace_t = poutputs_t * in_messages_t.
  type traces_t = (pid_t * trace_t) list.
  op trace (pid : pid_t) (trs : traces_t) : trace_t = oget (assoc trs pid).
  
  type view_t = input_t * rand_t * trace_t.
  type views_t = (pid_t * view_t) list.

  op view (pid : pid_t) (vs : views_t) : view_t = oget (assoc vs pid).
  op view_input (pid : pid_t) (v : view_t) : input_t = let (x,r,tr) = v in x.
  op view_rand (pid : pid_t) (v : view_t) : rand_t = let (x,r,tr) = v in r.
  op view_trace (pid : pid_t) (v : view_t) : trace_t = let (x,r,tr) = v in tr.

  (*op out_messages : pid_t -> view_t -> out_messages_t.*)
  op local_output : pid_t -> view_t -> output_t.

  op gate : rands_t -> inputs_t -> traces_t * outputs_t.

  axiom correct (rs : rands_t) (xs : inputs_t) :
    GateFunctionality.valid_inputs xs =>
    valid_rands rs => snd (gate rs xs) = f xs.

  axiom correct_domain (rs : rands_t) (xs : inputs_t) :
    unzip1 (snd (gate rs xs)) = pid_set /\
    unzip1 (fst (gate rs xs)) = pid_set.

  op consistent_views (vi vj : view_t) (i j : pid_t) : bool.
  op consistent_views_pinput xp (vi vj : view_t) (i j : pid_t) : bool =
    vi.`1.`1 = xp /\ vj.`1.`1 = xp /\ consistent_views vi vj i j.

  axiom local_output_correct (pid : pid_t) (xs : inputs_t) (rs : rands_t) :
    pid \in pid_set =>
    let (tr, y) = gate rs xs in
    output pid y = local_output pid (input pid xs, rand pid rs, trace pid tr). 

  axiom global_consistency xp (vs : views_t) :
    (forall (i j : pid_t), i \in pid_set => j \in pid_set => 
      consistent_views_pinput xp (oget (assoc vs i)) (oget (assoc vs j)) i j)
    <=>
    (exists rs sx, let xs = mk_inputs xp sx in 
                   valid_rands rs /\ valid_inputs xs /\
                   let (tr,y) = gate rs xs in
                   (forall pid, pid \in pid_set => oget (assoc vs pid) =
                     (input pid xs,rand pid rs,trace pid tr))).

  axiom messages_consistency (i j : pid_t) (xs : inputs_t) (rs : rands_t) :
    i \in pid_set => j \in pid_set =>
    let (tr, y) = gate rs xs in
    let vi = (input i xs,rand i rs, trace i tr) in
    let vj = (input j xs,rand j rs, trace j tr) in
    consistent_views vi vj i j.

  op extract_inputs (xs : inputs_t) (pids : pid_t list) : input_t list =
    map (fun pid => input pid xs) pids.
  op extract_rands (rs : rands_t) (pids : pid_t list) : rand_t list =
    map (fun pid => rand pid rs) pids.
  op extract_traces (tr : traces_t) (pids : pid_t list) : trace_t list =
    map (fun pid => trace pid tr) pids.

end Gate.
