require import List AuxList Aux Int.

require import ADomain AProtocolFunctionality.

theory Protocol.
  
  clone import ProtocolFunctionality as F.

  type rand_t.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand : circuit_t -> rand_t -> bool.
  op valid_rands (c : circuit_t) (rs : rands_t) : bool = 
    unzip1 rs = F.pid_set /\ (forall pid, pid \in F.pid_set => valid_rand c (oget (assoc rs pid))).

  type in_messages_t.

  type poutput_t.
  type poutputs_t = (pid_t * poutput_t) list.
  op poutput (pid : pid_t) (pouts : poutputs_t) : poutput_t = oget (assoc pouts pid).

  type trace_t = poutputs_t * in_messages_t.
  type traces_t = (pid_t * trace_t) list.
  op trace (pid : pid_t) (trs : traces_t) : trace_t = oget (assoc trs pid).

  type view_t = input_t * (rand_t * trace_t).
  type views_t = (pid_t * view_t) list.
  op view (pid : pid_t) (vs : views_t) : view_t = oget (assoc vs pid).

  op local_output : circuit_t -> pid_t -> view_t -> output_t.

  op protocol : circuit_t -> rands_t -> inputs_t -> traces_t * outputs_t.

  axiom correct (c : circuit_t) (rs : rands_t) (xs : inputs_t) :
    F.valid_circuit c =>
    F.valid_inputs c xs =>
    valid_rands c rs =>
    snd (protocol c rs xs) = f c xs.

  axiom correct_domain (c : circuit_t) (rs : rands_t) (xs : inputs_t) :
    unzip1 (snd (protocol c rs xs)) = F.pid_set /\
    unzip1 (fst (protocol c rs xs)) = F.pid_set.

  op consistent_views (c : circuit_t) (vi vj : view_t) (i j : pid_t) : bool.
  op consistent_views_public (c : circuit_t) xp (vi vj : view_t) (i j : pid_t) : bool =
    vi.`1.`1 = xp /\ vj.`1.`1 = xp /\ consistent_views c vi vj i j.
  op consistent_trace_public c xp vs = 
    (forall (i j : pid_t), i \in F.pid_set => j \in F.pid_set => 
      consistent_views_public c xp (oget (assoc vs i)) (oget (assoc vs j)) i j).

  axiom local_output_correct (c : circuit_t) (pid : pid_t) (xs : inputs_t) (rs : rands_t) :
    pid \in F.pid_set =>
    let (tr, y) = protocol c rs xs in
    output pid y = local_output c pid (input pid xs,(rand pid rs, trace pid tr)). 

  lemma local_output_correct' (c : circuit_t) (pid : pid_t) (xs : inputs_t) (rs : rands_t) :
    pid \in F.pid_set =>
    output pid (protocol c rs xs).`2 = local_output c pid (input pid xs,(rand pid rs, trace pid (protocol c rs xs).`1)). 
    move => H. smt(local_output_correct). qed.

  axiom global_consistency (c : circuit_t) xp (vs : views_t) :
    F.valid_circuit c =>
    (consistent_trace_public c xp vs
    <=>
    (exists rs sx, let xs = mk_inputs xp sx in 
                   valid_rands c rs /\ valid_inputs c xs /\
                   let (tr,y) = protocol c rs xs in
                   (forall pid, pid \in F.pid_set => oget (assoc vs pid) =
                     (input pid xs,(rand pid rs,trace pid tr))))).

  lemma global_consistency' (c : circuit_t) xp (vs : views_t) :
    F.valid_circuit c =>
    (consistent_trace_public c xp vs
    <=>
    (exists rs sx, valid_rands c rs /\ valid_inputs c (mk_inputs xp sx) /\
                   (forall pid, pid \in F.pid_set => oget (assoc vs pid) =
                     (input pid (mk_inputs xp sx),(rand pid rs,trace pid (protocol c rs (mk_inputs xp sx)).`1 ))))).
    move => H. split.
    rewrite global_consistency => |>rs sx H0 H1. rewrite (prod_id (protocol c rs (mk_inputs xp sx))) => |>H2. exists rs sx => |>. 
    progress. rewrite global_consistency => |>. exists rs sx => |>tr o. rewrite (prod_id (protocol c rs (mk_inputs xp sx))) => |>. qed.

  axiom messages_consistency (c : circuit_t) (i j : pid_t) (xs : inputs_t) (rs : rands_t) :
    i \in F.pid_set => j \in F.pid_set =>
    valid_rands c rs =>
    valid_circuit c =>
    valid_inputs c xs =>
    let (tr, y) = protocol c rs xs in
    let vi = (input i xs,(rand i rs,(trace i tr))) in
    let vj = (input j xs,(rand j rs,(trace j tr))) in
    consistent_views c vi vj i j.

  lemma messages_consistency' (c : circuit_t) (i j : pid_t) (xs : inputs_t) (rs : rands_t) :
    i \in F.pid_set => j \in F.pid_set =>
    valid_rands c rs =>
    valid_circuit c =>
    valid_inputs c xs =>
    consistent_views c (input i xs,(rand i rs,(trace i (protocol c rs xs).`1 ))) (input j xs,(rand j rs,(trace j (protocol c rs xs).`1 ))) i j.
  move => H H0 H1 H2 H3. smt(messages_consistency). qed.

  op extract_inputs (xs : inputs_t) (pids : pid_t list) : inputs_t =
    map (fun pid => (pid, input pid xs)) pids.
  op extract_rands (rs : rands_t) (pids : pid_t list) : rand_t list =
    map (fun pid => rand pid rs) pids.
  op extract_traces (tr : traces_t) (pids : pid_t list) : trace_t list =
    map (fun pid => trace pid tr) pids.

end Protocol.

(* Boolean output, for MitH *)

theory BoolProtocol.

  clone import Protocol as P.

  op true_output : P.F.output_t.
  op output_to_bool (o:P.F.output_t) : bool = (o = true_output).

  clone import ProtocolFunctionality as BoolF with
    type circuit_t = F.circuit_t,
    op n = F.n,
    op t = F.t,
    type pid_t = F.pid_t,
    op pid_set = F.pid_set,
    type pinput_t = F.pinput_t,
    type sinput_t = F.sinput_t,
    op valid_circuit = F.valid_circuit,
    op valid_inputs = F.valid_inputs,
    type output_t = bool,
    op f (c:circuit_t) (xs:inputs_t) : outputs_t =
      map (prod idfun output_to_bool) (F.f c xs)
    proof *.
    realize n_pos. rewrite /n F.n_pos. qed.
    realize t_pos. rewrite /t F.t_pos. qed.
    realize pid_set_uniq. rewrite /pid_set F.pid_set_uniq => />*. qed.
    realize pid_set_size. rewrite /pid_set /n F.pid_set_size => />*. qed.

  clone include Protocol with
    theory F = BoolF,
    type rand_t = P.rand_t,
    op valid_rand = P.valid_rand,
    type in_messages_t = P.in_messages_t,
    type poutput_t = P.poutput_t,
    op local_output c i v =
      let o = P.local_output c i v in
      output_to_bool o,
    op protocol c rs ws : traces_t * BoolF.outputs_t =
      let to = P.protocol c rs ws in
      (prod idfun (List.map (prod idfun output_to_bool))) to,
    op consistent_views = P.consistent_views
    proof *.
    realize correct.
    move => c rs xs H H0 H1. rewrite /BoolProtocol.protocol /F.f /BoolF.f => |>. rewrite /prod /idfun => |>. congr. rewrite P.correct => |>. qed.
    realize correct_domain.
    move => c rs xs. rewrite /BoolProtocol.protocol /F.pid_set /prod /idfun => |>. rewrite -map_comp /(\o) => |>. rewrite P.correct_domain => |>. qed.
    realize local_output_correct.
    move => c pid xs rs H. rewrite /BoolProtocol.protocol /F.output /BoolF.output /BoolProtocol.local_output /prod => |>. rewrite assoc_map_prod => |>. rewrite -P.local_output_correct' => |>. rewrite /output => |>. rewrite omap_some => |>. rewrite assocTP. smt(P.correct_domain). qed.
    realize global_consistency.
    move => c xp vs H. rewrite (_:consistent_trace_public=P.consistent_trace_public). progress. rewrite P.global_consistency => |>. split.
    move => rs sx H0 H1. rewrite (prod_id (P.protocol c rs (F.mk_inputs xp sx))) => |>H2. exists rs sx => |>tr o. rewrite (prod_id (BoolProtocol.protocol c rs (F.mk_inputs xp sx))) => |>pid H3. rewrite H2 => |>. 
    move => rs sx H0 H1.  rewrite (prod_id (BoolProtocol.protocol c rs (F.mk_inputs xp sx))) => |>H2. exists rs sx => |>tr o. rewrite (prod_id (P.protocol c rs (F.mk_inputs xp sx))) => |>pid H3. rewrite H2 => |>. qed.
    realize messages_consistency.
    move => c i j xs rs Hi Hj H H0 H1. rewrite (prod_id (BoolProtocol.protocol c rs xs)) => |>. rewrite (_:BoolProtocol.consistent_views=P.consistent_views). progress. rewrite P.messages_consistency' => |>. qed.

end BoolProtocol.
