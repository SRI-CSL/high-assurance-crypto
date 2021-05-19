require import Int List.

from General require import PrimeField ListExt.
from SecretSharing require import ASecretSharingScheme.
from MPC require import AGate GateWeak.
from Functionalities require import AdditionFunctionality.

theory AdditionGate.
  clone import AdditionFunctionality.
  import SecretSharingScheme.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t * sinput_t = snd (input pid xs).
  op valid_inputs (xs : inputs_t) : bool = 
    unzip1 xs = pid_set /\
    let sec1 = map (fun pid => (pid, fst (sinput pid xs))) pid_set in
    let sec2 = map (fun pid => (pid, snd (sinput pid xs))) pid_set in
    (exists r s, valid_secret s /\ valid_rand r /\ share r s = sec1) /\ 
    (exists r' s', valid_secret s' /\ valid_rand r' /\ share r' s' = sec2).

  type rand_t.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand : rand_t -> bool.
  op valid_rands (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ (forall pid, pid \in pid_set => valid_rand (rand pid rs)).

  type output_t = secret_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  type msgs_t.
  type in_messages_t = (pid_t * msgs_t) list.
  type out_messages_t = (pid_t * msgs_t) list.

  type trace_t = shares_t * in_messages_t.
  type traces_t = (pid_t * trace_t) list.
  op trace (pid : pid_t) (trs : traces_t) : trace_t = oget (assoc trs pid).

  op get_messages_to (pid : pid_t) (om : out_messages_t) : msgs_t = oget (assoc om pid).
  op get_messages_from (pid : pid_t) (im : in_messages_t) : msgs_t = oget (assoc im pid).
  
  type view_t = input_t * rand_t * trace_t.

  op out_messages_in_messages (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : out_messages_t.
  op out_messages (pid : pid_t) (v : view_t) : out_messages_t = 
    let (xi,ri,tri) = v in
    out_messages_in_messages pid xi ri tri.`2.

  op local_output_share (pid : pid_t) (x : input_t) (r : rand_t) (ims : in_messages_t) : share_t.
  op local_output (pid : pid_t) (v : view_t) : output_t =
    let (x, r, tr) = v in
    let (ys, ims) = tr in
    let yi = local_output_share pid x r tr.`2 in
    if oget (assoc ys pid) = yi then reconstruct ys else witness. 

  op eval : rands_t -> inputs_t -> (pid_t * ((pid_t * msgs_t) list)) list * shares_t.

  axiom eval_domain rs xs : unzip1 (eval rs xs).`2 = pid_set.

  op gate (rs : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let (tr,ys) = eval rs xs in
    let y = reconstruct ys in
    (map (fun pid => (pid, (ys, oget (assoc tr pid)))) pid_set, 
     map (fun pid => (pid, y)) pid_set).

  axiom local_output_share_correct (pid : pid_t) (xs : inputs_t) (rs : rands_t) :
    pid \in pid_set =>
    let (tr, y) = eval rs xs in
    oget (assoc y pid) = local_output_share pid (input pid xs) (rand pid rs) (oget (assoc tr pid)). 
  lemma local_output_correct (pid : pid_t) (xs : inputs_t) (rs : rands_t) :
    pid \in pid_set =>
    let (tr, y) = gate rs xs in
    GateFunctionality.output pid y = local_output pid (input pid xs, rand pid rs, trace pid tr).
  proof.
    progress; move : x1 x2 H0 => tr ys H0.
    rewrite /output /local_output /input /rand /trace; move : H0.
    rewrite /gate /=; move : (local_output_share_correct pid xs rs).
    rewrite H /=.
    have : exists (tr0, y), (tr0, y) = eval rs xs
      by exists (eval rs xs).`1 (eval rs xs).`2 => /#. 
    progress; move : H1 H2; rewrite -H0 /= /input /rand; progress.
    by rewrite !map_assoc //= H1 /=.
  qed.

  axiom out_messages_in_messages_consistency (i j : pid_t) (xs : inputs_t) (rs : rands_t) :
    i \in pid_set => j \in pid_set =>
    let (tr, y) = gate rs xs in
    get_messages_to j (out_messages_in_messages i (input i xs) (rand i rs) (trace i tr).`2) = 
    get_messages_from i (trace j tr).`2.

  lemma messages_consistency (i j : pid_t) (xs : inputs_t) (rs : rands_t) :
    i \in pid_set => j \in pid_set =>
    let (tr, y) = gate rs xs in
    get_messages_to j (out_messages i (input i xs, rand i rs, trace i tr)) = 
    get_messages_from i (trace j tr).`2.
  proof.
    rewrite /out_messages /=.
    move : (out_messages_in_messages_consistency) => /#.
  qed.
(*  pred input_pred (x_fx : inputs_t * GateFunctionality.input_t) = 
    let (xs,fx) = x_fx in
    let (fpub, fsec) = fx in
    let sec1 = map (fun pid => (pid, fst (sinput pid xs))) pid_set in
    let sec2 = map (fun pid => (pid, snd (sinput pid xs))) pid_set in
    reconstruct sec1 = (fst fsec) /\ reconstruct sec2 = (snd fsec).

  pred output_pred (y_fy : outputs_t * GateFunctionality.output_t) = 
    let (y,fy) = y_fy in unzip1 y = pid_set /\ reconstruct y = fy /\F
    valid_secret fy /\ (exists r, SecretSharingScheme.valid_rand r /\ share r fy = y).*)

  axiom eval_preserves_share rs xs :
    valid_inputs xs => valid_rands rs =>
    let (tr,ys) = eval rs xs in 
    exists r, SecretSharingScheme.valid_rand r /\ share r (reconstruct ys) = ys.

  clone import Gate with
    op GateFunctionality.n = n,
    op GateFunctionality.t = t,

    type GateFunctionality.pid_t = pid_t,
    op GateFunctionality.pid_set = pid_set,

    type GateFunctionality.pinput_t = AdditionFunctionality.GateFunctionality.pinput_t,
    type GateFunctionality.sinput_t = AdditionFunctionality.GateFunctionality.sinput_t,
    op GateFunctionality.valid_inputs = AdditionFunctionality.GateFunctionality.valid_inputs,
    type GateFunctionality.output_t = AdditionFunctionality.GateFunctionality.output_t,
    op GateFunctionality.f = AdditionFunctionality.GateFunctionality.f,

    type rand_t = rand_t,
    op rand = rand,
    op valid_rand = valid_rand,

    (*type output_t = output_t,
    op output = output,*)

    (*op to_foutput = reconstruct,*)
    type poutput_t = share_t,

    type msgs_t = msgs_t,
    op get_messages_to = get_messages_to,
    op get_messages_from = get_messages_from,

    op out_messages = out_messages,
    op local_output = local_output,

    op trace = trace,

    op gate = gate
  proof GateFunctionality.pid_set_uniq, GateFunctionality.pid_set_size, local_output_correct,
        messages_consistency. 
  realize GateFunctionality.pid_set_uniq by apply pid_set_uniq.
  realize GateFunctionality.pid_set_size by apply pid_set_size.
  realize local_output_correct by apply local_output_correct.
  realize messages_consistency by apply messages_consistency.

end AdditionGate.
