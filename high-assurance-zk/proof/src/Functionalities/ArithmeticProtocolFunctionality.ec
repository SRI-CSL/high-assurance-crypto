require import Int List Core.

from General require import ListExt PrimeField.

from Circuit require import ArithmeticCircuit.
from SecretSharing require import ASecretSharingScheme.
from Functionalities require import AProtocolFunctionality AdditionFunctionality MultiplicationFunctionality SMultiplicationFunctionality.

theory ArithmeticProtocolFunctionality.
  clone import SecretSharingScheme with type secret_t = t.
  clone import ArithmeticCircuit with op valid_constant = valid_secret.
  import Circuit.

  type pinput_t = secret_t list.
  type sinput_t = share_t list.
  type input_t = pinput_t * sinput_t.
  type inputs_t = (pid_t * input_t) list.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t = snd (input pid xs).
  op valid_inputs_topology (topo : topology_t) (xs : inputs_t) : bool =
    let (np, ns, m, q) = topo in
    (forall pid, pid \in pid_set => size (pinput pid xs) = np) /\
    (forall pid, pid \in pid_set => size (sinput pid xs) = np+ns) /\
    (forall k, 0 <= k < np => 
      let pub = map (fun pid => (pid, nth witness (pinput pid xs) k)) pid_set in
      (forall pid, pid \in pid_set => valid_secret (oget (assoc pub pid)))) /\
    (forall k, 0 <= k < np => 
      let pub = map (fun pid => (pid, nth witness (pinput pid xs) k)) pid_set in
      (exists s, all (fun v => snd v = s) pub)) /\
    (forall k, np <= k < np+ns => 
      let sec = map (fun pid => (pid, nth witness (sinput pid xs) k)) pid_set in
      (exists r s, valid_secret s /\ valid_rand r /\ share r s = sec)).
  op valid_inputs (c : circuit_t) (xs : inputs_t) : bool = 
    valid_circuit c /\ unzip1 xs = pid_set /\
    let (topo, gg) = c in valid_inputs_topology topo xs.

  type output_t = Domain.wire_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  op eval_gates (gg : gates_t) (x : t list * t list) : t =
    with gg = PInput w => let (xp,xs) = x in nth fzero xp w
    with gg = SInput w => let (xp,xs) = x in nth fzero xs w
    with gg = Constant gid c => c
    with gg = Addition gid wl wr => 
      let vwl = eval_gates wl x in
      let vwr = eval_gates wr x in fadd vwl vwr

    with gg = Multiplication gid wl wr => 
      let vwl = eval_gates wl x in
      let vwr = eval_gates wr x in fmul vwl vwr

    with gg = SMultiplication gid wl wr => 
      let vwl = eval_gates wl x in
      let vwr = eval_gates wr x in fmul vwl vwr.

  op eval_circuit (gg : gates_t) (x : t list * t list) : output_t = eval_gates gg x.

  op f (c : circuit_t) (xs : inputs_t) : outputs_t =
    let (np,ns,m,q) = fst c in
    let cc = snd c in
    let pubs = pinput (head witness pid_set) xs in
    let secs = map (fun k => map (fun pid => (pid, nth witness (sinput pid xs) k)) pid_set) (range 0 (np+ns)) in
    let secs = map (fun sec => (reconstruct sec)) secs in
    let y = eval_circuit cc (pubs, secs) in
    map (fun pid => (pid, y)) pid_set. 

  lemma constant_eval gg fxp fxs : 
    is_constant gg => eval_gates gg (fxp,fxs) = (as_constant gg).`2.
  proof. by elim gg => //. qed.

  clone import ProtocolFunctionality with
    theory Circuit <- ArithmeticCircuit.Circuit,
    op n = n,
    op t = t,
    type pid_t = pid_t,
    op pid_set = pid_set,
    type pinput_t = pinput_t,
    type sinput_t = sinput_t,
    op valid_inputs = valid_inputs,
    type output_t = output_t,
    op f = f,
    op valid_inputs_topology = valid_inputs_topology.

end ArithmeticProtocolFunctionality.
