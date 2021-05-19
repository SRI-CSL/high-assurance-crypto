require import Int List Real.

from General require import PrimeField ListExt.
from SecretSharing require import ASecretSharingScheme.
from MPC require import AGate GateWeak.
from Functionalities require import ConstantFunctionality.

theory ConstantGate.

  clone import ConstantFunctionality.
  import SecretSharingScheme.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t * sinput_t = snd (input pid xs).
  op valid_inputs (xs : inputs_t) : bool =
    unzip1 xs = pid_set /\
    let pub = map (fun pid => (pid, pinput pid xs)) pid_set in
    (forall pid, pid \in pid_set => valid_secret (pinput pid xs)) /\
    (exists c, forall pid, pid \in pid_set => c = pinput pid xs). 

  type rand_t = unit.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand (r : rand_t) : bool = true.
  op valid_rands (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ all (fun r => valid_rand (snd r)) rs.

  type output_t = secret_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  type msgs_t = unit.
  type in_messages_t = shares_t * (pid_t * msgs_t) list. 
  type out_messages_t = (pid_t * msgs_t) list.

  op get_messages_to (pid : pid_t) (ms : out_messages_t) : msgs_t = oget (assoc ms pid).
  op get_messages_from (pid : pid_t) (im : in_messages_t) : msgs_t = 
    let (ys, ims) = im in oget (assoc ims pid).

  type trace_t = in_messages_t.
  type traces_t = (pid_t * in_messages_t) list.
  op trace (pid : pid_t) (tr : traces_t) : in_messages_t = oget (assoc tr pid).
  
  type view_t = input_t * rand_t * (pid_t * msgs_t) list.

  op party_exec (pid : pid_t) (r : rand_t) (x : input_t) : share_t = 
    let pub_enc = public_encoding (fst x) in
    oget (assoc pub_enc pid).
  op empty_trace : (pid_t * msgs_t) list = [].

  op out_messages (pid : pid_t) (v : view_t) : out_messages_t = [].
  op local_output (pid : pid_t) (x : input_t) (r : rand_t) (tr : trace_t) : output_t = fst x.

  op eval (rs : rands_t) (xs : inputs_t) : (pid_t * ((pid_t * msgs_t) list)) list * shares_t =
    let tr = map (fun pid => (pid, empty_trace)) pid_set in
    let ys = map (fun pid => (pid, party_exec pid (oget (assoc rs pid)) 
                                              (oget (assoc xs pid)))) pid_set in
    (tr,ys).

  op gate (rs : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let (tr,ys) = eval rs xs in
    let y = reconstruct ys in
    (map (fun pid => (pid, (ys, oget (assoc tr pid)))) pid_set, 
     map (fun pid => (pid, y)) pid_set).

(*  pred input_pred (x_fx : inputs_t * GateFunctionality.input_t) = 
    let (xs,fx) = x_fx in
    let (fpub, fsec) = fx in
    fpub = pinput (head witness pid_set) xs.
  pred output_pred (y_fy : outputs_t * GateFunctionality.output_t) = 
    let (y,fy) = y_fy in unzip1 y = pid_set /\ reconstruct y = fy /\
    valid_secret fy /\ (exists r, SecretSharingScheme.valid_rand r /\ share r fy = y).*)

  clone import Gate with
    op GateFunctionality.n = n,
    op GateFunctionality.t = t,

    type GateFunctionality.pid_t = pid_t,
    op GateFunctionality.pid_set = pid_set,

    type GateFunctionality.pinput_t = ConstantFunctionality.GateFunctionality.pinput_t,
    type GateFunctionality.sinput_t = ConstantFunctionality.GateFunctionality.sinput_t,
    op GateFunctionality.valid_inputs = ConstantFunctionality.GateFunctionality.valid_inputs,
    type GateFunctionality.output_t = ConstantFunctionality.GateFunctionality.output_t,
    op GateFunctionality.f = ConstantFunctionality.GateFunctionality.f,

    type rand_t = rand_t,
    op rand = rand,
    op valid_rand = valid_rand,

    (*type output_t = output_t,
    op output = output,
    op GateFunctionality.to_foutput = reconstruct,*)
    type msgs_t = msgs_t,
    op get_messages_to = get_messages_to,
    op get_messages_from = get_messages_from,

    op out_messages = out_messages,
    op local_output = local_output,

    op trace = trace,

    op gate = gate
  proof *.
  realize GateFunctionality.n_pos by apply n_pos.
  realize GateFunctionality.t_pos by apply t_pos.
  realize GateFunctionality.pid_set_uniq by apply pid_set_uniq.
  realize GateFunctionality.pid_set_size by apply pid_set_size.
  realize correct.
    rewrite /valid_input /valid_inputs /valid_rands /output_pred /input_pred 
            /gate /eval /f /party_exec /pinput /input /=; progress.
rewrite /to_foutput.
have ->: (map (fun (pid : pid_t) => (pid, oget (assoc (public_encoding (oget (assoc xs pid)).`1) pid))) pid_set) = (map (fun (pid : pid_t) => (pid, oget (assoc (public_encoding c) pid))) pid_set).
rewrite -eq_in_map => pid; progress.
by rewrite (H1 pid) //=.

have ->: (map (fun (pid : pid_t) => (pid, oget (assoc (public_encoding c) pid))) pid_set) = public_encoding c.
rewrite (eq_assoc_map (public_encoding c)).
smt.
have ->: unzip1 (public_encoding c) = pid_set by smt.
rewrite -eq_in_map => pid; progress.
by rewrite map_assoc //=.
rewrite -eq_in_map => pid; progress.
rewrite -(H1 pid) //=.
have : valid_secret c.
rewrite (H1 (head witness pid_set)).
by smt(n_pos pid_set_size).
rewrite H0.
by smt(n_pos pid_set_size).
progress.
move : (public_encoding_correct c).
progress.
  qed.
  realize local_output_correct.
    rewrite /valid_input /valid_inputs /valid_rands /output_pred /input_pred 
            /gate /eval /f /party_exec /pinput /input /local_output /output /=; progress.
    rewrite map_assoc //=.
move : (public_encoding_reconstruct (oget (assoc xs pid)).`1).
progress.
rewrite -(H0 pid) //=.

smt.


have ->: (map (fun (pid0 : pid_t) => (pid0, oget (assoc (public_encoding (oget (assoc xs pid0)).`1) pid0))) pid_set) = (public_encoding (oget (assoc xs pid0)).`1)

rewrite map_assoc //=.
by rewrite H0 //=.
  qed.
  realize messages_consistency.
    rewrite /valid_input /valid_inputs /valid_rands /output_pred /gate /eval
            /get_messages_to /get_messages_from /trace /out_messages /f /= => i j xs rs.
    rewrite /valid_rand; progress.
    by rewrite !assoc_nil /= map_assoc //.
  qed.
  realize correct_domain. 
    rewrite /valid_input /valid_inputs /valid_rands /output_pred /gate /eval
            /get_messages_to /get_messages_from /trace /out_messages /f /= => rs xs.
by rewrite -!map_comp /(\o) /= map_id /=. 
  qed.

  op simulator (rs : rands_t) (xs : inputs_t) (cr : pid_t list) : outputs_t * views_t =
    (map (fun pid => (pid, pinput pid xs)) cr, map (fun pid => (pid, (input pid xs, rand pid rs, empty_trace))) cr).

  clone import WeakSecurity as ConstantPrivacy with 
    theory Gate <- Gate, type env_input_t = secret_t, op simulator = simulator.

  section Security.

    declare module D : Distinguisher_t{RealEvaluator,IdealEvaluator}.

    module R : Rand_t = {
      proc gen(aux : aux_t, cr : pid_t list) : rands_t = {
        return (map (fun pid => (pid, ())) pid_set);
      }
    }.

    equiv real_ideal_equiv :
      GameReal(D,R).main ~ GameIdeal(D,R).main :
      ={glob D, glob R, x, aux} /\ valid_secret x{1} ==> ={res}.
    proof.
      proc.
      seq 1 1 : (#pre /\ ={xs,cr}); first by call (_ : true).
      seq 1 1 : (#pre /\ ={r}); first by call (_ : true).
      (if; first by smt()); last by rnd.
      inline *; call (_ : true); wp; skip; progress.
      rewrite /simulator /gate /eval /= /trace /= -eq_in_map => pid; progress.
      rewrite /output /party_exec /pinput /input !map_assoc //=; first by move : H2; rewrite /valid_corrupted_set => /#. 
      rewrite !map_assoc //= 1:/#.
move : (public_encoding_reconstruct (oget (assoc xs{2} pid)).`1).
progress.
by rewrite H4 //= 1:/#.

      rewrite /simulator /gate /eval /= /trace /= -eq_in_map => pid; progress.
      by rewrite /output /party_exec /pinput /input !map_assoc //=. 
      by rewrite !map_assoc //= 1:/#.
    qed.

    lemma security &m x aux :
      valid_secret x =>
      Pr [ GameReal(D,R).main(x,aux) @ &m : res ] - 
      Pr [ GameIdeal(D,R).main(x,aux) @ &m : res ] = 0%r.
    proof. 
      progress.
      have ?: Pr [ GameReal(D,R).main(x,aux) @ &m : res ] = 
              Pr [ GameIdeal(D,R).main(x,aux) @ &m : res ] by byequiv real_ideal_equiv. 
      by smt().
    qed.
    
  end section Security.

end ConstantGate.
