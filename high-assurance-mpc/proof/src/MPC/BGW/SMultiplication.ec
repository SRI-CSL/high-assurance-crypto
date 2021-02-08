require import Int IntDiv List Distr DList Real.

from General require import PrimeField ListExt FieldPolynomial.
from ArithmeticProtocol require import SMultiplicationGate.
from Functionalities require import SMultiplicationFunctionality.
from MPC require import GatePrivacy.
from SecretSharing require import Shamir.

import Shamir.

theory BGWSMultiplication.

  clone import SMultiplicationFunctionality with theory SecretSharingScheme <- Shamir.

  type rand_t = unit.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand (r : rand_t) : bool = true.
  op valid_rands (rs : rands_t) : bool = all (fun r => valid_rand (snd r)) rs.

  type output_t = share_t.
  type outputs_t = (pid_t * share_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  type msgs_t = t list.
  type in_messages_t = (pid_t * msgs_t) list.
  type out_messages_t = (pid_t * msgs_t) list.

  op get_messages_to (pid : pid_t) (ms : out_messages_t) : msgs_t = odflt [] (assoc ms pid).
  op get_messages_from (pid : pid_t) (ms : in_messages_t) : msgs_t = odflt [] (assoc ms pid).

  type trace_t = in_messages_t.
  type traces_t = (pid_t * in_messages_t) list.
  op trace (pid : pid_t) (tr : traces_t) : in_messages_t = odflt [] (assoc tr pid).
  
  type view_t = input_t * rand_t * in_messages_t.

  op party_exec (r : rand_t) (x : input_t) : output_t = 
    let (pub, sec) = x in fmul pub sec.
  op empty_trace : trace_t = [].

  op out_messages (pid : pid_t) (v : view_t) : out_messages_t = [].
  op local_output (pid : pid_t) (v : view_t) : output_t = 
    let (x, r, tr) = v in
    let (pub, sec) = x in fmul pub sec.

  op gate (rs : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let tr = map (fun pid => (pid, empty_trace)) pid_set in
    let ys = map (fun pid => (pid, party_exec (oget (assoc rs pid)) 
                                              (oget (assoc xs pid)))) pid_set in
    (tr,ys).

  clone import SMultiplicationGate with
    theory SecretSharingScheme <- Shamir,
    type rand_t = rand_t,
    op valid_rand = valid_rand,
    type msgs_t = msgs_t,
    op get_messages_to = get_messages_to,
    op get_messages_from = get_messages_from,
    op out_messages = out_messages,
    op local_output = local_output,
    op gate = gate
  proof *.
  realize Gate.correct.
    rewrite /valid_inputs /valid_input /valid_inputs /valid_rands /valid_rand /output_pred
            /gate /party_exec /f /sum_pair /reconstruct /o /=.
    move => rs xs /=. 
    rewrite /GateFunctionality.pid_set /Shamir.pid_set.
    have ->: (fun (_ : GateFunctionality.pid_t * rand_t) => true) = predT
      by rewrite /predT fun_ext /(==).
    rewrite all_predT /=; progress.
    rewrite H1 -H6. 
    have ->: interpolate fzero ((share r s)) = s.
      move : (Shamir.correct r s).
      by rewrite H6 /valid_rand H2 H3 /= /reconstruct /#. 
    have ->: interpolate fzero (public_encoding c) = c.
      by move : (Shamir.public_encoding_correct c); rewrite H0.
    have ->: (map (fun (pid : pid_t) => (pid, let (pub, sec) = oget (assoc xs pid) in fmul pub sec)) pid_set) = (map (fun (pid : pid_t) => (pid, let (pub, sec) = oget (assoc xs pid) in fmul c (eval pid (update r 0 s)))) pid_set).
      rewrite -eq_in_map => x hx /=.
      move : H1 H6.
      by rewrite /share /= -!eq_in_map /sinput /SMultiplicationFunctionality.input /#.
    have ->: (map (fun (pid : pid_t) => (pid, let (x1, x1) = oget (assoc xs pid) in fmul c (eval pid (update r 0 s)))) pid_set) = (map (fun (pid : pid_t) => (pid, eval pid (smul c (update r 0 s)))) pid_set).
      by rewrite -eq_in_map => x hx /=; rewrite eval_smul => /#.
    rewrite (interpolate_eval pid_set (smul c (update r 0 s))).
      by apply pid_set_uniq.
      by rewrite degree_smul !degree_update0 H3 pid_set_size /max /=; smt(t_pos).
    rewrite -update_smul; first by rewrite expo_diff_count //; rewrite ?H2 ?H7; smt(t_pos).
    rewrite !eval_update0 => //.
      rewrite expo_diff_count //; first by rewrite size_smul; rewrite ?H2 ?H7; smt(t_pos).
      rewrite size_smul => i hi; rewrite smul_expo; first by done.
      by rewrite H5 /#. 
  qed.
  realize Gate.local_output_correct.
    rewrite /local_output /output /gate /party_exec /input /GateFunctionality.pid_set 
            /Shamir.pid_set => />; progress.
    have ->: (map (fun (pid : pid_t) => (pid, let (pub, sec) = oget (assoc xs pid) in fmul pub sec)) pid_set) = (map (fun (pid : pid_t) => (pid, let (pub, sec) = oget (assoc xs pid) in fmul c (eval pid (update r 0 s)))) pid_set).
      rewrite -eq_in_map => x hx /=.
      move : H1 H6.
      by rewrite /share /= -!eq_in_map /sinput /SMultiplicationFunctionality.input /#.
    have ->: (map (fun (pid : pid_t) => (pid, let (x1, x1) = oget (assoc xs pid) in fmul c (eval pid (update r 0 s)))) pid_set) = (map (fun (pid : pid_t) => (pid, eval pid (smul c (update r 0 s)))) pid_set).
      by rewrite -eq_in_map => x hx /=; rewrite eval_smul => /#.
    rewrite map_assoc => //.
    rewrite Core.oget_some /transpose /=.
    move : (assocP xs pid).
    rewrite H /Shamir.pid_set H9 /=; progress.
    rewrite H11 Core.oget_some /=.
    move : H11 H10.
    elim y => pub sec; progress.
    move : H1; rewrite /public_encoding -eq_in_map; progress.
    have ->: pub = pinput pid xs by rewrite /pinput /input => /#.
    have ->: pinput pid xs = c. 
      move : (H1 pid).
      have ->: pid \in Shamir.pid_set by smt().
      by done.
    have ->: sec = eval pid (update r 0 s).
      by move : H6; rewrite /share /= -!eq_in_map /sinput 
         /SMultiplicationFunctionality.input; progress; rewrite H6 => /#.
    by rewrite eval_smul.
  qed.
  realize Gate.messages_consistency.
    rewrite /valid_input /valid_inputs /valid_rand /valid_rands /gate /out_messages
            /empty_trace /trace /get_messages_to /get_messages_from; progress.
    by rewrite map_assoc.
  qed.

  op simulator (rs : rands_t) (xs : inputs_t) (cr : pid_t list) : view_t list =
    (map (fun pid => (oget (assoc xs pid), (), empty_trace)) cr).

  clone import Privacy with 
    theory Gate <- SMultiplicationGate.Gate,
    op simulator = simulator.

  section Security.

    declare module D : Distinguisher_t{RealEvaluator,IdealEvaluator}.

    module R : Rand_t = {
      proc gen(xs : inputs_t, cr : pid_t list) : rands_t = {
        return (map (fun pid => (pid, ())) pid_set);
      }
    }.

    equiv real_ideal_equiv :
      GameReal(D,R).main ~ GameIdeal(D,R).main :
      ={glob D, glob R, xs, cr} /\ valid_inputs xs{1} /\ size cr{1} = t /\ (forall pid, pid \in cr{1} => pid \in pid_set) ==> ={res}.
    proof.
      proc.
      seq 1 1 : (#pre /\ ={r}); first by call (_ : true).
      (if; first by smt()); last by rnd.
      inline *.
      call (_ : true).
      wp; skip; progress.
      move : H H1; rewrite /valid_inputs /valid_rands /valid_rand; progress.
      rewrite /extract_inputs /extract_rands /extract_traces /=.
      rewrite (eq_from_nth (witness, witness, witness) (zip3 (map (transpose SMultiplicationGate.Gate.GateFunctionality.input xs{2}) cr{2}) (map (transpose SMultiplicationGate.Gate.rand r{2}) cr{2}) (map (transpose SMultiplicationGate.Gate.trace ((SMultiplicationGate.Gate.gate r{2} xs{2})).`1) cr{2})) (map (fun (pid : Shamir.pid_t) => (oget (assoc xs{2} pid), tt, empty_trace)) cr{2})) => //.
        by rewrite size_zip3 !size_map /min /#.
        rewrite size_zip3 !size_map /min /=.
        have ->: size cr{2} < size cr{2} <=> false by smt().
        simplify; progress.
        rewrite nth_zip3; first by rewrite !size_map.
        rewrite !size_map => //.
        rewrite !(nth_map witness (witness,witness,witness) _ _ _) => //.
        rewrite !(nth_map witness witness _ _ _) => //.
        simplify; rewrite /input /trace /= /gate /= map_assoc.
          by rewrite H9 mem_nth.
        by rewrite Core.oget_some.
    qed.

    lemma security &m xs cr :
      valid_inputs xs =>
      size cr = t => 
      (forall pid, pid \in cr => pid \in pid_set) =>
      Pr [ GameReal(D,R).main(xs,cr) @ &m : res ] - Pr [ GameIdeal(D,R).main(xs,cr) @ &m : res ] = 0%r.
    proof. 
      progress.
      have ?: Pr [ GameReal(D,R).main(xs,cr) @ &m : res ] = Pr [ GameIdeal(D,R).main(xs,cr) @ &m : res ] by byequiv real_ideal_equiv. 
      by smt().
    qed.
    
  end section Security.

end BGWSMultiplication.
