require import Int IntDiv List Distr DList Real.

from General require import PrimeField ListExt FieldPolynomial Utils.
from ArithmeticProtocol require import InputGate.
from Functionalities require import InputFunctionality.
from MPC require import GateWeak.
from SecretSharing require import Shamir.

theory BGWInput.

  const n : {int | 2 <= n} as n_pos.
  const t : {int | 0 <= t < n%/2} as t_pos.

  clone import Shamir with
    op n = n,
    op t = t.

  type pinput_t = unit.
  type sinput_t = share_t.
  type input_t = pinput_t * sinput_t.
  type inputs_t = (pid_t * input_t) list.

  op input (pid : pid_t) (xs : inputs_t) : input_t = oget (assoc xs pid).
  op pinput (pid : pid_t) (xs : inputs_t) : pinput_t = fst (input pid xs).
  op sinput (pid : pid_t) (xs : inputs_t) : sinput_t = snd (input pid xs).
  op valid_inputs (xs : inputs_t) : bool = 
    unzip1 xs = pid_set /\
    let sec = map (fun pid => (pid, sinput pid xs)) pid_set in
    (exists s, sumt (map snd sec) = s). 

  type rand_t = polynomial.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand (r : rand_t) : bool = Shamir.valid_rand r witness.
  op valid_rands (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ (forall pid, pid \in pid_set => valid_rand (oget (assoc rs pid))).

  type output_t = secret_t.
  type outputs_t = (pid_t * output_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  type msgs_t = t.
  type in_messages_t = (pid_t * msgs_t) list.
  type out_messages_t = (pid_t * msgs_t) list.

  op get_messages_to (pid : pid_t) (ms : out_messages_t) : msgs_t = oget (assoc ms pid).
  op get_messages_from (pid : pid_t) (ms : in_messages_t) : msgs_t = oget (assoc ms pid).

  type trace_t = shares_t * in_messages_t.
  type traces_t = (pid_t * in_messages_t) list.
  op trace (pid : pid_t) (tr : traces_t) : in_messages_t = oget (assoc tr pid).
  
  type view_t = input_t * rand_t * trace_t.

  op party_exec1 (r : rand_t) (x : input_t) : (pid_t * share_t) list = 
    Shamir.share r x.`2.

  op party_exec2 (ms : (pid_t * share_t) list) : output_t = 
    sumt (map snd ms). (*interpolate fzero ms.*)

  op out_messages_in_messages (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : out_messages_t = party_exec1 r x.

  op local_output_share (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : share_t =
    party_exec2 ims.

  op eval (rs : rands_t) (xs : inputs_t) : (pid_t * ((pid_t * msgs_t) list)) list * shares_t =
    let p1s = map (fun pid => (pid, party_exec1 (oget (assoc rs pid)) (oget (assoc xs pid)))) pid_set in
    let ms = map (fun pid => (pid, map (fun ms => let (sender, m) = ms in (sender, get_messages_to pid m)) p1s)) pid_set in 
    let p2s = map (fun pid => (pid, party_exec2 (oget (assoc ms pid)))) pid_set in
    (ms, p2s).

print InputFunctionality.SecretSharingScheme.n.

  clone import InputGate with
    op InputFunctionality.SecretSharingScheme.n = Shamir.SecretSharingScheme.n,
    op InputFunctionality.SecretSharingScheme.t = Shamir.SecretSharingScheme.t,
    type InputFunctionality.SecretSharingScheme.pid_t = Shamir.SecretSharingScheme.pid_t,
    op InputFunctionality.SecretSharingScheme.pid_set = Shamir.SecretSharingScheme.pid_set,
    op InputFunctionality.SecretSharingScheme.valid_secret = Shamir.SecretSharingScheme.valid_secret,
    type InputFunctionality.SecretSharingScheme.share_t = Shamir.SecretSharingScheme.share_t,
    type InputFunctionality.SecretSharingScheme.rand_t = Shamir.SecretSharingScheme.rand_t,
    op InputFunctionality.SecretSharingScheme.valid_rand = Shamir.SecretSharingScheme.valid_rand,
    op InputFunctionality.SecretSharingScheme.share = Shamir.SecretSharingScheme.share,
    op InputFunctionality.SecretSharingScheme.public_encoding = Shamir.SecretSharingScheme.public_encoding,
    op InputFunctionality.SecretSharingScheme.pub_reconstruct = Shamir.SecretSharingScheme.pub_reconstruct,
    op InputFunctionality.SecretSharingScheme.reconstruct = Shamir.SecretSharingScheme.reconstruct,
    op InputFunctionality.SecretSharingScheme.get_party_share = Shamir.SecretSharingScheme.get_party_share,

    type rand_t = rand_t,
    op valid_rand = valid_rand,
    type msgs_t = msgs_t,
    op get_messages_to = get_messages_to,
    op get_messages_from = get_messages_from,
    op out_messages_in_messages = out_messages_in_messages,
    op local_output_share = local_output_share,
    op eval = eval
  proof InputFunctionality.GateFunctionality.n_pos, 
        InputFunctionality.GateFunctionality.t_pos,
        InputFunctionality.GateFunctionality.pid_set_size,
        InputFunctionality.GateFunctionality.pid_set_uniq,
        Gate.GateFunctionality.n_pos,
        Gate.GateFunctionality.t_pos,
        InputFunctionality.SecretSharingScheme.n_pos,
        InputFunctionality.SecretSharingScheme.t_pos,
        InputFunctionality.SecretSharingScheme.pid_set_size,
        InputFunctionality.SecretSharingScheme.pid_set_uniq,
        InputFunctionality.SecretSharingScheme.correct,
        InputFunctionality.SecretSharingScheme.size_share,
        InputFunctionality.SecretSharingScheme.unzip1_share,
        InputFunctionality.SecretSharingScheme.public_encoding_correct,
        InputFunctionality.SecretSharingScheme.size_public_encoding,
        InputFunctionality.SecretSharingScheme.unzip1_public_encoding,
        InputFunctionality.SecretSharingScheme.public_encoding_inj,
        InputFunctionality.SecretSharingScheme.public_encoding_reconstruct,
        InputFunctionality.SecretSharingScheme.public_encoding_rand,
        eval_domain, local_output_share_correct, out_messages_in_messages_consistency,
        eval_preserves_share, Gate.correct, Gate.correct_domain.
  realize InputFunctionality.GateFunctionality.n_pos by apply n_pos.
  realize InputFunctionality.GateFunctionality.t_pos by apply t_pos.
  realize InputFunctionality.GateFunctionality.pid_set_size by apply pid_set_size.
  realize InputFunctionality.GateFunctionality.pid_set_uniq by apply pid_set_uniq.
  realize Gate.GateFunctionality.n_pos by apply n_pos.
  realize Gate.GateFunctionality.t_pos by apply t_pos.
  realize InputFunctionality.SecretSharingScheme.n_pos by apply n_pos.
  realize InputFunctionality.SecretSharingScheme.t_pos by apply t_pos.
  realize InputFunctionality.SecretSharingScheme.pid_set_size by apply pid_set_size.
  realize InputFunctionality.SecretSharingScheme.pid_set_uniq by apply pid_set_uniq.
  realize InputFunctionality.SecretSharingScheme.correct by move : Shamir.SecretSharingScheme.correct => /#.
  realize InputFunctionality.SecretSharingScheme.size_share by move : Shamir.SecretSharingScheme.size_share => /#.
  realize InputFunctionality.SecretSharingScheme.unzip1_share by move : Shamir.SecretSharingScheme.unzip1_share => /#.
  realize InputFunctionality.SecretSharingScheme.public_encoding_correct by move : Shamir.SecretSharingScheme.public_encoding_correct => /#.
  realize InputFunctionality.SecretSharingScheme.size_public_encoding by move : Shamir.SecretSharingScheme.size_public_encoding => /#.
  realize InputFunctionality.SecretSharingScheme.unzip1_public_encoding by move : Shamir.SecretSharingScheme.unzip1_public_encoding => /#.
  realize InputFunctionality.SecretSharingScheme.public_encoding_inj by move : Shamir.SecretSharingScheme.public_encoding_inj => /#.
  realize InputFunctionality.SecretSharingScheme.public_encoding_reconstruct by move : Shamir.SecretSharingScheme.public_encoding_reconstruct => /#.
  realize InputFunctionality.SecretSharingScheme.public_encoding_rand by move : Shamir.SecretSharingScheme.public_encoding_rand => /#.
  realize eval_domain.
rewrite /eval /=; progress.
by rewrite -map_comp /(\o) /= map_id //=.
  qed.
  realize local_output_share_correct.
rewrite /eval /= /party_exec2.
progress.
rewrite !map_assoc //=.
by rewrite !map_assoc //=.
  qed.
  realize out_messages_in_messages_consistency.
rewrite /gate /eval /= /party_exec1.
progress.
rewrite /get_messages_to /= /get_messages_from /= /trace /=.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
rewrite /rand /=.
rewrite /out_messages_in_messages /= /party_exec1 /input /=.
rewrite -map_comp /(\o) /=.
by rewrite !map_assoc //=.
  qed.  
  realize Gate.correct.
    rewrite /valid_input /valid_inputs /valid_rands /valid_rand /valid_secret /sinput /input /output_pred /gate /eval /f /party_exec1 /party_exec2 /Shamir.SecretSharingScheme.pid_set /reconstruct /sinput /input /input_pred. 
    move => rs xs /=. progress.
    rewrite -eq_in_map => pid; progress.
    rewrite -!map_comp /(\o) /=.
    have ->: (fun (pid0 : pid_t) => (pid0, sumt (unzip2 (oget (assoc (map (fun (pid1 : pid_t) => (pid1, map (fun (ms : pid_t * BGWInput.out_messages_t) => let (sender, m) = ms in (sender, (BGWInput.get_messages_to pid1 m))) (map (fun (pid2 : pid_t) => (pid2, share (oget (assoc rs pid2)) (oget (assoc xs pid2)).`2)) pid_set))) pid_set) pid0))))) = (fun (pid0 : pid_t) => (pid0, sumt (unzip2 (oget (assoc (map (fun (pid1 : pid_t) => (pid1, map ((fun (ms : pid_t * BGWInput.out_messages_t) => let (sender, m) = ms in (sender, (BGWInput.get_messages_to pid1 m))) \o (fun (pid2 : pid_t) => (pid2, share (oget (assoc rs pid2)) (oget (assoc xs pid2)).`2))) pid_set)) pid_set) pid0))))). 
      rewrite fun_ext /(==) => pid'; progress.
      do 4!congr; rewrite -eq_in_map => pid''; progress.
      by rewrite -map_comp /(\o) //=.
    rewrite /(\o) //=.
    have ->: map (fun (pid0 : pid_t) => (pid0, sumt (unzip2 (oget (assoc (map (fun (pid1 : pid_t) => (pid1, map (fun (x : pid_t) => (x, (BGWInput.get_messages_to pid1 (share (oget (assoc rs x)) (oget (assoc xs x)).`2)))) pid_set)) pid_set) pid0))))) pid_set = map (fun (pid0 : pid_t) => (pid0, sumt (unzip2 (map (fun (x : pid_t) => (x, (BGWInput.get_messages_to pid0 (share (oget (assoc rs x)) (oget (assoc xs x)).`2)))) pid_set)))) pid_set.
      rewrite -eq_in_map => pid'; progress.
      do 2!congr.
      by rewrite !map_assoc //=.
    have ->: map (fun (pid0 : pid_t) => (pid0, sumt (unzip2 (map (fun (x : pid_t) => (x, (BGWInput.get_messages_to pid0 (share (oget (assoc rs x)) (oget (assoc xs x)).`2)))) pid_set)))) pid_set = map (fun (pid0 : pid_t) => (pid0, sumt (map (snd \o (fun (x : pid_t) => (x, (BGWInput.get_messages_to pid0 (share (oget (assoc rs x)) (oget (assoc xs x)).`2))))) pid_set))) pid_set.
      rewrite -eq_in_map => pid'; progress.
      by rewrite -map_comp /(\o) /=.
    rewrite /(\o) /= /get_messages_to /share /=.
    have ->: map (fun (pid0 : pid_t) => (pid0, sumt (map (fun (x : pid_t) => oget (assoc (map (fun (pid1 : coeficient) => (pid1, eval pid1 (update (oget (assoc rs x)) 0 (oget (assoc xs x)).`2))) pid_set) pid0)) pid_set))) pid_set = map (fun (pid0 : pid_t) => (pid0, sumt (map (fun (x : pid_t) => eval pid0 (update (oget (assoc rs x)) 0 (oget (assoc xs x)).`2)) pid_set))) pid_set.
      rewrite -eq_in_map => pid'; progress.
      congr.
      rewrite -eq_in_map => pid''; progress.
      by rewrite !map_assoc //=.
    have ->: map (fun (pid0 : pid_t) => (pid0, sumt (map (fun (x : pid_t) => eval pid0 (update (oget (assoc rs x)) 0 (oget (assoc xs x)).`2)) pid_set))) pid_set = map (fun (pid0 : pid_t) => (pid0, eval pid0 (update (foldr (fun (p : t * polynomial) (st : polynomial) => add st p.`2) pzero rs) 0 (sumt (map snd (map (fun x => (x, oget (assoc xs x)).`2) pid_set)))))) pid_set.
      rewrite -eq_in_map => pid'; progress.
      by rewrite sumt_map_eval //; first by smt(pid_set_uniq).
    rewrite -map_comp /(\o). 
    rewrite (interpolate_eval pid_set (update (foldr (fun (p : t * polynomial) (st : polynomial) => add st p.`2) pzero rs) 0 (sumt (map (fun (x : GateFunctionality.pid_t) => (x, oget (assoc xs x)).`2.`2) pid_set)))); first by smt(pid_set_uniq).
      + rewrite degree_update0 (degree_foldr_add rs t). 
        + rewrite H0; progress.
          by move : (H1 x); rewrite H3 //=.
        by smt(pid_set_size t_pos).
    rewrite eval_update0. 
      + rewrite count_expos_foldr_add //=. 
        + rewrite H0; progress.
          rewrite expo_diff_count //=.
            + move : (H1 x); rewrite H3 //=.
              by smt(pid_set_size t_pos).
            + move : (H1 x); rewrite H3 //=.
              by smt(pid_set_size t_pos).
    by smt().
  qed.
  realize Gate.correct_domain.
    by move => rs xs; rewrite /gate /eval /= /party_exec -!map_comp /(\o) /= !map_id /pid_set.
  qed.
  realize eval_preserves_share.
rewrite /valid_inputs /valid_rands /eval /pid_set /sinput /pinput /input /valid_secret /valid_rand.
progress.
rewrite /party_exec2 /party_exec1 /= /reconstruct /=.
    have ->: (fun (pid0 : pid_t) => (pid0, sumt (unzip2 (oget (assoc (map (fun (pid1 : pid_t) => (pid1, map (fun (ms : pid_t * BGWInput.out_messages_t) => let (sender, m) = ms in (sender, (BGWInput.get_messages_to pid1 m))) (map (fun (pid2 : pid_t) => (pid2, share (oget (assoc rs pid2)) (oget (assoc xs pid2)).`2)) pid_set))) pid_set) pid0))))) = (fun (pid0 : pid_t) => (pid0, sumt (unzip2 (oget (assoc (map (fun (pid1 : pid_t) => (pid1, map ((fun (ms : pid_t * BGWInput.out_messages_t) => let (sender, m) = ms in (sender, (BGWInput.get_messages_to pid1 m))) \o (fun (pid2 : pid_t) => (pid2, share (oget (assoc rs pid2)) (oget (assoc xs pid2)).`2))) pid_set)) pid_set) pid0))))). 
      rewrite fun_ext /(==) => pid'; progress.
      do 4!congr; rewrite -eq_in_map => pid''; progress.
      by rewrite -map_comp /(\o) //=.
    rewrite /(\o) //=.
    have ->: map (fun (pid0 : pid_t) => (pid0, sumt (unzip2 (oget (assoc (map (fun (pid1 : pid_t) => (pid1, map (fun (x : pid_t) => (x, (BGWInput.get_messages_to pid1 (share (oget (assoc rs x)) (oget (assoc xs x)).`2)))) pid_set)) pid_set) pid0))))) pid_set = map (fun (pid0 : pid_t) => (pid0, sumt (unzip2 (map (fun (x : pid_t) => (x, (BGWInput.get_messages_to pid0 (share (oget (assoc rs x)) (oget (assoc xs x)).`2)))) pid_set)))) pid_set.
      rewrite -eq_in_map => pid'; progress.
      do 2!congr.
      by rewrite !map_assoc //=.
    have ->: map (fun (pid0 : pid_t) => (pid0, sumt (unzip2 (map (fun (x : pid_t) => (x, (BGWInput.get_messages_to pid0 (share (oget (assoc rs x)) (oget (assoc xs x)).`2)))) pid_set)))) pid_set = map (fun (pid0 : pid_t) => (pid0, sumt (map (snd \o (fun (x : pid_t) => (x, (BGWInput.get_messages_to pid0 (share (oget (assoc rs x)) (oget (assoc xs x)).`2))))) pid_set))) pid_set.
      rewrite -eq_in_map => pid'; progress.
      by rewrite -map_comp /(\o) /=.
    rewrite /(\o) /= /get_messages_to /share /=.
    have ->: map (fun (pid0 : pid_t) => (pid0, sumt (map (fun (x : pid_t) => oget (assoc (map (fun (pid1 : coeficient) => (pid1, eval pid1 (update (oget (assoc rs x)) 0 (oget (assoc xs x)).`2))) pid_set) pid0)) pid_set))) pid_set = map (fun (pid0 : pid_t) => (pid0, sumt (map (fun (x : pid_t) => eval pid0 (update (oget (assoc rs x)) 0 (oget (assoc xs x)).`2)) pid_set))) pid_set.
      rewrite -eq_in_map => pid'; progress.
      congr.
      rewrite -eq_in_map => pid''; progress.
      by rewrite !map_assoc //=.
    have ->: map (fun (pid0 : pid_t) => (pid0, sumt (map (fun (x : pid_t) => eval pid0 (update (oget (assoc rs x)) 0 (oget (assoc xs x)).`2)) pid_set))) pid_set = map (fun (pid0 : pid_t) => (pid0, eval pid0 (update (foldr (fun (p : t * polynomial) (st : polynomial) => add st p.`2) pzero rs) 0 (sumt (map snd (map (fun x => (x, oget (assoc xs x)).`2) pid_set)))))) pid_set.
      rewrite -eq_in_map => pid'; progress.
      by rewrite sumt_map_eval //; first by smt(pid_set_uniq).
    rewrite -map_comp /(\o). 
    have ->: (interpolate fzero (map (fun (pid0 : pid_t) => (pid0, eval pid0 (update (foldr (fun (p : t * polynomial) (st : polynomial) => add st p.`2) pzero rs) 0 (sumt (map (fun (x : InputFunctionality.SecretSharingScheme.pid_t) => (x, oget (assoc xs x)).`2.`2) pid_set))))) pid_set)) = eval fzero (update (foldr (fun (p : t * polynomial) (st : polynomial) => add st p.`2) pzero rs) 0 (sumt (map (fun (x : InputFunctionality.SecretSharingScheme.pid_t) => (x, oget (assoc xs x)).`2.`2) pid_set))).
      rewrite (interpolate_eval pid_set (update (foldr (fun (p : t * polynomial) (st : polynomial) => add st p.`2) pzero rs) 0 (sumt (map (fun (x : pid_t) => (x, oget (assoc xs x)).`2.`2) pid_set)))); first by smt(pid_set_uniq).
        + rewrite degree_update0 (degree_foldr_add rs t). 
          + rewrite H0; progress.
            by move : (H1 x); rewrite H2 //=.
          by smt(pid_set_size t_pos).
      rewrite eval_update0 //=. 
        + rewrite count_expos_foldr_add //=. 
          + rewrite H0; progress.
            rewrite expo_diff_count //=.
              + move : (H1 x); rewrite H2 //=.
                by smt(pid_set_size t_pos).
              + move : (H1 x); rewrite H2 //=.
                by smt(pid_set_size t_pos).
    exists (foldr (fun (p : t * polynomial) (st : polynomial) => add st p.`2) pzero rs).
    rewrite (degree_foldr_add rs t).
      + rewrite H0; progress.
        by move : (H1 x); rewrite H2 /rand //=.
    split. split => //=. split.
    rewrite (size_foldr_add rs (t+1)) //=.
      + rewrite H0; progress.
        by move : (H1 x); rewrite H2 /rand //=.
      + progress; rewrite (expos_add_foldr rs t) //=.
        + rewrite H0; progress.
          move : (H1 x); rewrite H4 //=; progress.
          by rewrite H9 //=.
    rewrite -eq_in_map => pid; progress.
    rewrite eval_update0 //=.
      + rewrite expo_diff_count //=.
        + rewrite (size_foldr_add _ (t+1)) //=.
          + rewrite H0; progress.
            by move : (H1 x); rewrite H3 /rand //=.
          by smt(t_pos).
        rewrite (size_foldr_add _ (t+1)).
          + rewrite H0; progress.
            by move : (H1 x); rewrite H3 /rand //=.
          + progress; rewrite (expos_add_foldr rs t) //=.
            + rewrite H0; progress.
              move : (H1 x); rewrite H5 //=; progress.
              by rewrite H10 //=.
  qed.

  op simulator (rs : rands_t) (xs : inputs_t) (cr : pid_t list) : 
    InputGate.Gate.poutputs_t * 
    (pid_t * (InputFunctionality.input_t * 
              InputGate.Gate.rand_t * 
              InputGate.Gate.in_messages_t)) list =
    let pub = fst (oget (assoc xs (head witness cr))) in
    let xs' = map (fun pid => (pid, if pid \in cr then oget (assoc xs pid) else (pub, fzero))) pid_set in
    let (tr,ys) = eval rs xs' in
    (map (fun pid => (pid, output pid ys)) cr,
     map (fun pid => (pid, (oget (assoc xs pid), oget (assoc rs pid), oget (assoc tr pid)))) cr).

  clone import WeakSecurity as InpSec with 
    theory Gate <- InputGate.Gate,
    op simulator = simulator.

  section Security.

    declare module D : Distinguisher_t{RealEvaluator,IdealEvaluator}.

    module R : Rand_t = {
      proc gen(aux : aux_t, cr : pid_t list) : rands_t = {
        var p, pid, i, ps;
        i <- 0; ps <- [];

        while (i < n) {

          pid <- nth witness pid_set i;

          if (pid \in cr) {
            p <$ dpolynomial t;
          }
          else {
            p <@ PolynomialRand.gen(t);
          }
          ps <- ps ++ [(pid,p)];
          i <- i + 1;
        }
        return ps;
      }
    }.

    lemma rand_srand_equiv cr_ : 
      equiv [ R.gen ~ R.gen : ={aux,cr} /\ cr_ = cr{2} /\ (forall pid, pid \in cr{2} => pid \in pid_set) ==> 
                 unzip1 res{1} = pid_set /\ unzip1 res{1} = unzip1 res{2} /\
                 (forall pid, pid \in pid_set => 
                   if pid \in cr_ then oget (assoc res{1} pid) = oget (assoc res{2} pid)
                   else  (forall x c c', x <> fzero => eval x (update (oget (assoc res{1} pid)) 0 c) = eval x (update (oget (assoc res{2} pid)) 0 c'))) /\
                 (forall pid, pid \in pid_set => oget (assoc res{1} pid) \in dpolynomial t) /\
                 (forall pid, pid \in pid_set => oget (assoc res{2} pid) \in dpolynomial t) ].
    proof.
      proc; sp.
      while (={i,aux,cr} /\ 0 <= i{1} <= n /\ (forall pid, pid \in cr{2} => pid \in pid_set) /\
            (unzip1 ps{1} = take i{1} pid_set) /\ cr_ = cr{2} /\ unzip1 ps{1} = unzip1 ps{2} /\
            (forall pid, pid \in unzip1 ps{1} => if pid \in cr_ then 
                                                   oget (assoc ps{1} pid) = oget (assoc ps{2} pid)
                                                else (forall x c c', x <> fzero => eval x (update (oget (assoc ps{1} pid)) 0 c) = eval x (update (oget (assoc ps{2} pid)) 0 c'))) /\
            (forall pid, pid \in unzip1 ps{1} => oget (assoc ps{1} pid) \in dpolynomial t) /\
            (forall pid, pid \in unzip1 ps{2} => oget (assoc ps{2} pid) \in dpolynomial t)).
        wp; sp; if => //.
          wp; rnd; wp; skip; progress; first 2 by smt().
            rewrite map_cat /= (take_nth witness); first by rewrite pid_set_size.
            by smt(@List).
            by rewrite !map_cat H3.
            rewrite !assoc_cat; move : H12.
            rewrite mapP /=; progress.
            move : H12; rewrite mem_cat; progress.
            case (x \in ps{1}); progress; first by smt().
            case (x.`1 \in unzip1 ps{1}); progress; first by smt().
            have ->: x.`1 \in unzip1 ps{2} <=> false; first by smt().
            by simplify.
            rewrite !assoc_cat; move : H12.
            rewrite mapP /=; progress.
            move : H12; rewrite mem_cat; progress.
            case (x0 \in ps{1}); progress.
              rewrite -H3.
              have ->: x0.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x0.
              simplify; move : (H4 x0.`1).
              have ->: x0.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x0.
              simplify; rewrite H13 /=; progress.
              by move : (H16 x c c') => /#.
            case (x0.`1 \in unzip1 ps{1}); progress.
              rewrite -H3 H16 /=.
              simplify; move : (H4 x0.`1).
              simplify; rewrite H16 H13 /=; progress.
              by move : (H17 x c c') => /#.
            rewrite -H3 H16 /=.
            simplify; move : (H4 x0.`1).
            simplify; rewrite H16 H13 /=; progress.
            by smt().
            rewrite !assoc_cat; move : H12.
            rewrite mapP /=; progress.
            move : H12; rewrite mem_cat; progress.
            case (x \in ps{1}); progress.
              have ->: x.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x.
              by simplify; rewrite H5 mapP; progress; exists x.
            case (x.`1 \in unzip1 ps{1}); progress; first by rewrite H5.
            by smt().
            rewrite !assoc_cat; move : H12.
            rewrite mapP /=; progress.
            move : H12; rewrite mem_cat; progress.
            case (x \in ps{2}); progress.
              have ->: x.`1 \in unzip1 ps{2} by rewrite mapP; progress; exists x.
              by simplify; rewrite H6 mapP; progress; exists x.
            case (x.`1 \in unzip1 ps{2}); progress; first by rewrite H6.
            by smt().
          call (polynomial_rand_equiv t); skip; progress; first 2 by smt().
            rewrite map_cat /= (take_nth witness); first by rewrite pid_set_size.
            by smt(@List).
            by rewrite !map_cat H3.
            rewrite !assoc_cat; move : H13.
            rewrite mapP /=; progress.
            move : H13; rewrite mem_cat; progress.
            case (x \in ps{1}); progress; first by smt().
            case (x.`1 \in unzip1 ps{1}); progress; first by smt().
            have ->: x.`1 \in unzip1 ps{2} <=> false; first by smt().
            by smt().
            rewrite !assoc_cat; move : H13.
            rewrite mapP /=; progress.
            move : H13; rewrite mem_cat; progress.
            case (x0 \in ps{1}); progress.
              rewrite -H3.
              have ->: x0.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x0.
              simplify; move : (H4 x0.`1).
              have ->: x0.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x0.
              simplify; rewrite H14 /=; progress.
              by move : (H17 x c c') => /#.
            case (x0.`1 \in unzip1 ps{1}); progress.
              rewrite -H3 H17 /=.
              simplify; move : (H4 x0.`1).
              simplify; rewrite H17 H14 /=; progress.
              by move : (H18 x c c') => /#.
            rewrite -H3 H17 /=.
            simplify; move : (H4 x0.`1).
            simplify; rewrite H17 H14 /=; progress.
            by smt().
            rewrite !assoc_cat; move : H13.
            rewrite mapP /=; progress.
            move : H13; rewrite mem_cat; progress.
            case (x \in ps{1}); progress.
              have ->: x.`1 \in unzip1 ps{1} by rewrite mapP; progress; exists x.
              by simplify; rewrite H5 mapP; progress; exists x.
            case (x.`1 \in unzip1 ps{1}); progress; first by rewrite H5.
            by smt().
            rewrite !assoc_cat; move : H13.
            rewrite mapP /=; progress.
            move : H13; rewrite mem_cat; progress.
            case (x \in ps{2}); progress.
              have ->: x.`1 \in unzip1 ps{2} by rewrite mapP; progress; exists x.
              by simplify; rewrite H6 mapP; progress; exists x.
            case (x.`1 \in unzip1 ps{2}); progress; first by rewrite H6.
            by smt().
        skip; progress.
          by smt(n_pos).
          by rewrite take0.
          by rewrite H5 take_oversize; smt(pid_set_size).
          move : (H7 pid0); rewrite H5.
          have ->: take i_R pid_set = pid_set by rewrite take_oversize; smt(pid_set_size).
          by rewrite H10 H11 /=.
          move : (H7 pid0); rewrite H5.
          have ->: take i_R pid_set = pid_set by rewrite take_oversize; smt(pid_set_size).
          by rewrite H10 H11 /=; progress; rewrite (H13 x c c').
          by rewrite H8 H5 take_oversize; smt(pid_set_size).
          by rewrite H9 -H6 H5 take_oversize; smt(pid_set_size).
    qed.

    equiv real_ideal_equiv :
      GameReal(D,R).main ~ GameIdeal(D,R).main :
      ={glob D, glob R, aux, x} ==> ={res}.
    proof.
      proc. 
      seq 1 1 : (#pre /\ ={xs,cr}); first by call (_ : true).
      case (valid_corrupted_set cr{2}); last first.
rcondf{1} 2.
progress.
inline*.
wp.
while (#pre).
sp.
if.
by wp; rnd; skip; progress.
by wp; rnd; wp; skip; progress.
by wp; skip; progress => /#.
rcondf{2} 2.
progress.
inline*.
wp.
while (#pre).
sp.
if.
by wp; rnd; skip; progress.
by wp; rnd; wp; skip; progress.
by wp; skip; progress => /#.
inline*.
rnd.
wp.
sp 2 2.
while (#pre /\ ={i}).
sp.
if.
by progress.
by wp; rnd; skip; progress.
by wp; rnd; wp; skip; progress.
by wp; skip; progress => /#.
      seq 1 1 : (#pre /\ 
                 (forall pid, pid \in pid_set => 
                   if pid \in cr{2} then oget (assoc r{1} pid) = oget (assoc r{2} pid)
                   else  (forall x c c', x <> fzero => eval x (update (oget (assoc r{1} pid)) 0 c) = eval x (update (oget (assoc r{2} pid)) 0 c'))) /\
                 unzip1 r{1} = pid_set /\ unzip1 r{1} = unzip1 r{2} /\
                 (forall pid, pid \in pid_set => oget (assoc r{1} pid) \in dpolynomial t) /\
                 (forall pid, pid \in pid_set => oget (assoc r{2} pid) \in dpolynomial t)).
        exists* cr{2}; elim* => cr.
        by call (rand_srand_equiv cr); skip; progress => /#.
      if; last by rnd.
        progress.
          by rewrite -H2 H1.
          move : H5; rewrite /valid_rands /valid_rand => [[H5]] H9.
            rewrite /BGWInput.Shamir.t (dpolynomial_degree (oget (assoc r{2} pid)) BGWInput.t) //.
              by smt(t_pos).
              by rewrite H4 //.
            rewrite /BGWInput.Shamir.t (dpolynomial_size (oget (assoc r{2} pid)) BGWInput.t) //.
              by smt(t_pos).
              by rewrite H4 //.
            rewrite /BGWInput.Shamir.t (dpolynomial_exp (oget (assoc r{2} pid)) BGWInput.t) //.
              by smt(t_pos).
              by rewrite H4 //.
          by rewrite H1.
          move : H5; rewrite /valid_rands /valid_rand => [[H5]] H9.
            rewrite /BGWInput.Shamir.t (dpolynomial_degree (oget (assoc r{1} pid)) BGWInput.t) //.
              by smt(t_pos).
              by rewrite H3 //.
            rewrite /BGWInput.Shamir.t (dpolynomial_size (oget (assoc r{1} pid)) BGWInput.t) //.
              by smt(t_pos).
              by rewrite H3 //.
            rewrite /BGWInput.Shamir.t (dpolynomial_exp (oget (assoc r{1} pid)) BGWInput.t) //.
              by smt(t_pos).
              by rewrite H3 //.

      inline *; call (_ : true); wp; skip; progress.
       rewrite /simulator /= /gate /eval /party_exec1 /party_exec2 /= /input /= /output /get_messages_to /=.

rewrite -eq_in_map => pid; progress.
rewrite /trace !map_assoc //=; first 3 by smt().
rewrite /gate /party_exec /=.
rewrite !map_assoc //=; first 2 by smt().
rewrite !map_assoc //=; first by smt().
rewrite -!map_comp /(\o) /=.
congr.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.

case (x0 \in cr{2}); progress.
rewrite map_assoc //=.
smt().
rewrite /share /=.
congr.
rewrite !map_assoc; first by smt().
move : H7; rewrite /valid_corrupted_set; progress. 
by rewrite H11 //=.
simplify.

move : (H0 x0); rewrite H9 /=.
rewrite H10 /=.
progress.

        have : exists inp, Some inp = assoc xs{2} x0.
          exists (oget (assoc xs{2} x0)).
          by rewrite -Core.some_oget; first by rewrite assocTP => /#.
        progress; move : H12; progress.
        have ->: oget (assoc xs{2} x0) = inp by smt().
        clear H12.
        elim inp => pub sec /=.
simplify.
rewrite (H11 pid sec fzero).
smt(pid_set_neq0).
done.

       rewrite /simulator /= /gate /eval /party_exec1 /party_exec2 /= /input /= /output /get_messages_to /=.

rewrite -eq_in_map => pid; progress.
rewrite /trace !map_assoc //=.
move : (H0 pid); rewrite H8 /=.
have ->: pid \in pid_set by smt().
smt().
rewrite /trace !map_assoc //=; first 3 by smt().
rewrite !map_assoc //=; first by smt().
rewrite -!map_comp /(\o) /=.
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.
case (x0 \in cr{2}); progress.
rewrite map_assoc //=.
smt().
rewrite /share /=.
congr.
rewrite !map_assoc; first by smt().
move : H7; rewrite /valid_corrupted_set; progress. 
by rewrite H11 //=.
simplify.

move : (H0 x0); rewrite H9 /=.
rewrite H10 /=.
progress.

        have : exists inp, Some inp = assoc xs{2} x0.
          exists (oget (assoc xs{2} x0)).
          by rewrite -Core.some_oget; first by rewrite assocTP => /#.
        progress.
        have ->: oget (assoc xs{2} x0) = inp by smt().
        clear H12.
        elim inp => pub sec /=.
simplify.
rewrite (H11 pid sec fzero).
smt(pid_set_neq0).
done.
    qed.

    lemma security &m aux cr :
      Pr [ GameReal(D,R).main(aux,cr) @ &m : res ] - Pr [ GameIdeal(D,R).main(aux,cr) @ &m : res ] = 0%r.
    proof. 
      progress.
      have ?: Pr [ GameReal(D,R).main(aux,cr) @ &m : res ] = Pr [ GameIdeal(D,R).main(aux,cr) @ &m : res ] by byequiv real_ideal_equiv. 
      by smt().
    qed.

  end section Security.

end BGWInput.
