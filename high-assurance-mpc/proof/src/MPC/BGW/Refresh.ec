require import Int IntDiv List Distr DList Real.

from General require import PrimeField ListExt FieldPolynomial Utils.
from Functionalities require import RefreshFunctionality.
from MPC require import AGate GatePrivacy.
from SecretSharing require import Shamir.

theory BGWRefresh.

  const n : {int | 2 <= n} as n_pos.
  const t : {int | 0 <= t < n%/2} as t_pos.

  clone import Shamir as HMShamir with
    op n = n,
    op t = t.

  clone import RefreshFunctionality with 
    op SecretSharingScheme.n = HMShamir.n,
    op SecretSharingScheme.t = HMShamir.t,
    type SecretSharingScheme.pid_t = HMShamir.pid_t,
    op SecretSharingScheme.pid_set = HMShamir.pid_set,
    op SecretSharingScheme.valid_secret = HMShamir.valid_secret,
    type SecretSharingScheme.share_t = HMShamir.share_t,
    type SecretSharingScheme.rand_t = HMShamir.rand_t,
    op SecretSharingScheme.valid_rand = HMShamir.valid_rand,
    op SecretSharingScheme.share = HMShamir.share,
    op SecretSharingScheme.public_encoding = HMShamir.public_encoding,
    op SecretSharingScheme.pub_reconstruct = HMShamir.pub_reconstruct,
    op SecretSharingScheme.reconstruct = HMShamir.reconstruct,
    op SecretSharingScheme.get_party_share = HMShamir.get_party_share.

  type rand_t = polynomial.
  type rands_t = (pid_t * rand_t) list.
  op rand (pid : pid_t) (rs : rands_t) : rand_t = oget (assoc rs pid).
  op valid_rand (r : rand_t) : bool = HMShamir.valid_rand r witness.
  op valid_rands (rs : rands_t) : bool = 
    unzip1 rs = pid_set /\ (forall pid, pid \in pid_set => valid_rand (oget (assoc rs pid))).

  type output_t = secret_t.
  type outputs_t = (pid_t * share_t) list.
  op output (pid : pid_t) (ys : outputs_t) : output_t = oget (assoc ys pid).

  type msgs_t = t.
  type in_messages_t = (pid_t * msgs_t) list.
  type out_messages_t = (pid_t * msgs_t) list.

  op get_messages_to (pid : pid_t) (ms : out_messages_t) : msgs_t = oget (assoc ms pid).
  op get_messages_from (pid : pid_t) (ms : in_messages_t) : msgs_t = oget (assoc ms pid).

  type trace_t = shares_t * in_messages_t.
  type traces_t = (pid_t * trace_t) list.
  op trace (pid : pid_t) (tr : traces_t) : trace_t = oget (assoc tr pid).
  
  type view_t = input_t * rand_t * trace_t.

  op party_exec1 (r : rand_t) (x : input_t) : (pid_t * share_t) list = HMShamir.share r fzero.

  op party_exec2 (x : input_t) (ms : (pid_t * share_t) list) : output_t = 
    fadd x.`2 (sumt (map snd ms)).

  op out_messages (pid : pid_t) (v : view_t) : out_messages_t = 
    let (x, r, tr) = v in party_exec1 r x.

  op local_output (pid : pid_t) (v : view_t) : output_t = 
    let (x, r, tr) = v in 
    let (ys, ims) = tr in
    let yi = party_exec2 x tr.`2 in
    if yi = output pid ys then reconstruct ys else witness.

  op gate (rs : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let p1s = map (fun pid => (pid, party_exec1 (oget (assoc rs pid)) (oget (assoc xs pid)))) pid_set in
    let ms = map (fun pid => (pid, map (fun ms => let (sender, m) = ms in (sender, get_messages_to pid m)) p1s)) pid_set in 
    let pouts = map (fun pid => (pid, party_exec2 (oget (assoc xs pid)) (oget (assoc ms pid)))) pid_set in

    let y = reconstruct pouts in
    let ys = map (fun pid => (pid, y)) pid_set in
    let tr = map (fun pid => (pid, (pouts, oget (assoc ms pid)))) pid_set in
    (tr, ys).

  op consistent_views (vi vj : view_t) (i j : pid_t) = 
    let (xi, ri, ti) = vi in
    let (xj, rj, tj) = vj in
    get_messages_to j (out_messages i (xi , ri, ti)) = 
    get_messages_from i tj.`2.

  clone import Gate as RefreshGate with
    op GateFunctionality.n = HMShamir.SecretSharingScheme.n,
    op GateFunctionality.t = HMShamir.SecretSharingScheme.t,

    type GateFunctionality.pid_t = HMShamir.SecretSharingScheme.pid_t,
    op GateFunctionality.pid_set = HMShamir.SecretSharingScheme.pid_set,

    type GateFunctionality.pinput_t = RefreshFunctionality.GateFunctionality.pinput_t,
    type GateFunctionality.sinput_t = RefreshFunctionality.GateFunctionality.sinput_t,
    op GateFunctionality.valid_inputs = RefreshFunctionality.GateFunctionality.valid_inputs,
    type GateFunctionality.output_t = RefreshFunctionality.GateFunctionality.output_t,
    op GateFunctionality.f = RefreshFunctionality.GateFunctionality.f,

    type rand_t = rand_t,
    op valid_rand = valid_rand,

    type poutput_t = share_t,

    type msgs_t = msgs_t,
    op get_messages_to = get_messages_to,
    op get_messages_from = get_messages_from,

    op consistent_views = consistent_views,
    op local_output = local_output,

    op trace = trace,

    op gate = gate
  proof GateFunctionality.n_pos, GateFunctionality.t_pos,
        GateFunctionality.pid_set_uniq, GateFunctionality.pid_set_size,
        correct, local_output_correct, messages_consistency, correct_domain.
  realize GateFunctionality.n_pos by apply n_pos. 
  realize GateFunctionality.t_pos by apply t_pos.
  realize GateFunctionality.pid_set_uniq by apply pid_set_uniq.
  realize correct. 
    rewrite /valid_input /valid_inputs /valid_rands /valid_rand /valid_secret /sinput /input /output_pred /gate /f /party_exec1 /party_exec2 /pid_set /reconstruct /sinput /input /input_pred. 
    move => rs xs /=. progress.
    move : H3; rewrite /share /= -!eq_in_map => /> H3.
progress.

    have ->: (map (fun (pid : SecretSharingScheme.pid_t) => (pid, fadd (oget (assoc xs pid)).`2 (sumt (unzip2 (oget (assoc (map (fun (pid0 : pid_t) => (pid0, map (fun (ms : pid_t * BGWRefresh.out_messages_t) => let (sender, m) = ms in (sender, (BGWRefresh.get_messages_to pid0 m))) (map (fun (pid1 : pid_t) => (pid1, map (fun (pid2 : coeficient) => (pid2, eval pid2 (update (oget (assoc rs pid1)) 0 fzero))) pid_set)) pid_set))) pid_set) pid)))))) pid_set) 
=
(map (fun (pid : SecretSharingScheme.pid_t) => (pid, fadd (oget (assoc xs pid)).`2 (sumt (unzip2 (oget (assoc (map (fun (pid0 : pid_t) => (pid0, map ((fun (ms : pid_t * BGWRefresh.out_messages_t) => let (sender, m) = ms in (sender, (BGWRefresh.get_messages_to pid0 m))) \o (fun (pid1 : pid_t) => (pid1, map (fun (pid2 : coeficient) => (pid2, eval pid2 (update (oget (assoc rs pid1)) 0 fzero))) pid_set))) pid_set)) pid_set) pid)))))) pid_set).
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.
by rewrite -!map_comp /(\o) /=.

rewrite /(\o) /= /get_messages_to /=.
have ->: (map
     (fun (pid : SecretSharingScheme.pid_t) =>
        (pid,
         fadd (oget (assoc xs pid)).`2
           (sumt
              (unzip2
                 (oget
                    (assoc
                       (map
                          (fun (pid0 : pid_t) =>
                             (pid0,
                              map
                                (fun (x0 : pid_t) =>
                                   (x0,
                                    oget
                                      (assoc
                                         (map
                                            (fun (pid2 : coeficient) =>
                                               (pid2, eval pid2 (update (oget (assoc rs x0)) 0 fzero))) pid_set) pid0)))
                                pid_set)) pid_set) pid)))))) pid_set) =
(map
     (fun (pid : SecretSharingScheme.pid_t) =>
        (pid,
         fadd (oget (assoc xs pid)).`2
           (sumt
              (unzip2
                 (oget
                    (assoc
                       (map
                          (fun (pid0 : pid_t) =>
                             (pid0,
                              map
                                (fun (x0 : pid_t) =>
                                   (x0, eval pid0 (update (oget (assoc rs x0)) 0 fzero)))
                                pid_set)) pid_set) pid)))))) pid_set).
rewrite -eq_in_map; progress.
rewrite !map_assoc //=.
rewrite -!map_comp /(\o) /=.
congr.
congr.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.

have ->: (map
     (fun (pid : SecretSharingScheme.pid_t) =>
        (pid,
         fadd (oget (assoc xs pid)).`2
           (sumt
              (unzip2
                 (oget
                    (assoc
                       (map
                          (fun (pid0 : pid_t) =>
                             (pid0,
                              map (fun (x0 : pid_t) => (x0, eval pid0 (update (oget (assoc rs x0)) 0 fzero))) pid_set))
                          pid_set) pid)))))) pid_set) =
(map
     (fun (pid : SecretSharingScheme.pid_t) =>
        (pid,
         fadd (oget (assoc xs pid)).`2
           (sumt
              (unzip2 (map (fun (x0 : pid_t) => (x0, eval pid (update (oget (assoc rs x0)) 0 fzero))) pid_set)
                 )))) pid_set).
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.
have ->: (map
     (fun (pid : SecretSharingScheme.pid_t) =>
        (pid,
         fadd (oget (assoc xs pid)).`2
           (sumt (unzip2 (map (fun (x0 : pid_t) => (x0, eval pid (update (oget (assoc rs x0)) 0 fzero))) pid_set)))))
     pid_set) = 
(map
     (fun (pid : SecretSharingScheme.pid_t) =>
        (pid,
         fadd (oget (assoc xs pid)).`2
           (sumt (map (snd \o (fun (x0 : pid_t) => (x0, eval pid (update (oget (assoc rs x0)) 0 fzero)))) pid_set))))
     pid_set).
rewrite -eq_in_map; progress.
by rewrite -map_comp /(\o) /=.
print FieldPolynomial.
have ->: (map
     (fun (pid : SecretSharingScheme.pid_t) =>
        (pid,
         fadd (oget (assoc xs pid)).`2
           (sumt
              (map
                 ((fun (p : pid_t * t) => p.`2) \o
                  fun (x0 : pid_t) => (x0, eval pid (update (oget (assoc rs x0)) 0 fzero))) pid_set)))) pid_set) =
(map
     (fun (pid : SecretSharingScheme.pid_t) =>
        (pid,
         fadd (eval pid (update r 0 s))
           (eval pid (update (foldr (fun p st => add st (snd p)) pzero rs) 0 fzero)))) pid_set).
rewrite -eq_in_map; progress.
congr.
by rewrite H3 /=.
rewrite /(\o) /=.
rewrite /sumt.
rewrite foldr_map /=.

rewrite foldr_eval_add_update. smt(pid_set_uniq).
done.
done.

have ->: (map
     (fun (pid : SecretSharingScheme.pid_t) =>
        (pid,
         fadd (eval pid (update r 0 s))
           (eval pid
              (update
                 (foldr (fun (p : GateFunctionality.pid_t * polynomial) (st : polynomial) => add st p.`2) pzero rs) 0
                 fzero)))) pid_set) = 
(map
     (fun (pid : SecretSharingScheme.pid_t) =>
        (pid,
         eval pid (add (update r 0 s)
           (update
                 (foldr (fun (p : GateFunctionality.pid_t * polynomial) (st : polynomial) => add st p.`2) pzero rs) 0
                 fzero)))) pid_set).
rewrite -eq_in_map; progress.
by rewrite -eval_add.
rewrite interpolate_eval.
smt(pid_set_uniq).
rewrite degree_add.
rewrite degree_update0.
rewrite degree_update0.
have : (degree (foldr (fun (p : GateFunctionality.pid_t * polynomial) (st : polynomial) => add st p.`2) pzero rs)) = HMShamir.t.
move : (H5 x); rewrite H6 /=.
progress.

rewrite (degree_foldr_add _ HMShamir.t).
progress.
smt().
done.

progress.
rewrite H7 H0 /max /=.
smt(pid_set_size n_pos t_pos).

have ->: interpolate fzero (map (fun (pid : SecretSharingScheme.pid_t) => (pid, (oget (assoc xs pid)).`2)) pid_set) = interpolate fzero (map (fun (pid : SecretSharingScheme.pid_t) => (pid, eval pid (update r 0 s))) pid_set).
congr.
rewrite -eq_in_map; progress.
by rewrite H3 /=.
rewrite interpolate_eval.
smt(pid_set_uniq).
rewrite degree_update0.
smt(pid_set_size n_pos t_pos).
rewrite eval_update0.
rewrite expo_diff_count.
smt(n_pos t_pos).
smt().
done.
rewrite -update_add.
rewrite expo_diff_count.
smt(n_pos t_pos).
smt().
done.

rewrite count_expos_foldr_add.
progress.
rewrite expo_diff_count.
smt(t_pos).
progress.
smt().
done.
done.

rewrite !eval_update0.

rewrite count_expos_add_foldr.
progress.
rewrite expo_diff_count.
smt(t_pos).
progress.
smt().
done.
rewrite expo_diff_count.
smt(t_pos).
progress.
smt().
done.
done.

rewrite expo_diff_count.
smt(n_pos t_pos).
smt().
done.

rewrite count_expos_foldr_add.
progress.
rewrite expo_diff_count.
smt(t_pos).
progress.
smt().
done.
done.
by ringeq.
  qed.
  realize GateFunctionality.pid_set_size by apply pid_set_size.
  realize local_output_correct.
    rewrite /local_output /output /gate /party_exec1 /party_exec2 /input 
            /pid_set /get_messages_to => />; progress; rewrite map_assoc //=.
rewrite /trace /=.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
  qed.
  realize messages_consistency.
    rewrite /consistent_views /local_output /output /gate /party_exec1 /party_exec2 /input 
            /pid_set /get_messages_to /out_messages /trace /party_exec1 => />; progress. 
    rewrite /get_messages_from !map_assoc /share //= /= !map_assoc //=. 
    rewrite -!map_comp /(\o) /= !map_assoc //= !map_assoc //=.
  qed.
  realize correct_domain.
    by move => rs xs; rewrite /gate /= /party_exec -!map_comp /(\o) /= !map_id /pid_set.
  qed.

  op simulator (rs : rands_t) (xs : inputs_t) (cr : pid_t list) (ys : outputs_t) : views_t =
    let pub = fst (oget (assoc xs (head witness cr))) in
    let xs' = map (fun pid => (pid, if pid \in cr then oget (assoc xs pid) else (pub, (fzero)))) pid_set in

    let p1s = map (fun pid => (pid, party_exec1 (oget (assoc rs pid)) (oget (assoc xs' pid)))) pid_set in
    let ms = map (fun pid => (pid, map (fun ms => let (sender, m) = ms in (sender, get_messages_to pid m)) p1s)) pid_set in 
    let pouts = map (fun pid => (pid, party_exec2 (oget (assoc xs' pid)) (oget (assoc ms pid)))) pid_set in

    let poutsc = map (fun pid => (pid, oget (assoc pouts pid))) pid_set in
    let out_poly = interpolate_poly ((fzero, output (head witness cr) ys) :: poutsc) in

    let pouts = map (fun pid => (pid, eval pid out_poly)) pid_set in

    (map (fun pid => (pid, (oget (assoc xs pid), oget (assoc rs pid), (pouts, oget (assoc ms pid))))) cr). 

  clone import Privacy with 
    theory Gate <- RefreshGate,
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
            rewrite /HMShamir.t (dpolynomial_degree (oget (assoc r{2} pid)) t) //.
              by smt(t_pos).
              by rewrite H4 //.
            rewrite /HMShamir.t (dpolynomial_size (oget (assoc r{2} pid)) t) //.
              by smt(t_pos).
              by rewrite H4 //.
            rewrite /HMShamir.t (dpolynomial_exp (oget (assoc r{2} pid)) t) //.
              by smt(t_pos).
              by rewrite H4 //.
          by rewrite H1.
          move : H5; rewrite /valid_rands /valid_rand => [[H5]] H9.
            rewrite /HMShamir.t (dpolynomial_degree (oget (assoc r{1} pid)) t) //.
              by smt(t_pos).
              by rewrite H3 //.
            rewrite /HMShamir.t (dpolynomial_size (oget (assoc r{1} pid)) t) //.
              by smt(t_pos).
              by rewrite H3 //.
            rewrite /HMShamir.t (dpolynomial_exp (oget (assoc r{1} pid)) t) //.
              by smt(t_pos).
              by rewrite H3 //.

      inline *; call (_ : true); wp; skip; progress.
       rewrite /simulator /= /gate /party_exec1 /party_exec2 /= /input /= /output /get_messages_to /=.

rewrite -eq_in_map => pid; progress.
by rewrite !map_assoc //=.
rewrite /rand.
move : (H0 pid); rewrite H8 /=; progress.
rewrite H9.
smt().
done.
rewrite /trace /=.
rewrite !map_assoc //=; first 4 by smt().
rewrite !map_assoc //=; first by smt().
split; last first.

rewrite -!map_comp /(\o) /= -eq_in_map; progress.
rewrite /share /= !map_assoc //=; first 2 by smt().
move : (H0 x0); rewrite H9; progress.
case (x0 \in cr{2}); progress.
move : H10; rewrite H11 /=.
smt().
move : H10; rewrite H11 /=.
progress.
rewrite (H10 pid fzero fzero).
smt(pid_set_neq0).
done.

rewrite -eq_in_map => pid'; progress.
rewrite !map_assoc //=.
rewrite -!map_comp /(\o) //=.

rewrite -interpolate_poly_eval //=.
split.
rewrite mapP; progress.
rewrite Utils.existsN; progress.
case (x0.`1 \in cr{2}); progress.
have ->: fzero = x0.`1 <=> false by smt(pid_set_neq0).
done.
simplify.
case (fzero = x0.`1); progress.
rewrite mapP; progress.
rewrite Utils.existsN; progress.
case (x1 \in pid_set); progress.
have : x1 <> fzero by smt(pid_set_neq0).
smt().
rewrite -map_comp /(\o) /= map_id.
move : H; rewrite /valid_corrupted_set.
progress.
smt(pid_set_uniq).

rewrite interpolate_mem.
split.
rewrite mapP; progress.
rewrite Utils.existsN; progress.
case (x0.`1 \in cr{2}); progress.
have ->: fzero = x0.`1 <=> false by smt(pid_set_neq0).
done.
simplify.
case (fzero = x0.`1); progress.
rewrite mapP; progress.
rewrite Utils.existsN; progress.
case (x1 \in pid_set); progress.
have : x1 <> fzero by smt(pid_set_neq0).
smt().
rewrite -map_comp /(\o) /= map_id.
move : H; rewrite /valid_corrupted_set.
progress.
smt(pid_set_uniq).

simplify.
right.
by rewrite -map_comp /(\o) /= map_id.

rewrite assoc_cons.
have ->: pid' = fzero <=> false by smt(pid_set_neq0).
simplify.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
rewrite !map_assoc //=.
case (pid' \in cr{2}); progress.
rewrite !map_assoc //=.
rewrite -map_comp /(\o) /=. 
rewrite -map_comp /(\o) /=.
congr.
congr.
rewrite -eq_in_map; progress.
rewrite /share /=.
rewrite !map_assoc //=.
case (x0 \in cr{2}); progress.
smt().
move : (H0 x0); rewrite H11 H12 /=.
progress.
move : (H13 pid' fzero fzero).
smt(pid_set_neq0).

rewrite -!map_comp /(\o) /=.
rewrite /share /=.
have ->: 
     (map
        (fun (x : pid_t) =>
           oget
             (assoc
                (map
                   (fun (pid0 : coeficient) =>
                      (pid0, eval pid0 (update (oget (assoc r{1} x)) 0 fzero)))
                   pid_set) pid')) pid_set) = 
(map
        (fun (x : pid_t) => eval pid' (update (oget (assoc r{1} x)) 0 fzero))) pid_set.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.
have ->: 
     (map
        (fun (x : pid_t) =>
           oget
             (assoc
                (map
                   (fun (pid0 : coeficient) =>
                      (pid0, eval pid0 (update (oget (assoc r{2} x)) 0 fzero)))
                   pid_set) pid')) pid_set) = 
(map
        (fun (x : pid_t) => eval pid' (update (oget (assoc r{2} x)) 0 fzero))) pid_set.
rewrite -eq_in_map; progress.
by rewrite !map_assoc //=.

move : (sumt_map_eval pid_set r{1} (map (fun pid => (pid, (fzero, fzero))) pid_set)).
progress.
move : (H11 pid').
have ->: uniq pid_set by smt(pid_set_uniq).
rewrite H1 /=.
rewrite -map_comp /(\o) /= map_id /=.
rewrite -!map_comp /(\o) /=.
have ->: map
     (fun (pid0 : pid_t) =>
        eval pid'
          (update (oget (assoc r{1} pid0)) 0
             (oget
                (assoc
                   (map (fun (pid1 : pid_t) => (pid1, (fzero, fzero)))
                      pid_set) pid0)).`2)) pid_set = 
map
     (fun (pid0 : pid_t) =>
        eval pid'
          (update (oget (assoc r{1} pid0)) 0 fzero)) pid_set.
rewrite -eq_in_map; progress.
by rewrite !map_assoc /=.
have ->: map
           (fun (x : pid_t) =>
              (oget
                 (assoc
                    (map (fun (pid0 : pid_t) => (pid0, (fzero, fzero)))
                       pid_set) x)).`2) pid_set = 
map
           (fun (x : pid_t) => fzero) pid_set.
rewrite -eq_in_map; progress.
by rewrite !map_assoc /=.

progress.
rewrite H12.
have ->: sumt (map (fun (_ : pid_t) => fzero) pid_set) = fzero.
by rewrite sumt_map_fzero.

move : (sumt_map_eval pid_set r{2} (map (fun pid => (pid, (fzero, fzero))) pid_set)).
progress.
move : (H13 pid').
have ->: uniq pid_set by smt(pid_set_uniq).
rewrite -H2 H1 /=.
rewrite -map_comp /(\o) /= map_id /=.
rewrite -!map_comp /(\o) /=.
have ->: map
     (fun (pid0 : pid_t) =>
        eval pid'
          (update (oget (assoc r{2} pid0)) 0
             (oget
                (assoc
                   (map (fun (pid1 : pid_t) => (pid1, (fzero, fzero)))
                      pid_set) pid0)).`2)) pid_set = 
map
     (fun (pid0 : pid_t) =>
        eval pid'
          (update (oget (assoc r{2} pid0)) 0 fzero)) pid_set.
rewrite -eq_in_map; progress.
by rewrite !map_assoc /=.
have ->: map
           (fun (x : pid_t) =>
              (oget
                 (assoc
                    (map (fun (pid0 : pid_t) => (pid0, (fzero, fzero)))
                       pid_set) x)).`2) pid_set = 
map
           (fun (x : pid_t) => fzero) pid_set.
rewrite -eq_in_map; progress.
by rewrite !map_assoc /=.

progress.
rewrite H14.
have ->: sumt (map (fun (_ : pid_t) => fzero) pid_set) = fzero.
by rewrite sumt_map_fzero.

rewrite (ind_sumt_poly pid' (oget (assoc xs{2} pid')).`2 fzero r{1} r{2}).
done.
smt().
move : (H0 pid').
rewrite H9 H10 /=. 
progress.
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

end BGWRefresh.
