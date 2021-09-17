require import AllCore Int List.
require import Aux AuxList NextMsgArray NextMsgTrace NextMsgProtocol.
require import NextMsgISet NextMsgIMap.

require import FSet AuxFSet.
require import SmtMap AuxSmtMap.

import ISet IMap Array.

theory StatefulProtocol.

  clone import Trace as ST.

  (* Abstract messages *)

  type local_messages.
  type messages = local_messages pmap.

  type local_out_messages = local_messages.
  type local_in_messages = local_messages.
  type out_messages = messages.
  type in_messages = messages.

  op from_local_messages : local_messages -> pmsgs. (* needed for computing views *)
  op to_local_messages : pmsgs -> local_messages. (* needed for computing views *)
  op send_messages : out_messages -> in_messages. (* copies messages from output buffers to input buffers *)

  op from_messages : local_messages pmap -> ppmsgs = P.map from_local_messages.
  op to_messages : ppmsgs -> messages = P.map to_local_messages.

  op valid_local_messages : public_input -> round -> local_messages -> bool.
  op valid_messages (p:public_input) r (ms:messages) =
    P.all (fun i => valid_local_messages p r) ms.

  op valid_msg : public_input -> round -> msg -> bool.
  op valid_pmsgs p r (ms:pmsgs) : bool = P.all (fun i => valid_msg p r) ms.
  op valid_ppmsgs p r (ms:ppmsgs) : bool = P.all (fun i => valid_pmsgs p r) ms.

  axiom to_from_local_messages p r xs :
    valid_local_messages p r xs => to_local_messages (from_local_messages xs) = xs.
  axiom from_to_local_messages p r xs :
    valid_pmsgs p r xs => from_local_messages (to_local_messages xs) = xs.
  axiom ppswap_from_messages p r outs :
    valid_messages p r outs => ppswap (from_messages outs) = from_messages (send_messages outs). 
  axiom valid_pmsgs_from p r xs :
    valid_local_messages p r xs => valid_pmsgs p r (from_local_messages xs).

  axiom valid_local_messages_to p r xs :
    valid_pmsgs p r xs => valid_local_messages p r (to_local_messages xs).

  lemma valid_messages_get p r xs i :
    ISet.mem i partyset =>
    valid_messages p r xs => valid_local_messages p r (P.get xs i).
    move => Hi. rewrite /valid_messages P.allP => |>H. rewrite H => |>. move :Hi. rewrite /ISet.mem iset_in_def => |>. qed.

  lemma valid_pmsgs_get x n xs i :
    0 <= i /\ i < P.size =>
    valid_pmsgs x n xs => valid_msg x n (P.get xs i).
    move => |> H H0. rewrite /valid_pmsgs P.allP => |>H1. rewrite H1 => |>. qed.

  lemma valid_ppmsgs_from p r xs :
    valid_messages p r xs => valid_ppmsgs p r (from_messages xs).
    rewrite /valid_messages /valid_ppmsgs !P.allP /from_messages => |> H i H1 H2.
    rewrite P.get_map => |>. rewrite valid_pmsgs_from H => |>.
    qed.

  lemma to_from_messages p r xs :
    valid_messages p r xs => to_messages (from_messages xs) = xs.
    rewrite pmap_eqP => |>H x H0. rewrite !get_pmap => |>*. rewrite (to_from_local_messages p r) => |>*.
    move :H. rewrite /valid_messages /all allP => |>H1. rewrite H1 => |>*. move :H0. rewrite /ISet.mem iset_in_def in_iseq => |>*. qed.

  lemma from_to_messages p r xs :
    valid_ppmsgs p r xs => from_messages (to_messages xs) = xs.
    rewrite pmap_eqP => |>H x H0. rewrite !get_pmap => |>*. rewrite (from_to_local_messages p r) => |>*.
    move :H. rewrite /valid_ppmsgs /all allP => |>H1. rewrite H1 => |>*. move :H0. rewrite /ISet.mem iset_in_def in_iseq => |>*. qed.

  axiom get_local_messages_eqP (xs ys : local_messages) :
    (xs = ys) = (forall (x : int), ISet.mem x partyset => (P.get (from_local_messages xs) x) = (P.get (from_local_messages ys) x)).

  lemma local_messages_eqP p r (xs ys:local_messages) :
    valid_local_messages p r xs => 
    (xs = ys) = (from_local_messages xs = from_local_messages ys).
    move => H. rewrite -(to_from_local_messages p r)=> |>*. rewrite -(to_from_local_messages p r)=> |>*. rewrite pmap_eqP => |>*. rewrite !(to_from_local_messages p r)=> |>*. rewrite eq_logical => |>H1. have : from_local_messages xs = from_local_messages ys. rewrite pmap_eqP => |>*. 
    rewrite (_:(xs=ys)=(to_local_messages (from_local_messages xs) = to_local_messages (from_local_messages ys) )). rewrite !(to_from_local_messages p r) => |>*. have : xs = ys. rewrite get_local_messages_eqP => |>*. progress. progress. rewrite H0 => |>*. qed.     

  lemma get_messages_eqP (xs ys : messages) :
    (xs = ys) = (forall (x y : int), (ISet.mem x partyset /\ ISet.mem y partyset) => P.get (P.get (from_messages xs) x) y = P.get (P.get (from_messages ys) x) y).
    rewrite eq_logical => |>H. rewrite pmap_eqP => |>y. rewrite get_local_messages_eqP => |>H2 x H3. 
    have : (P.get ((P.get (from_messages xs) y)) x) = (P.get ((P.get (from_messages ys) y)) x). rewrite H => |>. rewrite /from_messages !get_pmap => |>H4. qed.

  lemma messages_eqP p r (xs ys:messages) :
    valid_messages p r xs =>
    (xs = ys) = (from_messages xs = from_messages ys).
    move => H. rewrite -(to_from_messages p r)=> |>*. rewrite -(to_from_messages p r) => |>*. rewrite ppmap_eqP => |>*. rewrite !(to_from_messages p r) => |>*. rewrite eq_logical => |>H1. have : from_messages xs = from_messages ys. rewrite ppmap_eqP => |>*. 
    rewrite (_:(xs=ys)=(to_messages (from_messages xs) = to_messages (from_messages ys) )). rewrite !(to_from_messages p r) => |>*. have : xs = ys. rewrite get_messages_eqP => |>*. progress. progress. rewrite H0 => |>*. qed.

  axiom valid_send_messages outs p r :
    valid_messages p r outs => valid_messages p r (send_messages outs).

  lemma send_messages_bij p r out1 out2 :
    valid_messages p r out1 => valid_messages p r out2 =>
    (out1 = out2) = (send_messages out1 = send_messages out2).
    rewrite eq_logical => |>H1 H2 H3. rewrite (messages_eqP p r) in H3. rewrite valid_send_messages => |>*. move :H3. rewrite -!(ppswap_from_messages p r) => |>H3. move :H3. rewrite !ppswap_eqP. progress. rewrite -(messages_eqP p r) in H => |>*. qed.

  lemma get_send_messages p r outs i :
    valid_messages p r outs =>
    ISet.mem i partyset => P.get (send_messages outs) i = to_local_messages (P.map (fun out => P.get (from_local_messages out) i) outs).
    move => H. have : ppswap (from_messages outs) = from_messages (send_messages outs). rewrite (ppswap_from_messages p r) => |>*. progress. rewrite ppmap_eqP /from_messages in H0. 
    rewrite (local_messages_eqP p r) => |>*. have : valid_messages p r (send_messages outs). rewrite valid_send_messages => |>*. rewrite /valid_messages /all allP => |>H2. rewrite H2 => |>*. move :H1. rewrite /ISet.mem iset_in_def in_iseq => |>*.
    rewrite (from_to_local_messages p r). have : valid_ppmsgs p r (from_messages outs). rewrite valid_ppmsgs_from => |>*. rewrite /valid_ppmsgs /all allP /valid_pmsgs /all !allP => |>H2 x H3. rewrite P.get_map => |>*. move :H3. rewrite in_iseq => |>*. have : all (fun (i0 : int) => valid_msg p r ((P.get ((P.get (from_messages outs) x)) i0))) (iota_ 0 P.size). rewrite H2 => |>*. rewrite allP => |>H4. have : valid_msg p r ((P.get ((P.get (from_messages outs) x)) i)). rewrite H4 => |>*. move :H1. rewrite /ISet.mem iset_in_def in_iseq => |>*. rewrite /from_messages => |>H5. move :H5. rewrite P.get_map => |>*. move :H3. rewrite in_iseq => |>*. 
    rewrite pmap_eqP => |>x H2. rewrite get_pmap => |>*. 
    have : (P.get ((P.get (ppswap ((P.map from_local_messages outs))) i)) x) = (P.get ((P.get ((P.map from_local_messages (send_messages outs))) i)) x). rewrite H0 => |>*. rewrite /ppswap get_ppinit. simplify. rewrite get_pinit H1. simplify. rewrite get_pinit H2. simplify. rewrite get_pmap. rewrite H2. simplify. 
    have : (P.get ((P.get (ppswap ((P.map from_local_messages outs))) i)) x) =
      (P.get ((P.get ((P.map from_local_messages (send_messages outs))) i)) x). rewrite H0 => |>*. clear H0. rewrite !get_pmap => |>H0 H3. rewrite -H0 => |>*. rewrite /ppswap get_ppinit H1 => |>*. rewrite get_pinit H2 => |>*. rewrite get_pmap => |>*. qed.

  lemma get_from_local_messages_send_messages p r outs i j :
    valid_messages p r outs =>
    (ISet.mem i partyset) => (ISet.mem j partyset) =>
    P.get (from_local_messages (P.get (send_messages outs) i)) j = P.get (from_local_messages (P.get outs j)) i.
    move => H Hi Hj. have : ppswap (from_messages outs) = from_messages (send_messages outs). rewrite (ppswap_from_messages p r outs) => |>. rewrite ppmap_eqP => |>H1. 
    have : (P.get ((P.get (ppswap (from_messages outs)) i)) j) = (P.get ((P.get (from_messages (send_messages outs)) i)) j). rewrite H1 => |>. rewrite /ppswap /from_messages => |>. rewrite get_pmap => |>. rewrite get_ppinit !Hi => |>. rewrite get_pinit Hj => |>. rewrite get_pmap => |>. 
    rewrite (get_send_messages p r outs) => |>. rewrite !(from_to_local_messages p r) => |>.
    rewrite /valid_pmsgs P.allP => |>k Hk1 Hk2. rewrite get_pmap => |>. rewrite /ISet.mem iset_in_def => |>. rewrite valid_pmsgs_get => |>. move :Hi. rewrite /ISet.mem iset_in_def => |>. rewrite valid_pmsgs_from => |>. rewrite valid_messages_get => |>. rewrite /ISet.mem iset_in_def => |>. rewrite !get_pmap => |>. qed.

  (* Local State *)

  type local_state.

  op init_local_state : party -> public_input -> local_input -> local_rand -> local_state.

  (* update state after a specific round *)
  op update_local_state : party -> round -> public_input -> local_in_messages -> local_state -> local_state.

  (* get state before a specific round *)
  op get_local_state' (i:party) (r:round) (x:public_input) (st0:local_state) (insi:in_msgs) : local_state = 
    let go = fun st r =>
      let insr = prget insi r in
      update_local_state i r x (to_local_messages insr) st in
    foldl go st0 (iseq r).
  op get_local_state (i:party) (r:round) (x:public_input) (wi:local_input) (ri:local_rand) (insi:in_msgs) : local_state = 
    get_local_state' i r x (init_local_state i x wi ri) insi.

   (* Global State *)
  type state = local_state pmap.

  op init_state (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) : state =
    P.imap (fun i (wi_ri:local_input*local_rand) => init_local_state i x wi_ri.`1 wi_ri.`2) (P.zip ws rs).

  op update_state (round:round) (x:public_input) (ins:local_in_messages pmap) (st:state) : state =
    P.imap (fun i (insi_sti:(_*_)) => update_local_state i round x  insi_sti.`1 insi_sti.`2) (P.zip ins st).

  op get_state (round:round) (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) (ins:in_msgs pmap) : state =
    P.imap (fun i (wi_ri_insi:local_input*(local_rand*in_msgs)) => get_local_state i round x wi_ri_insi.`1  wi_ri_insi.`2.`1  wi_ri_insi.`2.`2) (P.zip3 ws rs ins).  

  (* Local Protocol *)

  op stateful_local_protocol_round : party -> round -> public_input -> local_state -> local_out_messages.

  op stateful_local_protocol_end : party -> public_input -> local_state -> local_output.

  op stateful_local_protocol''' (i:party) (x:public_input) (st:local_state) (ins:in_msgs) sz (rounds:round list) : local_state * out_msgs =
    foldl (fun (acc:local_state*out_msgs) (round:round) =>
      let outs' = prset acc.`2 round (from_local_messages (stateful_local_protocol_round i round x acc.`1)) in
      let st' = update_local_state i round x (to_local_messages (prget ins round)) acc.`1 in
      (st',outs')
    ) (st,prempty sz witness) rounds.

  op stateful_local_protocol'' (i:party) (x:public_input) (st:local_state) (ins:in_msgs) sz (rounds:round) : local_state * out_msgs =
    stateful_local_protocol''' i x st ins sz (iseq rounds).

  op stateful_local_protocol' (i:party) (x:public_input) (st:local_state) (ins:in_msgs) : local_state * out_msgs =
    stateful_local_protocol'' i x st ins (rounds x) (rounds x).

  op stateful_local_protocol (i:party) (x:public_input) (vi:view) : out_msgs * local_output =
    let outs = stateful_local_protocol' i x (init_local_state i x vi.`1 vi.`2.`2) vi.`2.`1 in
    let out = stateful_local_protocol_end i x outs.`1 in
    (outs.`2,out).

  (* Global Protocol *)

  op stateful_protocol_round (round:round) (x:public_input) (st:state) : local_out_messages pmap =
    P.imap (fun i sti => stateful_local_protocol_round i round x sti) st.

  op stateful_protocol_end (x:public_input) (st:state) : local_output pmap =
    P.imap (fun i sti => stateful_local_protocol_end i x sti) st.

  op stateful_protocol''' (x:public_input) (ins:in_msgs pmap) (st:state) (rounds:round list) : in_msgs pmap * state =
    foldl (fun (ins_st:in_msgs pmap*state) (round:round) => 
      let ins = ins_st.`1 in
      let st = ins_st.`2 in
      let outs = send_messages (stateful_protocol_round round x st) in
      (pprset ins round (from_messages outs),update_state round x outs st)
      ) (ins,st) rounds.

  op stateful_protocol'' (x:public_input) (ins:in_msgs pmap) (st:state) (rounds:round) : in_msgs pmap * state = stateful_protocol''' x ins st (iseq rounds).

  op stateful_protocol' (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) : in_msgs pmap * state =
    stateful_protocol'' x (pprempty (rounds x) witness) (init_state x ws rs) (rounds x).

  op stateful_protocol (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) : trace * local_output pmap =
    let ins_st' = stateful_protocol' x ws rs in
    let outs = stateful_protocol_end x ins_st'.`2 in
    let tr = P.zip3 ws ins_st'.`1 rs in
    (tr,outs).

  op stateful_protocol_sz'' sz (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) rounds : in_msgs pmap * state =
    stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) rounds.

  op stateful_protocol_sz' sz (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) : in_msgs pmap * state =
    stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) (rounds x).

  op stateful_protocol_sz sz (x:public_input) (ws:local_input pmap) (rs:local_rand pmap) : trace * local_output pmap =
    let ins_st' = stateful_protocol_sz' sz x ws rs in
    let outs = stateful_protocol_end x ins_st'.`2 in
    let tr = P.zip3 ws ins_st'.`1 rs in
    (tr,outs).

  (* Properties *)

  axiom valid_stateful_local_protocol_round i r x st :
    valid_local_messages x r (stateful_local_protocol_round i r x st).

  lemma valid_stateful_protocol_round x n st :
    valid_messages x n (stateful_protocol_round n x st).
    rewrite /valid_messages P.allP => |>i Hi1 Hi2. rewrite /stateful_protocol_round => |>. rewrite P.get_imap => |>. rewrite valid_stateful_local_protocol_round => |>. qed.

  lemma get_local_state_succ i n x wi ri insi :
    0 <= n => get_local_state i (n+1) x wi ri insi = update_local_state i n x (to_local_messages ((prget insi n))) (get_local_state i n x wi ri insi).
    progress. rewrite /get_local_state /get_local_state' iseq_succ => |>*. rewrite foldl_rcons => |>*. qed.

  lemma get_local_state_prefix i n x ws rs ins1 ins2 :
    (forall r, 0 <= r < n => prget ins1 r = prget ins2 r) => 0 <= n =>
      get_local_state i n x ws rs ins1 = get_local_state i n x ws rs ins2.
    rewrite /get_local_state /get_local_state' => |>. elim/natind:n => |> n.
    move => Hn. rewrite !iseq_nil => |>.
    move => Hn R H Hn2. rewrite !iseq_succ => |>. rewrite !foldl_rcons => |>. rewrite R => |>. smt(). clear R. rewrite H => |>. smt(). qed.

  lemma get_local_state_prmsgs_up_to sz i n n2 x ws rs ins :
    (forall i, ISet.mem i partyset => Array.size (P.get ins i) = sz) => 
    ISet.mem i partyset /\ 0 <= n /\ n <= n2 /\ n2 <= sz =>
      get_local_state i n x ws rs ins = get_local_state i n x ws rs (prmsgs_up_to n2 ins).
    rewrite /get_local_state /get_local_state' => |>H1 H2 H3 H4 H5. move : H2 H3 H4. elim/natind:n => |>n H2 H3 H0 H4. rewrite !iseq_nil => |>H4. rewrite !iseq_succ => |>. rewrite !foldl_rcons => |>H6. rewrite H3 => |>. smt(). clear H3. rewrite (prget_prmsgs_up_to_lt sz) => |>. smt(). qed.

clone include Protocol with
    theory T <- ST,
    op local_protocol_round i r x wi ri insi = from_local_messages (stateful_local_protocol_round i r x (get_local_state i r x wi ri insi)),
    op local_protocol_end i x wi ri insi = stateful_local_protocol_end i x (get_local_state i (rounds x) x wi ri insi)
    proof *.
    realize local_protocol_round_prefix.
    rewrite  /local_protocol_round => |> i n x ws rs ins1 ins2 H Hi Hn. congr. rewrite (get_local_state_prefix _ _ _ _ _ ins1 ins2 ) => |>. qed.

  (* Properties *) 

  lemma stateful_local_protocol_fst_rcons''' i x st ins rs r sz :
    (stateful_local_protocol''' i x st ins sz (rcons rs r)).`1 =
      let acc = (stateful_local_protocol''' i x st ins sz rs) in
      update_local_state i r x (to_local_messages (prget ins r)) acc.`1.
    rewrite /stateful_local_protocol''' => |>*. rewrite foldl_rcons => |>*. qed.  

  lemma stateful_local_protocol_snd_rcons''' i x st ins rs r sz :
    (stateful_local_protocol''' i x st ins sz (rcons rs r)).`2 =
      let acc = stateful_local_protocol''' i x st ins sz rs in
      prset acc.`2 r (from_local_messages (stateful_local_protocol_round i r x acc.`1)).
    rewrite /stateful_local_protocol''' => |>*. rewrite foldl_rcons => |>*. qed.  

  lemma stateful_local_protocol_rcons''' i x st ins rs sz r :
    (stateful_local_protocol''' i x st ins sz (rcons rs r)) =
      let acc = stateful_local_protocol''' i x st ins sz rs in
      let l = update_local_state i r x (to_local_messages (prget ins r)) acc.`1 in
      let r = prset acc.`2 r (from_local_messages (stateful_local_protocol_round i r x acc.`1)) in
      (l,r).
    rewrite /stateful_local_protocol''' => |>*. rewrite !foldl_rcons => |>*. qed.

  lemma stateful_local_protocol_up_to_iseq''' i x st ins (n n2:round) sz :
    (forall i, ISet.mem i partyset => Array.size (P.get ins i) = sz) =>
    n <= n2 => n2 <= sz =>
    stateful_local_protocol''' i x st ins sz (iseq n) = stateful_local_protocol''' i x st (prmsgs_up_to n2 ins) sz (iseq n).
    elim/natind n => |>n H0 H1 H2 H3. rewrite !iseq_nil => |>*. 
    rewrite !iseq_succ => |>H4. rewrite !stateful_local_protocol_rcons''' => |>*. rewrite H1 => |>*. smt(). congr. congr. rewrite (prget_prmsgs_up_to_lt sz) => |>*. smt(). qed.

  lemma stateful_local_protocol_up_to_iseq'' i x st ins (n n2:round) sz :
    (forall i, ISet.mem i partyset => Array.size (P.get ins i) = sz) =>
    n <= n2 => n2 <= sz =>
    stateful_local_protocol'' i x st ins sz n = stateful_local_protocol'' i x st (prmsgs_up_to n2 ins) sz n.
    move => H H0 H1. rewrite /stateful_local_protocol'' => />. rewrite (stateful_local_protocol_up_to_iseq''' i x st ins n n2 sz) => />. qed.

  lemma stateful_local_protocol_fst_filter''' i x st ins rs ss sz :
    ISet.subset (ISet.oflist rs) ss =>
    (stateful_local_protocol''' i x st ins sz rs).`1 =
      (stateful_local_protocol''' i x st (prfilter (fun r => ISet.mem r ss) ins) sz rs).`1.
    elim/last_ind rs => |>s x0 H1 H2. rewrite !stateful_local_protocol_rcons''' => |>. rewrite H1 => |>. 
    rewrite /ISet.oflist oflist_rcons in H2 => |>. have : (FSet.oflist s) \subset ss. rewrite (subset_from_l _ (ISet.set1 x0)) => |>*. move => H3. rewrite /ISet.subset /ISet.oflist H3 => |>. 
    congr. congr. rewrite /prget /prfilter /pinit => |>*. rewrite P.tP => |>j Hj1 Hj2. 
    rewrite !P.get_init !andabP !andaP => |>*. rewrite P.get_map /filter => |>*. rewrite Array.get_init => |>*.
    case (0 <= x0 && x0 < Array.size (P.get ins j)) => |>. move => H4 H5. have : ISet.mem x0  ss. rewrite /ISet.oflist oflist_rcons in H2. have : (fset1 x0) \subset ss. rewrite (subset_from_r (FSet.oflist s)) => |>*. rewrite subsetP /(<=) => />H6. rewrite /ISet.mem H6 => />. rewrite in_fset1 => />. move => H7. rewrite H7 => |>*. move => H8. rewrite Array.get_out => |>*. qed.

  lemma stateful_local_protocol_fst_succ'' i x st ins sz n :
    0 <= n => (stateful_local_protocol'' i x st ins sz (n+1)).`1 =
      update_local_state i n x (to_local_messages (prget ins n)) (stateful_local_protocol'' i x st ins sz n).`1.
    rewrite /stateful_local_protocol'' /stateful_local_protocol''' => |>*. rewrite iseq_succ => |>*. rewrite foldl_rcons => |>*. qed.  

  lemma stateful_local_protocol_snd_succ'' i x st ins sz n :
    0 <= n => (stateful_local_protocol'' i x st ins sz (n+1)).`2 = prset
      (stateful_local_protocol'' i x st ins sz n).`2
      n
      (from_local_messages ((stateful_local_protocol_round i n x (stateful_local_protocol'' i x st ins sz n).`1))).
    rewrite /stateful_local_protocol'' /stateful_local_protocol''' => |>*. rewrite iseq_succ => |>*. rewrite foldl_rcons => |>*. qed.

  lemma stateful_protocol_fst_rcons''' x st ins ns n :
    0 <= n => 
      (stateful_protocol''' x ins st (rcons ns n)).`1 = pprset (stateful_protocol''' x ins st ns).`1 n (from_messages (send_messages (stateful_protocol_round n x (stateful_protocol''' x ins st ns).`2) )).
    rewrite /stateful_protocol''' => |>H. rewrite !foldl_rcons => |>*. qed.

  lemma stateful_protocol_fst_succ'' x ws rs sz n :
    0 <= n => 
      (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) (n+1)).`1 = pprset (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) n).`1 n (from_messages (send_messages (stateful_protocol_round n x (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) n).`2) )).
    rewrite /stateful_protocol'' /stateful_protocol''' => |>*. rewrite !iseq_succ => |>*. rewrite !foldl_rcons => |>*. qed.

  lemma stateful_protocol_snd_rcons''' x st ins ns n :
    0 <= n => 
       (stateful_protocol''' x ins st (rcons ns n)).`2 = update_state n x (send_messages (stateful_protocol_round n x (stateful_protocol''' x ins st ns).`2) ) (stateful_protocol''' x ins st ns).`2.
    rewrite /stateful_protocol''' => |>*. rewrite !foldl_rcons => |>*. qed.

  lemma stateful_protocol_snd_succ'' x st ins n :
    0 <= n => 
       (stateful_protocol'' x ins st (n+1)).`2 = update_state n x (send_messages (stateful_protocol_round n x (stateful_protocol'' x ins st n).`2) ) (stateful_protocol'' x ins st n).`2.
    rewrite /stateful_protocol'' /stateful_protocol''' => |>*. rewrite !iseq_succ => |>*. rewrite !foldl_rcons => |>*.  qed.

  lemma stateful_protocol_sz_snd_succ'' sz x ws rs n :
    0 <= n =>
    (stateful_protocol_sz'' sz x ws rs (n+1)).`2 = update_state n x (send_messages (stateful_protocol_round n x (stateful_protocol_sz'' sz x ws rs n).`2) ) (stateful_protocol_sz'' sz x ws rs n).`2.
    move => Hn. rewrite /stateful_protocol_sz'' => |>. rewrite stateful_protocol_snd_succ'' => |>. qed.

  lemma prdom_stateful_local_protocol_snd'' sz i x ws rs r ins :
    0 <= sz =>
    prdom sz r (stateful_local_protocol'' i x (init_local_state i x ws rs) ins sz r).`2.
    rewrite /stateful_local_protocol'' /stateful_local_protocol''' => |>*. elim/natind:r => |>*. rewrite iseq_nil => |>*. rewrite prdom_prempty => |>*. rewrite iseq_succ => |>*. rewrite foldl_rcons => |>*. rewrite prdom_prset => |>*. qed.

  lemma stateful_protocol_snd_iseq''' x ins1 ins2 st (n:round) :
    (forall i j r, ISet.mem i partyset => ISet.mem j partyset => 0 <= r < n => Array.get (P.get (P.get ins1 i) j) r = Array.get (P.get (P.get ins2 i) j) r ) =>
    (stateful_protocol''' x ins1 st (iseq n)).`2 = (stateful_protocol''' x ins2 st (iseq n)).`2.
    elim/natind n => |>n H0 H1. rewrite !iseq_nil => />*.  
    rewrite !iseq_succ => |>H4. rewrite !stateful_protocol_snd_rcons''' => |>*. rewrite H1 => />. clear H1. move => i j r Hi Hj Hr1 Hr2. rewrite H4 => />. smt(). qed.

  lemma get_stateful_local_protocol_out'' sz (n n2:round) i j x inp rs ins :
    ISet.mem i partyset => n <= n2 =>
    (Array.get ((P.get (stateful_local_protocol'' j x (init_local_state j x inp rs) ins sz n).`2 i)) n2) = witness.
    rewrite /stateful_local_protocol''. elim/natind:n => |>n H1 H2 H3. rewrite /stateful_local_protocol''' => |>*. rewrite iseq_nil => |>*. rewrite get_prempty H2 => |>*. rewrite Array.get_init => |>*. 
    rewrite iseq_succ => |>H4. rewrite stateful_local_protocol_rcons''' => |>*. rewrite get_prset H3 => |>*. rewrite Array.get_set_neqE => |>*. smt(). rewrite H2 => |>*. smt(). qed.

  lemma pprdom_stateful_protocol_fst'' sz x ws rs r :
    0 <= sz => 
    pprdom sz r (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) r).`1.
    rewrite /stateful_protocol'' /stateful_protocol''' => |>*. elim/natind:r => |>*. rewrite iseq_nil => |>*. rewrite pprdom_pprempty => |>*. rewrite iseq_succ => |>*. rewrite foldl_rcons => |>*. rewrite pprdom_pprset => |>*. qed.

  lemma pprdom_stateful_protocol_fst''' sz x ws rs r :
    0 <= sz => 
    pprdom sz r (stateful_protocol''' x (pprempty sz witness) (init_state x ws rs) (iseq r)).`1.
    rewrite /stateful_protocol'' /stateful_protocol''' => |>*. elim/natind:r => |>*. rewrite iseq_nil => |>*. rewrite pprdom_pprempty => |>*. rewrite iseq_succ => |>*. rewrite foldl_rcons => |>*. rewrite pprdom_pprset => |>*. qed.

  lemma get_stateful_protocol_fst_out'' (x:public_input) (ins:in_msgs pmap) (st:state) (rs:round) i j r :
    ISet.mem i partyset => ISet.mem j partyset => ! (0 <= r < rs) =>
    get (P.get (P.get (stateful_protocol'' x ins st rs).`1 i) j) r = get (P.get (P.get ins i) j) r.
    move => Hi Hj. rewrite /stateful_protocol'' => />. elim/natind:rs => />n.
    move => H H0. rewrite iseq_nil => />. 
    move => H H0 H1. rewrite iseq_succ => />. rewrite stateful_protocol_fst_rcons''' => />. rewrite get_pprset Hi => />. rewrite get_prset Hj => />. rewrite /from_messages => />. rewrite get_pmap => />. rewrite (get_from_local_messages_send_messages x n) => />. rewrite valid_stateful_protocol_round => />. rewrite get_set_neqE => />. smt(). rewrite H0 => />. smt(). qed.

  lemma get_local_state_set sz i n n2 x ws rs ins m :
    (forall i, ISet.mem i partyset => Array.size (P.get ins i) = sz) =>
    ISet.mem i partyset /\ prdom sz n2 ins /\ 0 <= n /\ n <= n2 /\ n2 < sz => 
      get_local_state i n x ws rs (prset ins n2 m) = get_local_state i n x ws rs ins.
   progress. rewrite (get_local_state_prmsgs_up_to sz _ n n2) => |>. move => j Hj. rewrite get_prset => |>. rewrite Hj => |>. rewrite Array.size_set => |>. rewrite H => |>. smt(). rewrite prmsgs_up_to_lt_set => |>*. rewrite -(get_local_state_prmsgs_up_to sz _ n n2) => |>*. smt(). qed.

  lemma get_state_pprmsgs_up_to sz n rounds2 x ws rs ins :
    pprdom sz rounds2 ins /\ 0 <= n /\ n <= rounds2 /\ rounds2 <= sz => 
      get_state n x ws rs ins = get_state n x ws rs (pprmsgs_up_to n ins).
    rewrite /get_state => |>H0 H1 H2 H3. rewrite pmap_eqP => |>y Hy. rewrite !get_pimap => |>. rewrite !get_pzip3 !Hy => |>. rewrite get_pprmsgs_up_to => |>. rewrite (get_local_state_prmsgs_up_to sz _ n n) => |>. move => j Hj.
    move :H0. rewrite /pprdom P.allP => |>H0. have : prdom sz rounds2 ((P.get ins y)). rewrite H0 => |>. move :Hy. rewrite /ISet.mem iset_in_def => |>. rewrite /prdom P.allP => |>H5. have : rdom sz rounds2 ((P.get ((P.get ins y)) j)). rewrite H5 => |>. move :Hj. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. 
    smt(). qed.

  lemma get_state_set sz n x ws rs ins m :
    pprdom sz n ins /\ 0 <= n < sz =>
      get_state n x ws rs (pprset ins n m) = get_state n x ws rs ins.
    progress. rewrite (get_state_pprmsgs_up_to sz n (n+1) x ws rs (pprset ins n m)) => |>*. rewrite pprdom_pprset => |>. smt(). smt().
    rewrite pprmsgs_up_to_lt_set => |>*. rewrite - (get_state_pprmsgs_up_to sz n n) => |>*. smt(). qed.

  lemma get_state_prefix_protocol'' sz x ws rs n n2 :
    0 <= n /\ n <= n2 /\ n2 <= sz => 
      get_state n x ws rs (protocol'' x ws rs (pprempty sz witness) n) = get_state n x ws rs (protocol'' x ws rs (pprempty sz witness) n2).
    progress. rewrite (_: get_state n x ws rs (protocol'' x ws rs (pprempty sz witness) n2) = get_state n x ws rs (pprmsgs_up_to n (protocol'' x ws rs (pprempty sz witness) n2)) ). rewrite (get_state_pprmsgs_up_to sz n n2) => |>. have : ST.pprdom sz n2 (protocol'' x ws rs (pprempty sz witness) n2). rewrite pprdom_protocol'' => |>*. smt(). rewrite ST.pprdom_pprempty => |>*. smt(). smt(). rewrite /pprdom P.allP => |>H3 i Hi1 Hi2.
    rewrite (_:pprmsgs_up_to = ST.pprmsgs_up_to). rewrite /pprmsgs_up_to => |>*. congr. rewrite prefix_protocol'' => |>*. smt(). qed.

  lemma get_state_init sz x ws rs :
    get_state 0 x ws rs (pprempty sz witness) = init_state x ws rs.
    rewrite /get_state /init_state => |>*. rewrite pmap_eqP => |>y Hy. rewrite !get_pimap => |>*. 
rewrite !get_pzip3 !Hy => |>*. rewrite !get_pzip => |>*. rewrite get_pprempty !Hy => |>*. rewrite /get_local_state /get_local_state' iseq_nil => |>*. qed.

  lemma size_get_stateful_local_protocol_snd'' sz i x st ins r j :
    0 <= j < P.size => 
    prdom sz r ((stateful_local_protocol'' i x st ins sz r).`2) =>
    Array.size (P.get (stateful_local_protocol'' i x st ins sz r).`2 j) = sz.
    rewrite /prdom P.allP => |>J1 J2 H.
    have : rdom sz r ((P.get (stateful_local_protocol'' i x st ins sz r).`2 j)). rewrite H => |>. rewrite /rdom => |>H1. qed.

  lemma size_get_stateful_protocol_fst'' sz x ins st n i j :
    0 <= i < P.size => 0 <= j < P.size => 
    pprdom sz n (stateful_protocol'' x ins st n).`1 =>
    Array.size (P.get (P.get (stateful_protocol'' x ins st n).`1 i) j) = sz.
    rewrite /pprdom P.allP => |>H1 H2 H3 H4 H5. 
    have : prdom sz n ((P.get (stateful_protocol'' x ins st n).`1 i)). rewrite H5 => |>. rewrite /prdom P.allP => |>H6. have : rdom sz n ((P.get ((P.get (stateful_protocol'' x ins st n).`1 i)) j)). rewrite H6 => |>. rewrite /rdom => |>. qed.

  lemma size_get_stateful_protocol_fst''' sz x ins st n rounds i j :
    0 <= i < P.size => 0 <= j < P.size => 
    pprdom sz n (stateful_protocol''' x ins st rounds).`1 =>
    Array.size (P.get (P.get (stateful_protocol''' x ins st rounds).`1 i) j) = sz.
    rewrite /pprdom P.allP => |>H1 H2 H3 H4 H5. 
    have : prdom sz n ((P.get (stateful_protocol''' x ins st rounds).`1 i)). rewrite H5 => |>. rewrite /prdom P.allP => |>H6. have : rdom sz n ((P.get ((P.get (stateful_protocol''' x ins st rounds).`1 i)) j)). rewrite H6 => |>. rewrite /rdom => |>. qed.

  lemma equiv_stateful_protocol_sz_snd''' (n1 n2:round) x ys cs r :
    r <= n1 => r <= n2 => 
    (stateful_protocol''' x (pprempty n1 witness) (init_state x ys cs) (iseq r)).`2 =
    (stateful_protocol''' x (pprempty n2 witness) (init_state x ys cs) (iseq r)).`2.
    move => R1 R2. rewrite /stateful_protocol /stateful_protocol_sz /stateful_protocol' /stateful_protocol_sz' => />. move : R1 R2. elim/natind:r => />r.
    move => R0 R1 R2. rewrite /stateful_protocol'' /stateful_protocol''' => />. rewrite !iseq_nil => />.
    move => R0 H R1 R2. rewrite !iseq_succ => />. rewrite !stateful_protocol_snd_rcons''' => />. congr. congr. congr. rewrite H => />. smt(). smt(). rewrite H => />. smt(). smt(). qed.

  lemma equiv_stateful_protocol_sz_snd n x ys cs :
    (stateful_protocol_sz n x ys cs).`2 = (stateful_protocol x ys cs).`2.
    rewrite /stateful_protocol /stateful_protocol_sz /stateful_protocol' /stateful_protocol_sz' => />. congr. pose re := pprempty (rounds x) witness. elim/natind:(rounds x) => />r H0.
    rewrite /stateful_protocol'' /stateful_protocol''' => />. rewrite !iseq_nil => />.
    rewrite !stateful_protocol_snd_succ'' => />H1. rewrite H1 => />. qed.

  lemma equiv_stateful_protocol_sz_fst n x ys cs :
    0 <= n => 
    (stateful_protocol_sz n x ys cs).`1 = P.map (prod idfun (prod (prext n) idfun)) (stateful_protocol x ys cs).`1.
    move => N. rewrite /stateful_protocol /stateful_protocol_sz /stateful_protocol' /stateful_protocol_sz' => />. rewrite pmap_eqP => />y Hy. rewrite get_pmap => />. rewrite !get_pzip3 !Hy /prod /idfun => />. 
    pose rx := rounds x. rewrite /rx.
    pose re := pprempty (rounds x) witness. have : rounds x <= rx. progress. rewrite /prext => />. rewrite pmap_eqP => />R o Ho. rewrite get_pinit Ho => />. rewrite tP => />. rewrite size_init => />. rewrite (size_get_stateful_protocol_fst'' n) => />. move :Hy. rewrite /ISet.mem iset_in_def => />. move :Ho. rewrite /ISet.mem iset_in_def => />. rewrite pprdom_stateful_protocol_fst'' => />. rewrite ge0_max => />. move => j Hj1 Hj2. rewrite get_init andabP andaP => />. rewrite (size_get_stateful_protocol_fst'' (rounds x)) => />. move :Hy. rewrite /ISet.mem iset_in_def => />. move :Ho. rewrite /ISet.mem iset_in_def => />. rewrite pprdom_stateful_protocol_fst'' => />. rewrite rounds_ge0 => />. case (j < rounds x) => />J. rewrite Hj1 => />.
    move :Hy Ho Hj1 Hj2 J. rewrite (_:j < rounds x = j < rx). progress. elim/natind:(rounds x) y o j => />r.
    move => R1 y o j Hy Ho Hj1 Hj2 J. rewrite /stateful_protocol'' /stateful_protocol''' !iseq_nil => />. rewrite /re !get_pprempty !Hy => />. rewrite !get_prempty !Ho => />. rewrite !get_init => />.
    move => R1 R2 y o j Hy Ho Hj1 Hj2 J. rewrite /stateful_protocol'' !iseq_succ => />. rewrite !stateful_protocol_fst_rcons''' => />. rewrite !get_pprset !Hy => />. rewrite !get_prset !Ho => />. rewrite /from_messages => />. rewrite get_pmap => />. rewrite (get_from_local_messages_send_messages x r) => />. rewrite valid_stateful_protocol_round => />. rewrite !get_setE => />. rewrite !R2 => />. rewrite (size_get_stateful_protocol_fst''' n _ _ _ r) => />. move :Hy. rewrite /ISet.mem iset_in_def => />. move :Ho. rewrite /ISet.mem iset_in_def => />. rewrite pprdom_stateful_protocol_fst''' => />. rewrite (size_get_stateful_protocol_fst''' (rounds x) _ _ _ r) => />. move :Hy. rewrite /ISet.mem iset_in_def => />. move :Ho. rewrite /ISet.mem iset_in_def => />. rewrite pprdom_stateful_protocol_fst''' => />. rewrite rounds_ge0 => />. rewrite get_pmap => />. rewrite (get_from_local_messages_send_messages x r) => />. rewrite valid_stateful_protocol_round => />. rewrite !andabP !J !Hj1 !Hj2 => />. case (j=r) => />.
    congr. congr. congr. congr. have : (stateful_protocol_sz n x ys cs).`2 = (stateful_protocol x ys cs).`2. rewrite equiv_stateful_protocol_sz_snd => />. rewrite /stateful_protocol_sz /stateful_protocol => />. rewrite (equiv_stateful_protocol_sz_snd''' n (rounds x)) => />. smt(). smt(). rewrite get_stateful_protocol_fst_out'' => />. smt(). rewrite get_pprempty Hy => />. rewrite get_prempty Ho => />. rewrite get_init => />. qed.

  lemma get_state_succ' sz i n x ws rs ins :
    ISet.mem i partyset /\ 0 <= n /\ n < sz =>
      (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) n).`2 = get_state n x ws rs (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) n).`1 =>
      ins = (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) (n+1)).`1 => 
      get_local_state i (n+1) x (P.get ws i) (P.get rs i) (P.get ins i) = update_local_state i n x (to_local_messages (P.map (fun pmsgs => P.get (from_local_messages pmsgs) i) (stateful_protocol_round n x (get_state n x ws rs ins)))) (get_local_state i n x (P.get ws i) (P.get rs i) (P.get ins i)).
    rewrite /get_local_state /get_local_state' /get_state => |>H2 H3 H4 H5. rewrite !iseq_succ => |>. rewrite !foldl_rcons => |>*. congr. congr. rewrite pmap_eqP => |>y Hy. 
    have : pprdom sz n (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) n).`1. rewrite pprdom_stateful_protocol_fst'' => |>*. smt(). progress.
    have : prdom sz n (P.get (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) n).`1 y). rewrite (pprdom_prdom_get sz n) => |>*. progress. 
    rewrite !get_pmap => |>*. rewrite !stateful_protocol_fst_succ'' => |>*. rewrite !get_pprset H2 => |>*. rewrite !get_prget Hy => |>*. rewrite !get_prset Hy => |>*. 
    rewrite Array.get_set_eqE /from_buffer => |>. move => H6. rewrite (size_get_stateful_protocol_fst'' sz) => |>. move :H2. rewrite /ISet.mem iset_in_def => |>. move :Hy. rewrite /ISet.mem iset_in_def => |>. 
    rewrite get_pmap => |>*. rewrite (get_send_messages x n) => |>*. rewrite /stateful_protocol_round => |>*. rewrite /valid_messages /all allP => |>z Hz. rewrite P.get_imap => |>. move :Hz. rewrite in_iseq => |>*. rewrite valid_stateful_local_protocol_round => |>*. 
    rewrite /stateful_protocol_round !get_pimap => |>*. rewrite !get_pzip3 !Hy => |>*. rewrite get_pprset => |>*. rewrite !get_pmap => |>*. rewrite (get_send_messages x n) => |>*. rewrite /valid_messages /all allP => |>z Hz. rewrite P.get_imap => |>*. move :Hz. rewrite in_iseq => |>*. rewrite valid_stateful_local_protocol_round => |>*. 
    rewrite !(from_to_local_messages x n) => |>*. rewrite /valid_pmsgs /all allP => |> z Hz. rewrite P.get_map => |>*. move :Hz. rewrite in_iseq => |>*. rewrite P.get_imap => |>*. move :Hz. rewrite in_iseq => |>*. rewrite valid_pmsgs_get => |>. move :H2. rewrite /ISet.mem iset_in_def => |>. rewrite valid_pmsgs_from => |>. rewrite valid_stateful_local_protocol_round => |>. rewrite /valid_pmsgs P.allP => |>j Hj1 Hj2. rewrite P.get_map => |>. rewrite P.get_imap => |>. rewrite valid_pmsgs_get => |>. move :Hy. rewrite /ISet.mem iset_in_def => |>. rewrite valid_pmsgs_from => |>. rewrite valid_stateful_local_protocol_round => |>. 
    rewrite !get_pmap => |>*. congr. congr. 
    rewrite !get_pimap => |>*. congr. rewrite Hy => |>. rewrite (get_local_state_set sz) => |>. move => k Hk. rewrite (size_get_stateful_protocol_fst'' sz) => |>. move :Hy. rewrite /ISet.mem iset_in_def => |>. move :Hk. rewrite /ISet.mem iset_in_def => |>. 
    rewrite H5 => |>. rewrite get_pimap => |>*. rewrite !get_pzip3 !Hy => |>*. qed. 

  lemma get_state_succ sz n x ws rs ins :
    0 <= n /\ n < sz => 
      (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) n).`2 = get_state n x ws rs (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) n).`1 =>
      ins = (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) (n+1)).`1 =>
      get_state (n+1) x ws rs ins = update_state n x (send_messages (stateful_protocol_round n x (get_state n x ws rs ins)) ) (get_state n x ws rs ins).
    rewrite /get_state /update_state => |>H2 H3 H4. rewrite pmap_eqP => |>y Hy. rewrite !get_pimap => |>*. rewrite !get_pzip3 !Hy => |>*. rewrite get_pzip !Hy => |>. rewrite !get_pimap => |>*. rewrite !get_pzip3 !Hy => |>*. 
    rewrite (get_state_succ' sz y n x ws rs _) => |>*.  congr. rewrite (get_send_messages x n) => |>*. rewrite valid_stateful_protocol_round => |>. qed.

  (* Equivalence *)
  
  lemma equiv_stateful_protocol_round round x ws rs ins :
    from_messages (stateful_protocol_round round x (get_state round x ws rs ins)) = protocol_round round x ws rs ins.
    rewrite /stateful_protocol_round /protocol_round => |>. rewrite pmap_eqP => |>y Hy.
    rewrite !get_pimap => |>*. rewrite !get_pzip3 !Hy => |>*. rewrite /from_buffer get_pmap => |>*. rewrite !get_pimap => |>*. rewrite /local_protocol_round => |>*. congr. congr. rewrite /get_state get_pimap => |>*. rewrite !get_pzip3 !Hy => |>*. qed.    

  lemma equiv_stateful_protocol'' sz (round:round) x ws rs :
    0 <= round /\ round <= sz =>
      get_state round x ws rs (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) round).`1 = (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) round).`2.
     elim/natind:round => |>n H1 H2 H3. rewrite /stateful_protocol''. rewrite (iseq_nil n) => |>*. have : n = 0. smt(). progress. rewrite -(get_state_init sz) => |>*.
    move => H5. rewrite (get_state_succ sz) => |>*. smt(). rewrite H2 => |>*. smt(). 
    rewrite stateful_protocol_snd_succ'' => |>*. rewrite stateful_protocol_fst_succ'' => |>*. rewrite !(get_state_set sz) => |>*. rewrite pprdom_stateful_protocol_fst'' => |>*. smt(). smt(). rewrite H2 => |>*. smt(). qed.

  lemma equiv_stateful_protocol_fst'' (sz:int) x ws rs round :
    round <= sz =>
      (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) round).`1 = protocol'' x ws rs (pprempty sz witness) round.
    rewrite /stateful_protocol'' /protocol'' => |>H2. 
    move :H2. elim/natind:round => |>n H3 H4. rewrite iseq_nil => |>. rewrite iseq_succ => |>H5. rewrite !foldl_rcons => |>. rewrite -H4. clear H4. smt(). clear H4. rewrite  /pprset. rewrite /merge. rewrite pmap_eqP => |>k Hk. rewrite !get_pinit !Hk => |>. rewrite pmap_eqP => |>z Hz. rewrite !get_pinit !Hz !Hk => |>. rewrite !get_pinit !Hz => |>.
    rewrite - (equiv_stateful_protocol_round n x ws rs _). rewrite stateful_protocol_fst_rcons''' => |>*. rewrite /pprset /merge => |>. rewrite get_pinit Hk => |>. rewrite get_pinit Hz => |>. 
    congr. rewrite /from_messages !get_pmap => |>. rewrite (get_from_local_messages_send_messages x n) => |>. rewrite valid_stateful_protocol_round => |>. congr. congr. congr. congr. 
    rewrite equiv_stateful_protocol'' => |>. smt(). qed.

  lemma equiv_stateful_protocol_fst' x ws rs :
    (stateful_protocol' x ws rs).`1 = protocol' x ws rs.
    rewrite /stateful_protocol' /protocol' => |>*. rewrite equiv_stateful_protocol_fst'' => |>*. qed.

  lemma equiv_stateful_protocol_snd'' sz x n ws rs :
    0 <= n /\ n <= sz => 
      (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) n).`2 = get_state n x ws rs (protocol'' x ws rs (pprempty sz witness) n).
    rewrite /stateful_protocol'' /protocol'' => |>H2 H3. move :H2 H3. elim/natind:n => |>n N1 N2 N3. rewrite iseq_nil => |>*. rewrite /stateful_protocol''' => |>. have : n=0. smt(). move => N0. rewrite N0. rewrite -(get_state_init sz) => |>*. 
    rewrite !iseq_succ => |>N4. rewrite !foldl_rcons => |>*. rewrite (get_state_succ sz n) => |>*. smt(). rewrite equiv_stateful_protocol'' => |>*. smt().  
    rewrite (_: (foldl (fun (ins : in_msgs pmap) (round : round) => ST.pprset ins round (ppswap (protocol_round round x ws rs ins))) (ST.pprempty sz witness) (iseq n)) = protocol'' x ws rs (pprempty sz witness) n ). rewrite /protocol'' => |>*. have : ST.pprdom sz n (protocol'' x ws rs (ST.pprempty sz witness) n). rewrite pprdom_protocol'' => |>*. smt(). rewrite ST.pprdom_pprempty => |>. smt(). move => N5.
    rewrite equiv_stateful_protocol_fst'' => |>*. rewrite -protocol_succ'' => |>*.
    rewrite stateful_protocol_snd_rcons''' => |>. rewrite N2 => |>. smt(). congr. 
    rewrite -(send_messages_bij x n) => |>*. rewrite valid_stateful_protocol_round => |>. rewrite valid_stateful_protocol_round => |>. congr. 
    rewrite (_: (foldl (fun (ins : in_msgs pmap) (round : round) => ST.pprset ins round (ST.ppswap (protocol_round round x ws rs ins))) (pprempty sz witness) (iseq n)) = protocol'' x ws rs (pprempty sz witness) n ). rewrite /protocol'' => |>*. rewrite (get_state_set sz) => |>. rewrite pprdom_protocol'' => |>. smt(). apply ST.pprdom_pprempty => |>. smt(). smt(). 
    rewrite (_: (foldl (fun (ins : in_msgs pmap) (round : round) => ST.pprset ins round (ST.ppswap (protocol_round round x ws rs ins))) (pprempty sz witness) (iseq n)) = protocol'' x ws rs (pprempty sz witness) n ). rewrite /protocol'' => |>*. rewrite (get_state_set sz) => |>. rewrite pprdom_protocol'' => |>. smt(). apply ST.pprdom_pprempty => |>. smt(). smt(). qed.

  lemma equiv_get_stateful_protocol_snd'' sz round i x ws rs :
    ISet.mem i partyset /\ 0 <= round /\ round <= sz =>
      P.get (stateful_protocol'' x (pprempty sz witness) (init_state x ws rs) round).`2 i = get_local_state i round x (P.get ws i) (P.get rs i) (P.get (protocol'' x ws rs (pprempty sz witness) round) i).
    progress. rewrite equiv_stateful_protocol_snd'' => |>*. rewrite /get_state get_pimap => |>*. rewrite !get_pzip3 !H => |>*. qed.

  lemma equiv_stateful_protocol_end x ws rs :
    stateful_protocol_end x (stateful_protocol' x ws rs).`2 = protocol_end x ws rs (protocol' x ws rs).
    rewrite /stateful_protocol_end /protocol_end => |>*. rewrite pmap_eqP => |>y Hy. rewrite !get_pimap => |>*. rewrite !get_pzip3 !Hy => |>*. rewrite /local_protocol_end => |>*. congr. 
    rewrite /protocol' /stateful_protocol' => |>*. rewrite equiv_get_stateful_protocol_snd'' => |>*. rewrite rounds_ge0 => |>*. qed.
  
  lemma equiv_stateful_protocol_snd x ws cs :
    (stateful_protocol x ws cs).`2 = (protocol x ws cs).`2.
    rewrite /stateful_protocol /protocol => |>*. rewrite equiv_stateful_protocol_end => |>*. qed.

  lemma equiv_stateful_protocol x ws rs :
    stateful_protocol x ws rs = protocol x ws rs.
    progress. rewrite /stateful_protocol /protocol => |>*. split. rewrite equiv_stateful_protocol_fst' => |>*. rewrite equiv_stateful_protocol_end => |>*. qed.

  lemma stateful_local_global_consistency x tr :
    (valid_trace x tr /\ consistent_trace x tr) = (exists ws rs, valid_inputs x ws /\ valid_rands x rs /\ (stateful_protocol x ws rs).`1 = tr).
    rewrite eq_logical => |>*. progress. exists (get_trace_inputs tr) (get_trace_rands tr) => |>*. rewrite equiv_stateful_protocol => |>*. rewrite consistent_trace_inputs => |>*. rewrite consistent_trace_rands => |>*. rewrite local_consistency => |>. 
    rewrite equiv_stateful_protocol => |>*. rewrite valid_trace_protocol => |>. rewrite equiv_stateful_protocol => |>i j H1. smt(global_consistency). qed.

  lemma stateful_protocol_consistency cs x ws :
    view_outputs x (stateful_protocol x ws cs).`1 = (stateful_protocol x ws cs).`2.
    progress. rewrite !equiv_stateful_protocol => |>*. rewrite protocol_consistency => |>*. qed.

  lemma equiv_stateful_local_protocol_fst'' i n x inp rs ins sz :
    0 <= n => (stateful_local_protocol'' i x (init_local_state i x inp rs) ins sz n).`1 = get_local_state i n x inp rs ins.
    elim/natind:n => |>*. rewrite /stateful_local_protocol'' /get_local_state /get_local_state' => |>*. rewrite !iseq_nil => |>*. 
    rewrite get_local_state_succ => |>*. rewrite stateful_local_protocol_fst_succ'' => |>*. congr. qed.

  lemma equiv_stateful_local_protocol'' i x (vi:view) sz :
    (stateful_local_protocol'' i x (init_local_state i x vi.`1 vi.`2.`2) vi.`2.`1 sz (rounds x)).`2 =
      local_protocol'' i x vi.`1 vi.`2.`2 vi.`2.`1 sz ((rounds x)).
    elim/natind:(rounds x) => |>n H. rewrite /stateful_local_protocol'' /local_protocol'' => |>*. rewrite !iseq_nil => |>*. 
    rewrite local_protocol_succ'' => |>H1. rewrite stateful_local_protocol_snd_succ'' => |>*. rewrite H1 => |>*. clear H1. rewrite /prset => |>*. rewrite /merge => |>. rewrite pmap_eqP => |>y Hy. rewrite !get_pinit !Hy => |>. congr. rewrite /local_protocol_round => |>*. congr. congr. rewrite equiv_stateful_local_protocol_fst'' => |>*. qed.

  lemma equiv_stateful_local_protocol' i x (vi:view) :
    (stateful_local_protocol' i x (init_local_state i x vi.`1 vi.`2.`2) vi.`2.`1).`2 = local_protocol' i x vi.
    rewrite /stateful_local_protocol' /local_protocol' => |>*. 
    rewrite equiv_stateful_local_protocol'' => |>*. qed.

  lemma equiv_stateful_local_protocol i x vi :
    stateful_local_protocol i x vi = local_protocol i x vi.
    rewrite /stateful_local_protocol /stateful_local_protocol' /local_protocol /local_protocol' => |>*. 
    rewrite equiv_stateful_local_protocol'' => |>*. rewrite /local_protocol_end => |>*. congr. 
    rewrite equiv_stateful_local_protocol_fst'' => |>*. rewrite rounds_ge0 => |>*. qed.

  lemma equiv_get_stateful_protocol_sz'' sz i j n x ws rs :
    ISet.mem i ST.partyset => ISet.mem j ST.partyset =>
    0 <= n => n < ST.rounds x => rounds x <= sz =>
    get (ST.P.get (ST.P.get (protocol' x ws rs) i) j) n =
    ST.P.get (from_local_messages (ST.P.get (stateful_protocol_round n x (stateful_protocol_sz'' sz x ws rs n).`2) j)) i.
    move => Hi Hj Hn1 Hn2 Hn3.
    rewrite /protocol' => |>. rewrite (split_protocol'' (ST.rounds x) (n+1) (ST.rounds x)) => |>. smt(). rewrite get_protocol_out''' => |>. smt(). smt(). have : 0 <= rounds x. rewrite rounds_ge0 => |>. move => H. smt(). 
    rewrite (get_protocol_prefix_sz'' (rounds x) sz) => |>. smt(). smt(). smt().
    rewrite protocol_succ'' => |>. rewrite ST.get_pprset Hi => |>. rewrite ST.get_prset Hj => |>. rewrite /stateful_protocol_sz'' /ppswap ST.get_ppinit Hi => |>. rewrite ST.get_pinit Hj => |>.
    rewrite get_set_eqE => |>. rewrite (size_get_get_protocol'' sz) => |>. smt(). rewrite ST.pprdom_pprempty => |>. smt(). smt().
    rewrite /stateful_protocol_round /protocol_round /local_protocol_round => |>. rewrite !ST.get_pimap => |>. rewrite !ST.get_pzip3 !Hj => |>. congr. congr. congr. 
    rewrite -equiv_stateful_protocol_fst'' => |>. smt(). rewrite -equiv_stateful_protocol'' => |>. smt(). rewrite /get_state get_pimap => |>. rewrite !get_pzip3 !Hj => |>. qed.

  (*Consistency*)

  lemma stateful_local_consistency x tr ws rs :
    ws = ST.get_trace_inputs tr =>
    rs = ST.get_trace_rands tr =>
    valid_trace x tr /\ consistent_trace x tr => (stateful_protocol x ws rs).`1 = tr.
    progress. rewrite equiv_stateful_protocol => |>*. rewrite local_consistency => |>*. qed.

  (* used for MitH output validation *)
  op stateful_consistent_outputs (x:public_input) (i j:party) : local_output -> local_output -> bool.
  
  type local_state2 = local_state * local_state.

  op stateful_consistent_views_outputs_round (r:round) (x:public_input) (i j:party) (ins1 ins2:in_msgs) (sts:local_state2) : local_state2 * bool =
    let outs1 = from_local_messages (stateful_local_protocol_round i r x sts.`1) in
    let outs2 = from_local_messages (stateful_local_protocol_round j r x sts.`2) in
    let in1 = prget ins1 r in
    let in2 = prget ins2 r in
    let sts1' = update_local_state i r x (to_local_messages in1) sts.`1 in
    let sts2' = update_local_state j r x (to_local_messages in2) sts.`2 in
    let b = (eq_msg (P.get outs1 j) (P.get in2 i)) /\ (eq_msg (P.get outs2 i) (P.get in1 j)) in
    ((sts1',sts2'),b).

  op stateful_consistent_views_outputs''' (x:public_input) (i j:party) (ins1 ins2:in_msgs) (sts:local_state2) rounds : local_state2 * bool =
    let go = fun (stb:_*_) r =>
      let stb' = stateful_consistent_views_outputs_round r x i j ins1 ins2 stb.`1 in
      (stb'.`1,stb.`2 /\ stb'.`2) in
    foldl go (sts,true) rounds.

  op stateful_consistent_views_outputs'' (x:public_input) (i j:party) (ins1 ins2:in_msgs) (sts:local_state2) : local_state2 * bool =
    stateful_consistent_views_outputs''' x i j ins1 ins2 sts (iseq (rounds x)).

  op stateful_consistent_views_outputs' (x:public_input) (i j:party) (vi vj:view) : local_state2 * bool =
    let st1 = init_local_state i x vi.`1 vi.`2.`2 in
    let st2 = init_local_state j x vj.`1 vj.`2.`2 in
    let outsb = stateful_consistent_views_outputs'' x i j vi.`2.`1 vj.`2.`1 (st1,st2) in
    outsb.

  (* streamlined consistency checking gate by gate without constructing output messages *)
  op stateful_consistent_views_outputs (x:public_input) (i j:party) (vi vj:view) : bool =
    let outsb = stateful_consistent_views_outputs' x i j vi vj in
    let outs1 = outsb.`1.`1 in
    let outs2 = outsb.`1.`2 in
    let b = outsb.`2 in
    let out1 = stateful_local_protocol_end i x outs1 in
    let out2 = stateful_local_protocol_end j x outs2 in
    b /\ stateful_consistent_outputs x i j out1 out2.

  lemma stateful_consistent_views_outputs_rcons''' x i j ins1 ins2 sts rs r :
    stateful_consistent_views_outputs''' x i j ins1 ins2 sts (rcons rs r) =
      let sts' = stateful_consistent_views_outputs''' x i j ins1 ins2 sts rs in
      let sts'' = stateful_consistent_views_outputs_round r x i j ins1 ins2 sts'.`1 in
      (sts''.`1,sts'.`2 /\ sts''.`2).
    rewrite /stateful_consistent_views_outputs''' => |>*. rewrite foldl_rcons => |>*. qed.

  lemma stateful_consistent_views_outputs_round_up_to sz (n n2:round) x i j ins1 ins2 sts :
    (forall i, ISet.mem i partyset => Array.size (P.get ins1 i) = sz) =>
    (forall i, ISet.mem i partyset => Array.size (P.get ins2 i) = sz) =>
    0 <= n < n2 => n2 <= sz => 
    stateful_consistent_views_outputs_round n x i j ins1 ins2 sts =
    stateful_consistent_views_outputs_round n x i j (prmsgs_up_to n2 ins1) (prmsgs_up_to n2 ins2) sts.
    rewrite /stateful_consistent_views_outputs_round => |>H1 H2 H3 H4 H5. progress. congr. congr. rewrite (prget_prmsgs_up_to_lt sz) => |>*. congr. congr. rewrite (prget_prmsgs_up_to_lt sz) => |>*. rewrite !(prget_prmsgs_up_to_lt sz) => |>*. qed.

  lemma stateful_consistent_views_outputs_up_to_iseq''' sz (n n2:round) x i j ins1 ins2 sts :
    (forall i, ISet.mem i partyset => Array.size (P.get ins1 i) = sz) =>
    (forall i, ISet.mem i partyset => Array.size (P.get ins2 i) = sz) =>
    n <= n2 => n2 <= sz => 
    stateful_consistent_views_outputs''' x i j ins1 ins2 sts (iseq n) =
    stateful_consistent_views_outputs''' x i j (prmsgs_up_to n2 ins1) (prmsgs_up_to n2 ins2) sts (iseq n).
    move => H1 H2. elim/natind n => |>n N1 N2 N3. rewrite !iseq_nil => |>*.
    rewrite !iseq_succ => |>N4. rewrite !stateful_consistent_views_outputs_rcons''' => |>*. rewrite !N2 => |>*. smt(). clear N2. progress. rewrite (stateful_consistent_views_outputs_round_up_to sz n n2) => |>*. smt(). rewrite (stateful_consistent_views_outputs_round_up_to sz n n2) => |>*. smt(). qed.

  lemma stateful_consistent_views_outputs_left''' sz x i j ins1 ins2 sts rs :
    (stateful_consistent_views_outputs''' x i j ins1 ins2 sts rs).`1.`1 =
    (stateful_local_protocol''' i x sts.`1 ins1 sz rs).`1.
    elim/last_ind rs => |>s x0 H. 
    rewrite stateful_consistent_views_outputs_rcons''' => |>*.
    rewrite stateful_local_protocol_fst_rcons''' => |>*. rewrite -H => |>*. qed.

  lemma stateful_consistent_views_outputs_right''' sz x i j ins1 ins2 sts rs :
    (stateful_consistent_views_outputs''' x i j ins1 ins2 sts rs).`1.`2 =
    (stateful_local_protocol''' j x sts.`2 ins2 sz rs).`1.
    elim/last_ind rs => |>s x0 H. 
    rewrite stateful_consistent_views_outputs_rcons''' => |>*.
    rewrite stateful_local_protocol_fst_rcons''' => |>*. rewrite -H => |>*. qed.

  lemma stateful_consistent_views_outputs_left' x i j vi vj :
    (stateful_consistent_views_outputs' x i j vi vj).`1.`1 =
    (stateful_local_protocol' i x (init_local_state i x vi.`1 vi.`2.`2) vi.`2.`1).`1.
    rewrite /stateful_consistent_views_outputs' /stateful_consistent_views_outputs'' /stateful_local_protocol' => |>*. rewrite (stateful_consistent_views_outputs_left''' (rounds x)) => |>*. qed.

  lemma stateful_consistent_views_outputs_right' x i j vi vj :
    (stateful_consistent_views_outputs' x i j vi vj).`1.`2 =
    (stateful_local_protocol' j x (init_local_state j x vj.`1 vj.`2.`2) vj.`2.`1).`1.
    rewrite /stateful_consistent_views_outputs' /stateful_consistent_views_outputs'' /stateful_local_protocol' => |>*. rewrite (stateful_consistent_views_outputs_right''' (rounds x)) => |>*. qed.

  lemma equiv_stateful_consistent_views_outputs''' x i j (vi vj:view) :
    ISet.mem i partyset => ISet.mem j partyset => 
    valid_view x vi => valid_view x vj =>
    (stateful_consistent_views_outputs''' x i j vi.`2.`1 vj.`2.`1
      (init_local_state i x vi.`1 vi.`2.`2, init_local_state j x vj.`1 vj.`2.`2)
      (iseq (rounds x))).`2 =
    ( (P.get vi.`2.`1 j) = (P.get (stateful_local_protocol'' j x (init_local_state j x vj.`1 vj.`2.`2) vj.`2.`1 (rounds x) (rounds x)).`2 i) /\
      (P.get vj.`2.`1 i) = (P.get (stateful_local_protocol'' i x (init_local_state i x vi.`1 vi.`2.`2) vi.`2.`1 (rounds x) (rounds x)).`2 j) ).
    rewrite !/valid_view => |>H1 H2 H3 H4. 
    pose vi2 := ST.prmsgs_up_to (rounds x) vi.`2.`1.
    pose vj2 := ST.prmsgs_up_to (rounds x) vj.`2.`1.
    have : vi.`2.`1 = vi2. rewrite /vi2 (ST.prmsgs_up_to_id (rounds x) (rounds x)) => |>*. rewrite rounds_ge0 => |>*. move => H5.
    have : vj.`2.`1 = vj2. rewrite /vj2 (ST.prmsgs_up_to_id (rounds x) (rounds x)) => |>*. rewrite rounds_ge0 => |>*. move => H6.
    rewrite !H5 !H6 /vi2 /vj2. pose rx := rounds x. rewrite /rx.
    rewrite (_: (stateful_local_protocol'' i x (init_local_state i x (fst3 vi) (thr3 vi)) (prmsgs_up_to (rounds x) (snd3 vi)) (rounds x) (rounds x)) = (stateful_local_protocol'' i x (init_local_state i x (fst3 vi) (thr3 vi)) (prmsgs_up_to (rounds x) (snd3 vi)) rx (rounds x)) ). progress. 
    rewrite (_: (stateful_local_protocol'' j x (init_local_state j x (fst3 vj) (thr3 vj)) (prmsgs_up_to (rounds x) (snd3 vj)) (rounds x) (rounds x)) = (stateful_local_protocol'' j x (init_local_state j x (fst3 vj) (thr3 vj)) (prmsgs_up_to (rounds x) (snd3 vj)) rx (rounds x)) ). progress. 
    have : 0 <= rounds x <= rx. rewrite rounds_ge0 /rx => |>. elim/natind:(rounds x) => |> n N1 N2 N3. 
    (*0*)
    rewrite (_:n=0) => |>*. smt(). rewrite !(ST.prmsgs_up_to_0 (rounds x)) /stateful_consistent_views_outputs''' /stateful_local_protocol'' /stateful_local_protocol''' /get_view_in_msgs => |>.
    move => k Hk. move :H3. rewrite /prdom P.allP => |>H7. have : rdom (rounds x) (rounds x) ((P.get (snd3 vi) k)). rewrite H7 => |>. move :Hk. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. 
    move => k Hk. move :H4. rewrite /prdom P.allP => |>H8. have : rdom (rounds x) (rounds x) ((P.get (snd3 vj) k)). rewrite H8 => |>. move :Hk. rewrite /ISet.mem iset_in_def => |>. rewrite /rdom => |>. 
    rewrite !iseq_nil => |>*. rewrite eq_logical => |>*. progress.
    have : n=0. smt(). progress. rewrite !ST.get_prempty H1 H2 => |>*. rewrite !ST.get_prempty H1 H2 => |>*. 
    (*succ*)
    move => N4.
    have : 0 <= i < P.size. move :H1. rewrite /ISet.mem iset_in_def => />. move => Hi. 
    have : 0 <= j < P.size. move :H2. rewrite /ISet.mem iset_in_def => />. move => Hj. 
    have : forall (i0 : int), mem i0 partyset => size (P.get (prmsgs_up_to (n + 1) (snd3 vi)) i0) = rx. move => k Hk. rewrite size_prmsgs_up_to => />. have : rdom (rounds x) (rounds x) (P.get (snd3 vi) k). rewrite prdom_rdom_get => />. rewrite /rdom => />. move => Svi.
    have : forall (i0 : int), mem i0 partyset => size (P.get (prmsgs_up_to (n + 1) (snd3 vj)) i0) = rx. move => k Hk. rewrite size_prmsgs_up_to => />. have : rdom (rounds x) (rounds x) (P.get (snd3 vj) k). rewrite prdom_rdom_get => />. rewrite /rdom => />. move => Svj.
    have : forall (i0 : int), mem i0 partyset => size (P.get (prmsgs_up_to n (snd3 vi)) i0) = rx. move => i0 Hi0. have : size (P.get (prmsgs_up_to (n + 1) (snd3 vi)) i0) = rx. rewrite Svi => />. rewrite !size_prmsgs_up_to => />. move => Svi1.
    have : forall (i0 : int), mem i0 partyset => size (P.get (prmsgs_up_to n (snd3 vj)) i0) = rx. move => i0 Hi0. have : size (P.get (prmsgs_up_to (n + 1) (snd3 vj)) i0) = rx. rewrite Svj => />. rewrite !size_prmsgs_up_to => />. move => Svj1.
    have : forall (i0 : int), mem i0 partyset => size (P.get (snd3 vi) i0) = rx. move => i0 Hi00. have : size (P.get (prmsgs_up_to (n + 1) (snd3 vi)) i0) = rx. rewrite Svi => />. rewrite size_prmsgs_up_to => />. move => Svi0.
    have : forall (i0 : int), mem i0 partyset => size (P.get (snd3 vj) i0) = rx. move => i0 Hi0. have : size (P.get (prmsgs_up_to (n + 1) (snd3 vj)) i0) = rx. rewrite Svj => />. rewrite size_prmsgs_up_to => />. move => Svj0.
    rewrite !stateful_local_protocol_snd_succ'' => |>*. rewrite !iseq_succ => |>*. rewrite stateful_consistent_views_outputs_rcons''' => |>*. rewrite !ST.get_prset H1 H2 => |>*. rewrite (stateful_consistent_views_outputs_up_to_iseq''' rx n n) => |>. smt(). rewrite !prmsgs_up_to_lt => |>*. smt(). smt(). rewrite N2 => |>*. smt(). clear N2.    
    rewrite eq_logical => |>. split.
    (*forward*)
    move => K1 K2 K3. move :K3. rewrite /stateful_consistent_views_outputs_round => />. rewrite !eq_msgP => />. rewrite (stateful_consistent_views_outputs_right''' rx) => />. rewrite !get_prget !H1 !H2 => />. rewrite (stateful_consistent_views_outputs_left''' rx) => />S1 S2.
    rewrite !Array.tP => |>. rewrite size_prmsgs_up_to => |>. rewrite Array.size_set => |>. rewrite size_get_stateful_local_protocol_snd'' => |>. rewrite prdom_stateful_local_protocol_snd'' => |>. smt(). split. rewrite Svi0 => />. 
    move => r Hr1 Hr2. case (r=n) => />. rewrite Array.get_set_eqE => |>. rewrite size_get_stateful_local_protocol_snd'' => |>. rewrite prdom_stateful_local_protocol_snd'' => |>. smt(). rewrite -S2 => />. congr. congr. rewrite -stateful_local_protocol_up_to_iseq'' => />. smt(). rewrite (stateful_local_protocol_up_to_iseq'' j x _ _ n n) => />. smt(). 
    move => N. rewrite get_set_neqE => />. rewrite prmsgs_up_to_nesucc => />. rewrite K1 => />. congr. congr. rewrite -!stateful_local_protocol_up_to_iseq'' => />. smt(). smt(). 
    rewrite size_prmsgs_up_to => />. rewrite size_set => />. rewrite size_get_stateful_local_protocol_snd'' => />. rewrite prdom_stateful_local_protocol_snd'' => />. smt(). rewrite Svj0 => />. 
    move => r Hr1 Hr2. case (r=n) => />. rewrite Array.get_set_eqE => |>. rewrite size_get_stateful_local_protocol_snd'' => |>. rewrite prdom_stateful_local_protocol_snd'' => |>. smt(). rewrite -S1 => />. congr. congr. rewrite -stateful_local_protocol_up_to_iseq'' => />. smt(). rewrite -(stateful_local_protocol_up_to_iseq''' i x _ _ n n) => />. smt(). 
    move => N. rewrite get_set_neqE => />. rewrite prmsgs_up_to_nesucc => />. rewrite K2 => />. congr. congr. rewrite -!stateful_local_protocol_up_to_iseq'' => />. smt(). smt(). 
    (*backward*)
    rewrite !tP => |>. rewrite !size_prmsgs_up_to => />. rewrite !size_set => />. rewrite !size_get_stateful_local_protocol_snd'' => />. rewrite !prdom_stateful_local_protocol_snd'' => />. smt(). rewrite !prdom_stateful_local_protocol_snd'' => />. smt(). rewrite !prdom_stateful_local_protocol_snd'' => />. smt(). rewrite !prdom_stateful_local_protocol_snd'' => />. smt(). rewrite Svi0 => />. rewrite Svj0 => />. move => S1 S2. rewrite !eq_msgP => />. rewrite !get_prget !H1 !H2 => />. split. split.
    move => k Hk1 Hk2. case (k=n) => |>. rewrite get_prmsgs_up_to_out => |>*. rewrite get_stateful_local_protocol_out'' => |>*. move => K. rewrite -prmsgs_up_to_nesucc. smt(). rewrite S1 => |>*. rewrite get_set_neqE => |>*. rewrite /stateful_local_protocol'' => |>*. rewrite (stateful_local_protocol_up_to_iseq''' _ _ _ _ n n) => |>*. smt(). rewrite prmsgs_up_to_lt => |>*. smt(). 
    move => k Hk1 Hk2. case (k=n) => |>. rewrite get_prmsgs_up_to_out => |>*. rewrite get_stateful_local_protocol_out'' => |>*. move => K. rewrite -prmsgs_up_to_nesucc. smt(). rewrite S2 => |>*. rewrite get_set_neqE => |>*. rewrite /stateful_local_protocol'' => |>*. rewrite (stateful_local_protocol_up_to_iseq''' _ _ _ _ n n) => |>*. smt(). rewrite prmsgs_up_to_lt => |>*. smt(). 
    rewrite S1 => />. smt(). rewrite S2 => />. smt(). rewrite get_set_eqE => |>*. rewrite size_get_stateful_local_protocol_snd'' => />. rewrite prdom_stateful_local_protocol_snd'' => />. smt(). smt(). rewrite (stateful_consistent_views_outputs_left''' rx) /stateful_local_protocol'' => |>*. rewrite (stateful_local_protocol_up_to_iseq''' _ _ _ (prmsgs_up_to (n + 1) vi.`2.`1) n n) => |>*. smt(). rewrite prmsgs_up_to_lt => |>*. smt(). rewrite get_set_eqE => |>*. rewrite size_get_stateful_local_protocol_snd'' => />. rewrite prdom_stateful_local_protocol_snd'' => />. smt(). smt(). rewrite (stateful_consistent_views_outputs_right''' rx) /stateful_local_protocol'' => |>*. rewrite (stateful_local_protocol_up_to_iseq''' _ _ _ (prmsgs_up_to (n + 1) vj.`2.`1) n n) => |>*. smt(). rewrite prmsgs_up_to_lt => |>*. smt(). qed.

  lemma equiv_stateful_consistent_views_outputs' x i j vi vj :
    ISet.mem i partyset => ISet.mem j partyset => 
    ((stateful_consistent_views_outputs' x i j vi vj).`2
    /\ consistent_inputs x i j vi.`1 vj.`1
    /\ consistent_rands x i j vi.`2.`2 vj.`2.`2
    /\ valid_view x vi /\ valid_view x vj)
      = (pairwise_consistent_views x i j vi vj).
    rewrite /stateful_consistent_views_outputs' /stateful_consistent_views_outputs'' /pairwise_consistent_views /consistent_views /get_view_out_msgs /stateful_local_protocol => |>H1 H2. 
    rewrite -!equiv_stateful_local_protocol' => |>*. rewrite /stateful_local_protocol' !/valid_view /rounds => |>*. rewrite /get_view_in_msgs => |>*. 
    rewrite eq_logical => |>*. split. move => H3 H4 H5 H6 H7.
    move :H3. rewrite equiv_stateful_consistent_views_outputs''' => |>. rewrite /valid_view => |>. rewrite /valid_view => |>. move => H8 H9. rewrite !eq_rmsgsP => |>. 
    rewrite !eq_rmsgsP => |> K1 K2 K3 K4 K5 K6. 
    rewrite equiv_stateful_consistent_views_outputs''' => |>*. qed.

  lemma equiv_stateful_consistent_views_outputs x i j vi vj :
    ISet.mem i partyset => ISet.mem j partyset => 
    (stateful_consistent_views_outputs x i j vi vj
    /\ consistent_inputs x i j vi.`1 vj.`1
    /\ consistent_rands x i j vi.`2.`2 vj.`2.`2
    /\ valid_view x vi /\ valid_view x vj)
      = (pairwise_consistent_views x i j vi vj
      /\ stateful_consistent_outputs x i j
        (stateful_local_protocol i x vi).`2
        (stateful_local_protocol j x vj).`2).
    rewrite /stateful_consistent_views_outputs => |>H H0. 
    rewrite (_: (((stateful_consistent_views_outputs' x i j vi vj).`2 /\
  stateful_consistent_outputs x i j
    (stateful_local_protocol_end i x (stateful_consistent_views_outputs' x i j vi vj).`1.`1)
    (stateful_local_protocol_end j x (stateful_consistent_views_outputs' x i j vi vj).`1.`2)) /\
 consistent_inputs x i j vi.`1 vj.`1 /\ consistent_rands x i j vi.`2.`2 vj.`2.`2 /\ valid_view x vi /\ valid_view x vj) = (((stateful_consistent_views_outputs' x i j vi vj).`2
    /\ consistent_inputs x i j vi.`1 vj.`1
    /\ consistent_rands x i j vi.`2.`2 vj.`2.`2
    /\ valid_view x vi /\ valid_view x vj) /\ stateful_consistent_outputs x i j
    (stateful_local_protocol_end i x (stateful_consistent_views_outputs' x i j vi vj).`1.`1)
    (stateful_local_protocol_end j x (stateful_consistent_views_outputs' x i j vi vj).`1.`2)) ). smt(). rewrite equiv_stateful_consistent_views_outputs' => |>*. rewrite /stateful_local_protocol => |>*. rewrite eq_logical => |>*. progress. move :H2. rewrite stateful_consistent_views_outputs_left' stateful_consistent_views_outputs_right' => |>*. rewrite stateful_consistent_views_outputs_left' stateful_consistent_views_outputs_right' => |>*. qed.

end StatefulProtocol.

