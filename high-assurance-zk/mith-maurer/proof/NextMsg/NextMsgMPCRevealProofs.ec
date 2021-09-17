require import AllCore Int List FSet SmtMap Distr.
require import Aux AuxList AuxFSet AuxSmtMap.
require import NextMsgArray NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgWeak NextMsgMPC NextMsgMPCReveal NextMsgWeakProofs NextMsgMPCProofs.

require import NextMsgIMap NextMsgISet NextMsgArray.

theory WeakRevealProofs.

  clone import WeakProofs as WP.

  clone import WeakReveal as WR with
    theory W = WP.W
    proof valid_send_messages, valid_stateful_local_protocol_round, ST.rounds_ge0, to_from_local_messages, from_to_local_messages, ppswap_from_messages, valid_pmsgs_from, get_local_messages_eqP, ST.eq_msgP.
    realize valid_send_messages.
    rewrite /valid_messages /send_messages => />outs p r. rewrite !ST.P.allP => />H i Hi1 Hi2.
    rewrite /weak_rounds => />. case (r < M.ST.rounds (pub_input_conv p)) => />H1.
    rewrite (_:(ST.P.get (WP.W.P.send_messages outs) i) = M.ST.P.get (M.send_messages outs) i). progress. 
    have : M.valid_messages (pub_input_conv p) r (M.send_messages outs). rewrite M.valid_send_messages => />. rewrite /valid_messages WP.W.P.ST.P.allP => />j Hj1 Hj2. have : valid_local_messages p r (ST.P.get outs j). rewrite H => />. rewrite /valid_local_messages /weak_rounds H1 => />.
    rewrite /valid_messages WP.W.P.ST.P.allP => />H2. have : WP.W.P.valid_local_messages (pub_input_conv p) r (WP.W.P.ST.P.get (M.send_messages outs) i). rewrite H2 => />. rewrite /valid_local_messages /send_messages => />. 
    have : valid_local_messages p r (ST.P.get outs i). rewrite H => />. rewrite /valid_local_messages /weak_rounds H1 => />H2. 
    rewrite -final_valid_local_send_messages //. qed.
    realize valid_stateful_local_protocol_round.
    rewrite /valid_local_messages /stateful_local_protocol_round /mpc_local_protocol_round => />i r x st. case (r < weak_rounds x) => />H. 
    rewrite (_:WP.W.P.valid_local_messages=M.valid_local_messages). progress. rewrite M.valid_stateful_local_protocol_round.
    rewrite valid_reveal_local_start => />. qed.
    realize ST.rounds_ge0.
    rewrite /rounds => />p. smt(W.P.ST.rounds_ge0). qed.
    realize to_from_local_messages.
    rewrite /valid_local_messages /to_local_messages /from_local_messages => />p r xs. case (r < weak_rounds p) => />H.
    move => H1. rewrite (_:WP.W.P.to_local_messages=M.to_local_messages). progress. rewrite (_:WP.W.P.from_local_messages=M.from_local_messages). progress. rewrite (M.to_from_local_messages (pub_input_conv p) r) => |>.
    move => H1. smt(final_to_from_local_messages). qed.
    realize from_to_local_messages.
    rewrite /valid_pmsgs /from_local_messages /to_local_messages => />p r xs. rewrite ST.P.allP => />H. 
    rewrite ST.pmap_eqP => />x Hx. case (r < weak_rounds p) => />H1.
    rewrite (_:WP.W.P.from_local_messages=M.from_local_messages). progress. rewrite (_:WP.W.P.to_local_messages=M.to_local_messages). progress. rewrite (M.from_to_local_messages (pub_input_conv p) r) => />. rewrite /valid_pmsgs WP.W.P.ST.P.allP => />i Hi1 Hi2. have : valid_msg p r (ST.P.get xs i). rewrite H => />. rewrite /valid_msg => />. rewrite H1 => />. 
    have : valid_msg p r (ST.P.get xs x). rewrite H => />. move :Hx. rewrite /ISet.mem iset_in_def => />. rewrite /valid_msg => />. rewrite H1 => />. move => H2. rewrite (_:WP.W.P.from_local_messages=M.from_local_messages). progress. rewrite (_:WP.W.P.to_local_messages=M.to_local_messages). progress. rewrite (final_from_to_local_messages p) => />. move => i Hi1 Hi2. have : valid_msg p r (ST.P.get xs i). rewrite H => />. rewrite /valid_msg H1 => />. qed.
    realize ppswap_from_messages.
    rewrite /valid_messages /from_messages /send_messasges => />p r outs. rewrite ST.P.allP => />H. rewrite ST.ppmap_eqP => />x y Hx Hy. rewrite /ppswap ST.get_pmap => />. rewrite ST.get_ppinit Hx => />. rewrite ST.get_pinit Hy => />. rewrite ST.get_pmap => />. have : valid_local_messages p r (ST.P.get outs y). rewrite H => />. move :Hy. rewrite /ISet.mem iset_in_def => />. rewrite /valid_local_messages => />. case (r < weak_rounds p) => />H0. have : M.ST.ppswap (M.from_messages outs) = M.from_messages (M.send_messages outs). rewrite (M.ppswap_from_messages (pub_input_conv p) r) => />. rewrite /valid_messages WP.W.P.ST.P.allP => />i Hi1 Hi2. have : valid_local_messages p r (ST.P.get outs i). rewrite H => />. rewrite /valid_local_messages => />. rewrite H0 => />. rewrite M.ST.ppmap_eqP => />H1 H2.
    have : M.ST.P.get (M.ST.P.get (M.ST.ppswap (M.from_messages outs)) x) y = M.ST.P.get (M.ST.P.get (M.from_messages (M.send_messages outs)) x) y. rewrite H1 => />. rewrite /ppswap M.ST.get_ppinit Hx /from_messages => />. rewrite M.ST.get_pinit Hy => />. rewrite !WP.W.P.ST.get_pmap => />. rewrite M.ST.get_pmap => />. 
    move => H1. have : M.ST.ppswap (from_messages outs) = M.from_messages (M.send_messages outs). rewrite (final_ppswap_from_messages p) => />i Hi1 Hi2. have : valid_local_messages p r (ST.P.get outs i). rewrite H => />. rewrite /valid_local_messages => />. rewrite H0 => />. rewrite M.ST.ppmap_eqP => />H2. 
    have : M.ST.P.get (M.ST.P.get (M.ST.ppswap (from_messages outs)) x) y = M.ST.P.get (M.ST.P.get (M.from_messages (M.send_messages outs)) x) y. rewrite H2 => />. rewrite /from_messages /ppswap M.ST.get_ppinit Hx => />. rewrite M.ST.get_pinit Hy => />. rewrite M.ST.get_pmap => />. rewrite WP.W.P.ST.get_pmap => />. qed.
    realize valid_pmsgs_from.
    rewrite /valid_local_messages /valid_pmsgs => />p r xs. case (r < weak_rounds p) => />H0. rewrite ST.P.allP => />H i Hi1 Hi2 H1. have : M.valid_pmsgs (pub_input_conv p) r (M.from_local_messages xs). rewrite M.valid_pmsgs_from => />. rewrite /valid_pmsgs WP.W.P.ST.P.allP => />H2. have : WP.W.P.valid_msg (pub_input_conv p) r (WP.W.P.ST.P.get (M.from_local_messages xs) i). rewrite H2 => />. rewrite /valid_msg /from_local_messages /get => />. 
    rewrite ST.P.allP => />H i Hi1 Hi2 H1. rewrite /from_local_messages => />. rewrite final_valid_pmsgs_from => />. qed.
    realize get_local_messages_eqP.
    smt(M.get_local_messages_eqP). qed.
    realize ST.eq_msgP. rewrite /eq_msg => m1 m2. rewrite WP.W.P.ST.eq_msgP => //. qed.

end WeakRevealProofs.

theory MPCRevealProofs.

  clone import WeakRevealProofs as WRP.

  clone import MPCReveal as MR with
    theory WR = WRP.WR.

  axiom valid_inputs_start x ws :
    WR.valid_inputs x ws => WR.W.P.valid_inputs (WR.pub_input_conv x) ws.

  axiom valid_execution x ws cs :
    WR.valid_inputs x ws /\ WR.valid_rands x cs =>
      valid_outputs x (WR.W.P.stateful_protocol (WR.pub_input_conv x) ws cs).`2.

   axiom reveal_correctness i x ss :
    i \in WR.W.P.ST.partyset /\ valid_outputs x ss =>
      reveal_functionality x (WP.W.unshare_output ss) = WR.reveal_local_end x (WRP.WP.W.P.ST.P.get (WR.W.P.send_messages (reveal_start x ss)) i).

  axiom reconstruct_final_messages i x s (ss:WR.W.local_outputs) :
    corrupted_set i /\ valid_outputs x ss => 
    s = reveal_functionality x (WP.W.unshare_output ss) => 
      reconstruct_final i x (corrupted i ss) s = reveal_start x ss.

  lemma valid_rands_conv x cs :
    P.valid_rands x cs = WP.W.P.valid_rands (WR.pub_input_conv x) cs.
    rewrite /P.valid_rands => />*. qed.

  lemma pprset_wst_st (xs: 'a P.ST.pprmap) i x :
    WRP.WR.ST.pprset xs i x = WP.W.P.ST.pprset xs i x. progress. qed.

  lemma map_wst_wpst (f:'a->'b) (xs: 'a WP.W.P.ST.P.arrayN) :
    WRP.WR.ST.P.map f xs = WP.W.P.ST.P.map f xs. progress. qed.

  lemma get_wpst_wrst (xs:'a WP.W.P.ST.P.arrayN) i :
    WP.W.P.ST.P.get xs i = WRP.WR.ST.P.get xs i. progress. qed.

  lemma reveal_stateful_protocol_prefix''' x ys cs ins n :
    n <= (WP.W.P.ST.rounds (WRP.WR.pub_input_conv x)) =>
    WRP.WR.stateful_protocol''' x ins (WRP.WR.init_state x ys cs) (iseq n) =
    prod idfun (WP.W.P.ST.P.map L) (WP.W.P.stateful_protocol''' (WRP.WR.pub_input_conv x) ins (WP.W.P.init_state (WRP.WR.pub_input_conv x) ys cs) (iseq n)).
    elim/natind:n => />n N. move => N0. rewrite !iseq_nil /prod /idfun /stateful_protocol''' => />. rewrite /init_state => />. rewrite WP.W.P.ST.pmap_eqP => />y Hy. rewrite !WP.W.P.ST.get_pimap => />.
    rewrite /prod /idfun => />N0 N1. rewrite !iseq_succ => />. rewrite !WP.W.P.stateful_protocol_fst_rcons''' => />. rewrite eq2 => />. rewrite WRP.WR.stateful_protocol_fst_rcons''' => />. rewrite WRP.WR.stateful_protocol_snd_rcons''' => />. rewrite !N0 => />. smt(). rewrite pprset_wst_st => />. split.
    congr. rewrite /from_messages /from_local_messages /send_messages => />. rewrite map_wst_wpst => />. congr. congr. rewrite /stateful_protocol_round => />. rewrite WRP.WR.ST.pmap_eqP => />z Hz. rewrite !WRP.WR.ST.get_pimap => />. rewrite /stateful_local_protocol_round /mpc_local_protocol_round => />. have : n < WRP.WR.weak_rounds x. smt(). move => weak. rewrite weak => />. rewrite WP.W.P.stateful_protocol_snd_rcons''' => />. rewrite /update_state => />. rewrite WP.W.P.ST.pmap_eqP => />w Hw. rewrite !WP.W.P.ST.get_pimap => />. rewrite !WP.W.P.ST.get_pzip !Hw => />. rewrite !WP.W.P.ST.get_pmap => />. rewrite !get_wpst_wrst (WRP.WR.get_send_messages x n) => />.
    rewrite WRP.WR.valid_stateful_protocol_round => />.
    rewrite /update_local_state /mpc_update_local_state => />. have : n < WRP.WR.weak_rounds x. smt(). move => weak. rewrite weak => />. rewrite /update_local_state => />. congr. rewrite /get (WP.W.P.get_send_messages (WR.pub_input_conv x) n) => />.
    rewrite WP.W.P.valid_stateful_protocol_round => />. 
    rewrite /to_local_messages => />. congr. rewrite WP.W.P.ST.pmap_eqP => />z Hz. rewrite !WP.W.P.ST.get_pmap => />. congr. rewrite /from_local_messages => />. congr. congr. rewrite /stateful_protocol_round => />. rewrite WP.W.P.ST.pmap_eqP => />k Hk. rewrite !WP.W.P.ST.get_pimap => />. rewrite /stateful_local_protocol_round /mpc_local_protocol_round => />. rewrite weak => />. qed.
    
  lemma reveal_stateful_protocol_fst x ys cs :
    P.valid_inputs x ys /\ P.valid_rands x cs =>
      (P.stateful_protocol x ys cs).`1 = WR.M.ST.add_trace_in_msgs
        (WP.W.P.ST.rounds (WR.pub_input_conv x))
        (WP.W.P.from_messages (WR.M.send_messages ( reveal_start x (WR.M.stateful_protocol_sz   (WP.W.P.ST.rounds (WR.pub_input_conv x) + 1) (WR.pub_input_conv x) ys cs).`2 )))
        (WP.W.P.stateful_protocol_sz (WP.W.P.ST.rounds (WR.pub_input_conv x) + 1) (WR.pub_input_conv x) ys cs).`1.
    rewrite /P.stateful_protocol => />H H0. rewrite P.ST.pmap_eqP => />z Hz. rewrite P.ST.get_pinit /add_trace_in_msgs Hz /add_view_in_msgs => />*. rewrite !WP.W.P.ST.get_pzip !Hz => />*. 
    rewrite !/stateful_protocol /stateful_protocol_sz => />*. rewrite !P.ST.get_pzip3 !Hz => />*. rewrite WP.W.P.ST.get_pzip3 Hz => />. 
    rewrite /stateful_protocol' /stateful_protocol_sz' !/stateful_protocol'' /rounds iseq_succ => />*. rewrite WP.W.P.ST.rounds_ge0 => />*. rewrite WRP.WR.stateful_protocol_fst_rcons''' => />. rewrite WP.W.P.ST.rounds_ge0 => />. rewrite P.ST.get_pprset Hz => />*. rewrite /prset /merge. rewrite WP.W.P.ST.pmap_eqP => />. move => w Hw. rewrite !WP.W.P.ST.get_pinit !Hz !Hw => />. congr.
    congr. rewrite /get => />. congr. rewrite (_:WR.pub_input_conv=WRP.WR.pub_input_conv). progress. rewrite reveal_stateful_protocol_prefix''' => />.
    progress. rewrite reveal_stateful_protocol_prefix''' => />. rewrite /from_messages /get => />. congr. rewrite WP.W.P.ST.get_pmap /from_local_messages /send_messages => />. congr. congr. 
congr. rewrite /stateful_protocol_round /stateful_local_protocol_round /reveal_start /mpc_local_protocol_round /stateful_protocol_end => />. have : ! WP.W.P.ST.rounds (WRP.WR.pub_input_conv x) < WRP.WR.weak_rounds x. rewrite /weak_rounds /rounds => />. move => neg. rewrite neg => />. rewrite WRP.WR.ST.pmap_eqP => />y Hy. rewrite !WRP.WR.ST.get_pimap /reveal_local_start /stateful_local_protocol_end /pub_input_conv => />. congr. congr. rewrite /prod => />. rewrite WRP.WR.ST.get_pmap => />. qed.
    
  lemma reveal_stateful_protocol_fst_fst x ys cs i :
    P.valid_inputs x ys /\ P.valid_rands x cs /\ i \in WR.M.ST.partyset =>
      ((WR.M.ST.P.get ((WR.M.stateful_protocol (WR.pub_input_conv x) ys cs)).`1 i)).`1 = ((WR.M.ST.P.get ((P.stateful_protocol x ys cs)).`1 i)).`1.
    progress. rewrite reveal_stateful_protocol_fst => />*. rewrite /add_trace_in_msgs => />*. rewrite WR.M.ST.get_pmap => />*. rewrite /add_view_in_msgs WR.M.ST.get_pzip/ISet.mem H1 => />*. rewrite /stateful_protocol /stateful_protocol_sz /get => />. rewrite !WP.W.P.ST.get_pzip3 /ISet.mem !H1 => />. qed.

  lemma p_wp_get (xs:'a P.ST.P.arrayN) i :
    P.ST.P.get xs i = WP.W.P.ST.P.get xs i. progress. qed.
  lemma p_wr_get (xs:'a P.ST.P.arrayN) i :
    P.ST.P.get xs i = WRP.WR.ST.P.get xs i. progress. qed.

  lemma reveal_stateful_protocol_snd (x:WR.pub_input) ys cs :
    P.valid_inputs x ys /\ P.valid_rands x cs => 
      (P.stateful_protocol x ys cs).`2 = P.ST.pinit (fun i => reveal_functionality x (WR.W.unshare_output (WR.M.stateful_protocol_sz (WP.W.P.ST.rounds (WRP.WR.pub_input_conv x) + 1) (WR.pub_input_conv x) ys cs).`2)).
    move => H. have : valid_outputs x (WR.W.P.stateful_protocol (WR.pub_input_conv x) ys cs).`2. rewrite valid_execution => |>. move :H. rewrite /valid_inputs /valid_rands => />. move => H0.
    rewrite /stateful_protocol => />. rewrite P.ST.pmap_eqP => />n Hn. rewrite P.ST.get_pinit Hn => />*. rewrite P.ST.get_pinit Hn => />*. rewrite /stateful_local_protocol_end /mpc_local_protocol_end => />*. rewrite /stateful_protocol' /stateful_protocol'' /rounds iseq_succ => />*. rewrite WP.W.P.ST.rounds_ge0 => />*. 
    rewrite WRP.WR.stateful_protocol_snd_rcons''' => />. rewrite WP.W.P.ST.rounds_ge0 => />. 
    rewrite /update_state => />*. rewrite  WP.W.P.ST.get_pimap => />*. rewrite WP.W.P.ST.get_pzip Hn => />*. rewrite /update_local_state /mpc_update_local_state => />*. have : ! WP.W.P.ST.rounds (WRP.WR.pub_input_conv x) < WRP.WR.weak_rounds x. smt(). move => neg. rewrite neg => />*. rewrite (reveal_correctness n) => />. move :H0. rewrite /stateful_protocol /stateful_protocol_sz => />. rewrite /stateful_protocol' /stateful_protocol_sz' /stateful_protocol'' => />. rewrite (WP.W.P.stateful_protocol_snd_iseq''' _ (WP.W.P.ST.pprempty (WP.W.P.ST.rounds (WRP.WR.pub_input_conv x) + 1) witness) (WP.W.P.ST.pprempty (WP.W.P.ST.rounds (WRP.WR.pub_input_conv x)) witness) _ _) => />.  move => i j r Hi Hj Hr1 Hr2. rewrite !WP.W.P.ST.get_pprempty !Hi => />. rewrite !WP.W.P.ST.get_prempty !Hj => />. rewrite !Array.get_init => />. 
    rewrite /reveal_local_end. congr. congr. rewrite /send_messages. congr. rewrite /stateful_protocol_round /stateful_local_protocol_round /mpc_local_protocol_round /reveal_start => />*. rewrite P.ST.pmap_eqP => />z Hz. rewrite P.ST.get_pimap => />*. rewrite P.ST.get_pmap => />*. rewrite neg => />*. rewrite /reveal_local_start. congr. rewrite /stateful_protocol_end => />*. rewrite /stateful_protocol /stateful_protocol' => />*. rewrite /stateful_protocol_sz /stateful_protocol_sz' /stateful_protocol'' /stateful_protocol_end => />. rewrite P.ST.get_pimap => />*. rewrite /stateful_local_protocol_end /pub_input_conv => />. congr. rewrite reveal_stateful_protocol_prefix''' /prod /idfun => />. rewrite !P.ST.get_pmap => />. qed.


  lemma prset_wrst_wpst (xs: 'a P.ST.prmap) i x :
    WR.W.P.ST.prset xs i x = WP.W.P.ST.prset xs i x. progress. qed.

  (*lemma get_mr_w (xs : 'a W.P.ST.P.t) i :
    MR.P.T.P.get xs i = W.P.T.P.get xs i. progress. qed.*)

  lemma get_st_wrst (xs: 'a P.ST.P.arrayN) i :
    P.ST.P.get xs i = WR.M.ST.P.get xs i. progress. qed.

  lemma fdom_simulator_out is x ws cs :
    fdom (WR.W.simulator_out is x ws cs).`1 = is.
    rewrite (_:WR.W.simulator_out is x ws cs = WP.W.simulator_out is x ws cs). progress. 
    rewrite (_:fdom (WP.W.simulator_out is x ws cs).`1 = IMap.dom (WP.W.simulator_out is x ws cs).`1). progress. 
    rewrite /IMap.dom WP.dom_simulator_out => />. qed.

  clone include MPCProofs with
    theory M = MR
    proof *.
    realize mpc_correctness.
    rewrite /functionality /mpc_functionality => />x ys cs H H0. rewrite M.P.ST.pmap_eqP => />y H1. rewrite M.P.ST.get_pinit H1 => />*. rewrite (_:WR.W.functionality=WP.W.functionality). progress. rewrite (_:WR.W.unshare_input=WP.W.unshare_input). progress. rewrite (WP.weak_correctness (WR.pub_input_conv x) ys cs) => />. smt(valid_inputs_start). rewrite (_:M.P.stateful_protocol=P.stateful_protocol). progress. rewrite reveal_stateful_protocol_snd => />. rewrite M.P.ST.get_pinit H1 => />. rewrite /unshare_output => />. rewrite -WP.W.P.equiv_stateful_protocol_snd => />. rewrite WR.M.equiv_stateful_protocol_sz_snd => />. qed.
    realize mpc_privacy.
    proc. wp. sp. simplify.
    (* weak *)
    alias{1} 1 stub = 0. swap{1} 1 1. alias{2} 1 stub = 0. swap{2} 1 1.
    alias{1} 2 sivi = WR.W.simulator_out i (WR.pub_input_conv x) (corrupted i ss) cs.
    alias{2} 2 sv = WR.W.P.stateful_protocol (WR.pub_input_conv x) ss cs.
    alias{2} 3 sivi = corrupted2 i sv.
    transitivity{2}
      { sivi <@ WP.WeakPrivacy.real_out(i,WR.pub_input_conv x,ss); }
      ( ={i,x,ss} /\ P.valid_inputs x{2} ss{2} /\ corrupted_set i{2} /\ si{1} = corrupted i{2} ss{2} /\  y{1} = functionality x{1} ss{1} ==> ={i,sivi,x,ss} /\ (P.valid_inputs x{2} ss{2}) /\ corrupted_set i{2} /\ sivi{1} = WR.W.simulator_out i{1} (WR.pub_input_conv x{1}) (corrupted i{1} ss{1}) cs{1} /\ si{1} = corrupted i{2} ss{2} /\ y{1} = functionality x{1} ss{1} )
      ( ={i,x,ss} /\ (P.valid_inputs x{2} ss{2}) /\ card i{2} = corrupted_t /\ i{2} \subset P.ST.partyset ==> ={ss,i,sivi,x} /\ sv{2} = WR.W.P.stateful_protocol (WR.pub_input_conv x{2}) ss{2} cs{2} /\ sivi{1} = corrupted2 i{2} sv{2} /\ P.valid_inputs x{2} ss{2} /\ P.valid_rands x{2} cs{2} /\ corrupted_set i{2} ).
      progress. exists (i{2}) (ss{2}) (x{2}) => />*. 
      progress. move :H1. rewrite /simulator_out /(><) => />H5 H6. rewrite /simulator /mpc_simulator => />*. rewrite -fmap_eqIn /corrupted => />*. rewrite fdom_map fdom_ofset => />*. split. smt(WP.dom_simulator_out). move => j. rewrite fdom_simulator_out => Hj. rewrite ofset_some => />*. rewrite map_some => />*. rewrite -mem_fdom fdom_simulator_out => />*. rewrite !eq2 => />.
      rewrite /simulator_out /IMap.ofset => />. rewrite (_: (ofset ((P.ST.P.get ss{2})) i{2}) = (corrupted i{2} ss{2}) ). progress. rewrite H5 => />. rewrite /corrupted ofset_some. rewrite Hj. rewrite !oget_some => />. rewrite (_: ((P.ST.P.get ((WR.W.P.stateful_protocol (WR.pub_input_conv x{2}) ss{2} cs{2})).`1 j)).`1 = ((P.ST.P.get ((WR.W.P.stateful_protocol (WR.pub_input_conv x{2}) ss{2} cs{2})).`1 j)).`1 ). progress. rewrite (_:WR.W.P.stateful_protocol=WR.M.stateful_protocol). progress. rewrite !get_st_wrst => />. rewrite reveal_stateful_protocol_fst_fst => />. rewrite (in_subset i{2}) => />. move :H4. rewrite /corrupted_set => />. rewrite WP.view_outputs_corrupted => />*. move :H4. rewrite /corrupted_set => />H7 H8. 
      rewrite (_: (WP.W.P.view_outputs (WR.pub_input_conv x{2}) (WR.M.stateful_protocol (WR.pub_input_conv x{2}) ss{2} cs{2}).`1) = (WP.W.P.stateful_protocol (WR.pub_input_conv x{2}) ss{2} cs{2}).`2). rewrite /stateful_protocol /view_outputs => />. rewrite WP.W.P.ST.pmap_eqP => />z Hz. rewrite WP.W.P.ST.get_pimap => />*. rewrite WP.W.P.ST.get_pzip3 Hz => />*. rewrite /view_output /stateful_protocol_end => />*. rewrite WP.W.P.ST.get_pimap => />*. rewrite /local_protocol_end => />*. congr. rewrite /stateful_protocol' => />*. rewrite -WP.W.P.equiv_stateful_protocol'' => />*. rewrite WP.W.P.ST.rounds_ge0 => />*. rewrite /get_state WP.W.P.ST.get_pimap => />*. rewrite !WP.W.P.ST.get_pzip3 !Hz => />*.
    rewrite (reconstruct_final_messages i{2} x{2} (functionality x{2} ss{2}) _) => />. rewrite valid_execution => />*. rewrite /functionality /mpc_functionality => />*. congr. rewrite /functionality => />. rewrite (WP.weak_correctness (WR.pub_input_conv x{2}) ss{2} cs{2}) => />. rewrite (_:(WP.W.P.valid_inputs (WR.pub_input_conv x{2}) ss{2})=(WR.W.P.valid_inputs (WR.pub_input_conv x{2}) ss{2})). progress. rewrite valid_inputs_start => />*. rewrite -WP.W.P.equiv_stateful_protocol_snd => />*.  
      rewrite (_:M.P.stateful_protocol=P.stateful_protocol). progress. rewrite !reveal_stateful_protocol_fst => />*. rewrite /add_trace_in_msgs /add_view_in_msgs => />*. have : ISet.mem j WR.M.ST.partyset. rewrite /ISet.mem. rewrite (in_subset i{2}) => />. move :H4. rewrite /corrupted_set => />. move => Hj'. rewrite !WR.M.ST.get_pmap => />*. rewrite !WR.M.ST.get_pzip Hj' => />*. rewrite /prextset => />*. split. congr. rewrite WP.W.P.equiv_stateful_protocol_sz_fst => />. have : 0 <= WP.W.P.ST.rounds (WR.pub_input_conv x{2}). rewrite WP.W.P.ST.rounds_ge0 => />. smt(). rewrite WR.M.ST.get_pmap => />. progress. rewrite /get /from_messages /send_messages => />. congr. congr. congr. congr. rewrite WR.M.equiv_stateful_protocol_sz_snd => />. rewrite WP.W.P.equiv_stateful_protocol_sz_fst => />. have : 0 <= WP.W.P.ST.rounds (WR.pub_input_conv x{2}). rewrite WP.W.P.ST.rounds_ge0 => />. smt(). rewrite WR.M.ST.get_pmap => />. 
    transitivity{2}
      { sivi <@ WP.WeakPrivacy.ideal_out(i,WR.pub_input_conv x,ss); }
      ( ={i,x,ss} /\ si{1} = corrupted i{2} ss{2} /\ y{1} = functionality x{1} ss{1} ==> ={i,x,sivi,ss} /\ sivi{1} = (WR.W.simulator_out i{1} (WR.pub_input_conv x{1}) ((corrupted i{1} ss{1})) cs{1}) /\ si{1} = corrupted i{2} ss{2} /\ y{1} = functionality x{1} ss{1} )
      ( ={i,x,ss} /\ (P.valid_inputs x{2} ss{2}) /\ corrupted_set i{2} ==> ={i,x,sivi,ss} /\ (P.valid_inputs x{2} ss{2}) /\ corrupted_set i{2} ).
      progress. exists (i{2}) (ss{2}) (x{2}) => />*.
      progress.
      (* left - ideal *)
      inline WP.WeakPrivacy.ideal_out. wp. sp. simplify.
      conseq (_ : _ ==> cs{1}=cs0{2}). auto => />*.
      auto => />*. 
      (* ideal - real *)
      call (WP.weak_privacy_out) => />*. auto => />*. smt(valid_inputs_start).
      (* real - right *)
      inline WP.WeakPrivacy.real_out. wp. sp. simplify. conseq (_ : p{1}=WR.pub_input_conv x{2} /\ ys{1}=ss{2} ==>p{1}=WR.pub_input_conv x{2} /\ cs0{1}=cs{2} /\ cs0{1} \in WP.W.gen_rand p{1}).
      progress. progress. rewrite -WP.W.P.equiv_stateful_protocol => />*. rewrite -WP.W.P.equiv_stateful_protocol => />*. smt(WP.valid_gen_rand). rewrite /ISet.card H0 => />*. rewrite /ISet.subset H1 => />. 
      auto => />*. qed.
    realize gen_rand_ll.
    rewrite /gen_rand => />*. rewrite WP.gen_rand_ll => />*. qed.
    realize valid_gen_rand.
    rewrite /gen_rand => />. progress. rewrite /M.P.valid_rands valid_rands_conv => />*. rewrite WP.valid_gen_rand => />*. qed.
    realize dom_simulator.
    rewrite /simulator /mpc_simulator => />*. rewrite /IMap.dom fdom_map => />*. rewrite fdom_simulator_out => />*. qed.

end MPCRevealProofs.
