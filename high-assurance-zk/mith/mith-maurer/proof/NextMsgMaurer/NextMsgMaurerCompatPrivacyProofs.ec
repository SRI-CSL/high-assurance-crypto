(* general *)
require import AllCore FSet SmtMap List Distr.

(* hugo *)
require import Aux AuxList AuxFSet AuxSmtMap.
require import NextMsgMaurerCompat NextMsgMaurer NextMsgMaurerMPC NextMsgMaurerProofs NextMsgMaurerCompatProofs.
require import NextMsgMaurerProofs NextMsgMPCProofs.
require import NextMsgMaurerCompatProofs.
require import NextMsgMPCReveal.
require import NextMsgMaurerP NextMsgArray NextMsgISet NextMsgIMap.

(* mbb *)
require import Array5 Array9.

(* vitor *)
require import ProtocolPrivacy.

theory MaurerCompatPrivacy.

  clone include Privacy with
    theory P = MaurerProtocol,
    op restricted_inputs c xs = true.
    
  import MaurerProtocolFunctionality.
  import MaurerProtocol.
  import P.
  import F.

  module Rand : Rand_t = {
    proc gen(c:circuit_t, cr:pid_t list, aux : aux_t) : rands_t = {
      var rs;
      rs <$ gen_rand c.`1;
      return rs;
    }
  }.

  module Simulator : Simulator_t = {
    proc simm(c : circuit_t, xs : inputs_t, rs : rands_t, cr : pid_t list, y : outputs_t) : views_t = {
      var vv;
      vv <- simulator cr c xs rs y;
      return vv;
    }
  }.

  module Privacy (D : Distinguisher_t) = {
    proc real1 (c:circuit_t,xs,cr) =
    {
      var rs,vsc,b';
      if (F.valid_inputs c xs /\ valid_corrupted_set cr)
      {
        rs <$ gen_rand c.`1;
        vsc <@ RealEvaluator.eval(c,xs,cr,rs);
        b' <@ D.guess(vsc);
      }
      else { b' <$ {0,1}; }
      return b';
    }
    proc ideal1 (c:circuit_t,xs,cr) =
    {
      var rs,vsc,b';
      if (F.valid_inputs c xs /\ valid_corrupted_set cr)
      {
        rs <$ gen_rand c.`1;
        vsc <@ IdealEvaluator(Simulator).eval(c,xs,cr,rs);
        b' <@ D.guess(vsc);
      }
      else { b' <$ {0,1}; }
      return b';
    }
    proc real2 (c:circuit_t,xs,cr) =
    {
      var vsc;
        vsc <@ MaurerMPCRevealProofs.MPCPrivacy.real(from_corrupted_parties_t cr,c.`1,from_inputs_t xs);
        return to_corrupted_views_t cr vsc;
    }
    proc ideal2 (c:circuit_t,xs,cr) =
    {
      var vsc;
        vsc <@ MaurerMPCRevealProofs.MPCPrivacy.ideal(from_corrupted_parties_t cr,c.`1,from_inputs_t xs);
        return to_corrupted_views_t cr vsc;
    }
  }.

  lemma gen_rand_ll (c : circuit_t) :
    is_lossless (MaurerProtocol.gen_rand c.`1).
    rewrite /MaurerProtocol.gen_rand => />*. rewrite dmap_ll. smt(MaurerMPCRevealProofs.gen_rand_ll). qed.

  lemma valid_gen_rand (c : circuit_t) (rs : rands_t) :
    rs \in MaurerProtocol.gen_rand c.`1 => P.valid_rands c rs.
    rewrite /gen_rand supp_dmap => />a H. have : MaurerMPCReveal.P.valid_rands c.`1 a. smt(MaurerMPCRevealProofs.valid_gen_rand).
    move => H0. have : MaurerProtocol.valid_rands c (MaurerProtocol.to_rands_t a). rewrite MaurerCompatProofs.valid_rands_to => />*. clear H H0. rewrite /valid_rands /to_rands_t => />H H0 pid H1. have : (MaurerProtocol.valid_rand c (oget (assoc ((MaurerP.to_assoc a)) pid))). rewrite H0 => />*. clear H0.
    rewrite MaurerP.assoc_to_assoc. move :H1. rewrite in_iseq => />*. qed.

  lemma mu1_gen_rand_to c rs :
    mu1 (gen_rand c) (to_rands_t rs) = mu1 (MaurerMPCRevealProofs.M.gen_rand c) rs.
    rewrite /gen_rand /to_rands_t => />*. rewrite dmap1E /pub_input_conv /pred1 /(\o) => />*.
    apply (mu_eq) => />*. rewrite MaurerP.to_assoc_eq => />*. qed.

  lemma mu1_gen_rand_from c rs :
    P.valid_rands c rs =>
    mu1 (gen_rand c.`1) rs = mu1 (MaurerMPCReveal.gen_rand c.`1) (from_rands_t rs).
    rewrite /gen_rand /from_rands_t => />. rewrite dmap1E /pub_input_conv /pred1 /(\o) => />. move => H H0.
    apply (mu_eq) => />x. rewrite MaurerP.tP => />. have : size rs = 5. have : size (unzip1 rs) = 5. rewrite H. rewrite size_iseq => />*. rewrite size_map => />*. move => H1. rewrite eq_logical => />*. progress.
    rewrite MaurerP.get_init andabP andaP => />*. rewrite MaurerP.assoc_to_assoc => />*. rewrite andabP andaP => />*. 
    apply (eq_from_nth witness) => />. rewrite MaurerP.size_to_assoc => />*. rewrite /size H1 => />*. move => i. rewrite MaurerP.size_to_assoc => />Hi1 Hi2. rewrite MaurerP.nth_to_assoc_some => />*. rewrite nth_onth (onth_nth (witness,witness)) => />. move :Hi2. rewrite /size H1 => />*. rewrite -(zip_unzip rs) => />*. rewrite nth_zip => />*. rewrite !size_map => />*. rewrite (nth_map witness) => />*. move :Hi2. rewrite H1 /size => />*. rewrite (nth_map witness) => />*. move :Hi2. rewrite H1 /size => />*. rewrite H2 => />*. clear H2. rewrite MaurerP.get_init andabP andaP => />*. rewrite -(zip_unzip rs) => />*. rewrite H => />*. rewrite nth_onth (onth_nth (witness,witness)) => />*. rewrite size_zip size_map => />*. rewrite size_iseq => />*. rewrite ge0_max => />*. smt(size_ge0). rewrite nth_zip => />*. rewrite size_iseq size_map => />*. rewrite ge0_max => />*. rewrite H1 => />*. rewrite nth_iseq => />*. move :Hi2. rewrite /size => />*. rewrite Hi1 => />*. rewrite andaP => />*. 
    rewrite (assoc_iseq_some witness) => />*. rewrite H /pid_set H1 => />*. move :Hi2. rewrite H1 /size => />*. qed.

  lemma supp_from_gen_rand c rs :
    rs \in gen_rand c => from_rands_t rs \in MaurerMPCRevealProofs.M.gen_rand c.
    rewrite /from_rands_t /gen_rand /pub_input_conv => />. rewrite supp_dmap => />a H.
    rewrite (_:(MaurerP.init (fun (i : MaurerProtocolFunctionality.pid_t) => oget (assoc ((MaurerP.to_assoc a)) i)))=a) => />*. rewrite MaurerP.tP /size => />i Hi1 Hi2. rewrite MaurerP.get_init => />*. rewrite MaurerP.assoc_to_assoc => />*. rewrite /size !andabP !andaP => />*. qed.

  lemma to_supp_gen_rand c rs :
    rs \in MaurerMPCReveal.gen_rand c => to_rands_t rs \in gen_rand c.
    rewrite /to_rands_t /gen_rand => />H. rewrite supp_dmap => />*. move :H. rewrite /pub_input_conv => />*. exists rs => />*. qed.

  lemma valid_to_from_rands_t c rs :
    P.valid_rands c rs => to_rands_t (from_rands_t rs) = rs.
    rewrite /valid_rands /to_rands_t /from_rands_t => />H H0. apply (eq_from_nth witness) => />. rewrite MaurerP.size_to_assoc => />*. have : size (unzip1 rs) = size F.pid_set. rewrite H => />*. rewrite size_map size_iseq /size => />H1. rewrite H1 ge0_max => />. move => i. rewrite MaurerP.size_to_assoc /size => />Hi1 Hi2. 
    rewrite MaurerP.nth_to_assoc_some => />*. rewrite MaurerP.get_init andabP Hi1 Hi2 => />*. rewrite -(zip_unzip rs). rewrite assoc_zip => />*. rewrite !size_map => />*. rewrite nth_onth (onth_nth (witness,witness)) => />*. have : size (unzip1 rs) = size F.pid_set. rewrite H => />*. rewrite size_map size_iseq /size => />szrs. rewrite size_zip !size_map => />*. smt(). rewrite nth_zip => />*. rewrite !size_map => />*. rewrite !(nth_map witness) => />*. have : size (unzip1 rs) = size F.pid_set. rewrite H => />*. rewrite size_map size_iseq => />szrs. rewrite szrs ge0_max => />*. have : size (unzip1 rs) = size F.pid_set. rewrite H => />*. rewrite size_map size_iseq => />szrs. rewrite szrs ge0_max => />*.
    rewrite (onth_nth witness) => />*. rewrite !H => />*. rewrite !index_iseq => />*. rewrite in_iseq => />*. rewrite size_map => />*. have : size (unzip1 rs) = 5. rewrite H size_iseq => />*. rewrite size_map => />szrs. rewrite szrs Hi2 => />*. rewrite (nth_map witness) => />*. rewrite !H !index_iseq => />*. rewrite in_iseq => />*. have : size (unzip1 rs) = 5. rewrite H size_iseq => />*. rewrite size_map => />szrs. rewrite szrs Hi2 => />*. rewrite H index_iseq => />*. rewrite in_iseq => />*. rewrite (unzip1_eq_nth _ (unzip1 rs)) => />*. have : size (unzip1 rs) = 5. rewrite H size_iseq => />*. rewrite size_map => />szrs. rewrite szrs Hi2 => />*. rewrite H nth_iseq => />*. rewrite Hi1 Hi2 => />*. qed.

  lemma dom_simulator cr c xs rs y :
    unzip1 (simulator cr c xs rs y) = cr.
    rewrite /simulator => />*. rewrite /to_corrupted_views_t => />*. rewrite -map_comp /(\o) => />*. rewrite map_id => />*. qed.

  lemma size_simulator cr c xs rs y :
    valid_corrupted_set cr =>
    size (simulator cr c xs rs y) = 2.
    move => H. have : unzip1 (simulator cr c xs rs y) = cr. rewrite dom_simulator => />. move => H0. have : size (unzip1 (simulator cr c xs rs y)) = 2. rewrite H0 => />*. move :H. rewrite /valid_corrupted_set => />*. rewrite size_map => />*. qed.

  lemma privacy2 (D <: Distinguisher_t) :
    equiv [Privacy(D).real2 ~ Privacy(D).ideal2 : F.valid_circuit c{1} /\ F.valid_inputs c{1} xs{1} /\ valid_corrupted_set cr{1} /\ ={glob D,c,xs,cr} ==> ={res} ].
    proc. symmetry. call MaurerMPCRevealProofs.mpc_privacy => />*. auto => />. progress.
    rewrite /from_corrupted_parties_t /partyset /ISet.subset subsetP /(<=) /ISet.oflist /ISet.iset /parties => />a I. have : a \in F.pid_set. rewrite H7 => />*. rewrite -mem_oflist I //. rewrite iset_in_def in_iseq => />*. move :H5. rewrite /t /corrupted_t => />H5. rewrite /ISet.card cardE => />*. have : perm_eq cr{1} (elems (oflist cr{1})). rewrite oflist_uniq => />*. move => H8. have : size cr{1} = size (elems (oflist cr{1})). apply (perm_eq_size) => />*. progress. rewrite /from_corrupted_parties_t /ISet.oflist. rewrite -H9 => />*. 
    rewrite (_:MaurerMPCRevealProofs.M.P.valid_inputs=MaurerMPCReveal.P.valid_inputs). progress. rewrite MaurerCompatProofs.valid_inputs_from => />. qed.

  lemma maurer_privacy (D <: Distinguisher_t) :
    equiv [GameReal(D,Rand).main ~ GameIdeal(D,Rand,Simulator).main : F.valid_circuit c{1} /\ ={glob D,c,aux,x} ==> ={res} ]. 
    proc. simplify.
    seq 1 1 : ( F.valid_circuit c{1} /\ ={glob D,c,xs,cr} ).
    call (_: true ) => />*. auto => />*. 
    inline Rand.gen. sp. 
    transitivity{1}
      { b' <@ Privacy(D).real1(c,xs,cr); }
      ( F.valid_circuit c{1} /\ c0{1}=c{1} /\ ={glob D,c,c0,xs,cr} ==> ={b'} )
      ( F.valid_circuit c{1} /\ c0{1}=c{1} /\ ={glob D,c,c0,xs,cr} ==> ={b'} ).
      progress. exists (glob D){2} c{2} c{2} cr{2} xs{2} => />*. 
      progress. 
    inline *. wp. sp. if{2}.
    seq 1 1 : (#pre /\ rs{1}=rs0{2} /\ P.valid_rands c{1} rs{1}). auto.
    move => &1 &2 H. split. progress. move => H0. split. progress. move :H. progress. move => H1 H2 H3. split. move :H. progress. move => H4. split. trivial. move => H5. split. move :H. progress. rewrite valid_gen_rand => />*. move :H. progress.
    sp. if{1}. sp. call (_: true ) => />*. auto => />. progress. 
    conseq (_ : false ==> _ ). progress. smt(). auto => />. progress.
    seq 1 0 : #pre. rnd{1}. auto => />*. rewrite gen_rand_ll => />*. 
    sp. if{1}. sp. conseq (_ : false ==> _). progress. smt(). auto => />. progress. 
    auto => />. progress. 
    transitivity{2}
      { b' <@ Privacy(D).ideal1(c,xs,cr); }
      ( F.valid_circuit c{1} /\ c0{1}=c{1} /\ ={glob D,c,c0,xs,cr} ==> ={b'} )
      ( F.valid_circuit c{1} /\ c0{1}=c{1} /\ ={glob D,c,c0,xs,cr} ==> ={b'} ).
      progress. exists (glob D){2} c0{2} c0{2} cr{2} xs{2} => />*. 
      progress. 
    inline Privacy(D).real1 Privacy(D).ideal1. sp. if. 
      progress.
    wp. seq 2 2 : ( ={glob D,vsc0} ).
    (* actual proof start *)
    transitivity{1}
      { vsc0 <@ Privacy(D).real2(c1,xs,cr1); }
      ( F.valid_circuit c{1} /\ F.valid_inputs c{1} xs{1} /\ valid_corrupted_set cr{1} /\ cr1{1}=cr{1} /\ c0{1} = c{1} /\ c1{1} = c{1} /\ xs0{1}=xs{1} /\ ={glob D,c,c0,c1,xs,xs0,cr,cr1} ==> ={glob D,vsc0} )
      ( F.valid_circuit c{1} /\ F.valid_inputs c{1} xs{1} /\ valid_corrupted_set cr{1} /\ cr1{1}=cr{1} /\ c0{1} = c{1} /\ c1{1} = c{1} /\ xs0{1}=xs{1} /\ ={glob D,c,c0,c1,xs,xs0,cr,cr1} ==> ={glob D,vsc0} ).
      progress. exists (glob D){2} c0{2} c0{2} c0{2} cr{2} cr{2} xs{2} xs{2} => />*.
      progress.
    inline *. sp. seq 1 1 : (#pre /\ from_rands_t rs0{1}=cs{2}). rnd from_rands_t to_rands_t => />. progress. move :H H0. progress. rewrite mu1_gen_rand_to => />*. rewrite supp_from_gen_rand => />*. rewrite (valid_to_from_rands_t c1{2}). rewrite valid_gen_rand => />*. trivial.
    auto => />. progress. rewrite MaurerCompatProofs.from_to_rands_t => />*. rewrite mu1_gen_rand_to => />*. rewrite supp_from_gen_rand => />*. rewrite (valid_to_from_rands_t c1{2}). rewrite valid_gen_rand => />*. trivial. 
    sp. auto => />. progress. 
    rewrite /to_corrupted_views_t /corrupted /from_corrupted_parties_t => />*. apply (eq_from_nth witness) => />. rewrite !size_map => />. rewrite size_map => />. move => i Hi1 Hi2. rewrite !(nth_map witness) => />*. rewrite /input /to_view_t /IMap.get /IMap.ofset ofset_some => />*. rewrite nth_in_oflist => />*.
    rewrite /get !MaurerP.get_zip3 => />*. have : 0 <= nth witness cr1{2} i && nth witness cr1{2} i < MaurerP.size. have : nth witness cr1{2} i \in F.pid_set. rewrite H7 => />*. rewrite nth_in => />*. rewrite in_iseq => />*. move => H8. rewrite !H8 => />*. 
    rewrite /trace /to_traces_t /rand /from_rands_t /snd3 => />*. rewrite !MaurerP.get_init => />*. rewrite assoc_map_r => />*. rewrite !H8 => />*. rewrite in_iseq => />*. rewrite MaurerP.get_map => />*. rewrite /stateful_protocol => />*. rewrite MaurerP.get_zip3 => />*. have : 0 <= nth witness cr1{2} i /\ nth witness cr1{2} i < 5. move :H8. rewrite /size => />*. move => H9. rewrite H9 => />*. rewrite H8 => />. rewrite MaurerCompatProofs.to_from_input_t => />*. rewrite in_iseq => />*. 
    transitivity{2}
      { vsc0 <@ Privacy(D).ideal2(c1,xs,cr1); }
      ( F.valid_circuit c{1} /\ F.valid_inputs c{1} xs{1} /\ valid_corrupted_set cr{1} /\ cr1{1} = cr{1} /\ c0{1} = c{1} /\ c1{1} = c{1} /\ xs0{1}=xs{1} /\ ={glob D,c,c0,c1,xs,xs0,cr,cr1} ==> ={glob D,vsc0} )
      ( F.valid_circuit c{1} /\ F.valid_inputs c{1} xs{1} /\ valid_corrupted_set cr{1} /\ cr1{1} = cr{1} /\ c1{1}=c{1} /\ xs0{1}=xs{1} /\ ={glob D,c,c0,c1,xs,xs0,cr,cr1} ==> ={glob D,vsc0} ).
      progress. exists (glob D){2} c1{2} c1{2} c1{2} cr1{2} cr1{2} xs0{2} xs0{2} => />*.
      progress.
    call (privacy2(D)) => />*. auto => />. progress.
    inline *. sp. seq 1 1 : (#pre /\ cs{1}=from_rands_t rs0{2}). rnd to_rands_t from_rands_t => />. progress. move :H H0. progress. rewrite mu1_gen_rand_from. rewrite valid_gen_rand => />*. progress. rewrite to_supp_gen_rand => />*. rewrite MaurerCompatProofs.from_to_rands_t => />*. 
    auto => />. progress. rewrite (MaurerCompatProofs.to_from_rands_t c1{2}). smt(valid_gen_rand) => />*. trivial. rewrite mu1_gen_rand_from. rewrite valid_gen_rand => />*. progress. rewrite to_supp_gen_rand => />*. rewrite MaurerCompatProofs.from_to_rands_t => />*. 
    sp. auto => />. progress. 
    rewrite /to_corrupted_views_t /corrupted /from_corrupted_parties_t => />*. apply (eq_from_nth witness) => />. rewrite !size_map => />*. rewrite size_simulator => />*. rewrite size_map => />. move => i Hi1 Hi2. rewrite (nth_map witness) => />*. rewrite eq2 => />*. progress. 
    rewrite (unzip1_eq_nth _ (unzip1 (simulator cr1{2} c1{2} ((P.extract_inputs xs0{2} cr1{2})) rs0{2} (map (fun (pid : pid_t) => (pid, oget (assoc ((F.f c1{2} xs0{2})) pid))) cr1{2}))) ) => />*. rewrite size_simulator => />*. move :Hi2. rewrite H5 /t => />*. rewrite dom_simulator => />*. rewrite /to_view_t /MaurerProtocol.simulator /to_corrupted_views_t => />*. rewrite (nth_map witness) /to_view_t => />*. split. 
    congr. rewrite /from_corrupted_parties_t /from_corrupted_inputs_t => />*. congr. congr. congr. rewrite (_:MaurerMPCRevealProofs.M.simulator=MaurerMPCReveal.simulator) /IMap.ofset /IMap.imap. progress. congr. rewrite -fmap_eqIn => />. rewrite !fdom_ofset !fdom_map => />*. rewrite fdom_ofassoc /extract_inputs => />*. rewrite -map_comp /(\o) => />*. rewrite map_id => />j. rewrite /ISet.oflist mem_oflist => />Hj. rewrite ofset_some /from_inputs_t => />*. rewrite mem_oflist => />. rewrite /get MaurerP.get_init => />*. have : 0 <= j < MaurerP.size. have : j \in F.pid_set. have : j \in F.pid_set. rewrite H7 => />*. move => H8. rewrite H8 => />. rewrite in_iseq /size => />. move => H8. rewrite H8 => />*. rewrite map_some => />*. rewrite mem_ofassoc => />*. rewrite -map_comp /(\o) => />*. rewrite map_id => />*. congr. rewrite ofassoc_get => />*. rewrite assoc_map_r => />*. rewrite Hj => />*. rewrite /f /from_outputs_t => />*. rewrite -nth0_head. rewrite (nth_map witness) => />*. rewrite H5 /t => />*. rewrite /to_outputs_t => />*. rewrite assoc_map_r => />*. rewrite in_iseq => />*. have : 0 <= nth witness cr1{2} 0 /\ nth witness cr1{2} 0 < 5. have : nth witness cr1{2} 0 \in F.pid_set. rewrite H7 => />*. rewrite nth_in => />*. rewrite H5 /t => />*. rewrite in_iseq => />*. move => H8. rewrite H8 => />*. 
    progress. congr. congr. congr. congr. rewrite /IMap.ofset /IMap.imap /from_corrupted_parties_t => />*. rewrite /from_corrupted_inputs_t => />*. rewrite -fmap_eqIn => />. rewrite !MaurerMPCRevealProofs.dom_simulator => />. move => j. rewrite /ISet.oflist mem_oflist => Hj. rewrite (_:MaurerMPCRevealProofs.M.simulator=MaurerMPCReveal.simulator). progress. congr. congr. rewrite /IMap.imap /IMap.ofassoc -fmap_eqIn => />. rewrite !fdom_ofset !fdom_map => />*. rewrite fdom_ofassoc /extract_inputs => />*. rewrite -map_comp /(\o) => />*. rewrite map_id => />k. rewrite mem_oflist => />Hk. rewrite ofset_some /from_inputs_t => />*. rewrite mem_oflist => />. rewrite /get MaurerP.get_init => />*. have : 0 <= k < MaurerP.size. have : k \in F.pid_set. rewrite H7 => />*. rewrite in_iseq => />*. move => H8. rewrite H8 => />*. rewrite map_some => />*. rewrite mem_ofassoc => />*. rewrite -map_comp /(\o) => />*. rewrite map_id => />*. congr. rewrite ofassoc_get => />*. rewrite assoc_map_r => />*. rewrite Hk => />*. rewrite /from_outputs_t /f => />*. rewrite -nth0_head (nth_map witness) => />*. rewrite H5 /t => />*. rewrite /to_outputs_t assoc_map_r => />*. rewrite in_iseq => />*. have : 0 <= nth witness cr1{2} 0 /\ nth witness cr1{2} 0 < 5. have : nth witness cr1{2} 0 \in F.pid_set. rewrite H7 => />*. rewrite nth_in => />*. rewrite H5 /t => />*. rewrite in_iseq => />*. move => H8. rewrite H8 => />*. 
    congr. congr. congr. congr. rewrite /from_corrupted_parties_t => />*. rewrite /from_corrupted_inputs_t => />*. rewrite -fmap_eqIn => />. rewrite !MaurerMPCRevealProofs.dom_simulator => />. move => j. rewrite /ISet.oflist mem_oflist => />Hj. rewrite (_:MaurerMPCRevealProofs.M.simulator=MaurerMPCReveal.simulator). progress. congr. congr. rewrite /IMap.ofset /IMap.ofassoc /IMap.imap -fmap_eqIn => />. rewrite !fdom_ofset !fdom_map !fdom_ofassoc => />. rewrite /extract_inputs => />. rewrite -map_comp /(\o) => />*. rewrite map_id => />k. rewrite mem_oflist => />Hk. rewrite /get ofset_some => />. rewrite mem_oflist => />. rewrite /from_inputs_t map_some => />*. rewrite mem_ofassoc /extract_inputs => />*. rewrite -map_comp /(\o) => />*. rewrite map_id => />*. rewrite MaurerP.get_init => />*. have : 0 <= k < MaurerP.size. have : k \in F.pid_set. rewrite H7 => />*. rewrite in_iseq => />*. move => H8. rewrite H8 => />*. congr. rewrite ofassoc_get /extract_inputs => />*. rewrite assoc_map_r => />*. rewrite Hk => />*. rewrite /from_outputs_t /f /to_outputs_t => />*. rewrite -nth0_head (nth_map witness) => />*. rewrite H5 /t => />*. rewrite assoc_map_r => />*. rewrite in_iseq => />*. have : 0 <= nth witness cr1{2} 0 /\ nth witness cr1{2} 0 < 5. have : nth witness cr1{2} 0 \in F.pid_set. rewrite H7 => />*. rewrite nth_in => />*. rewrite H5 /t => />*. rewrite in_iseq => />*. move => H8. rewrite H8 => />*. 
    (* actual proof end *)
    call (_: true ) => />*. auto => />. 
    auto => />. 
    inline *. sp. if{1}. seq 1 1: (#pre /\ rs0{1}=rs{2} /\ P.valid_rands c{2} rs{2}).
    rnd. auto. move => &1 &2 H. split. progress. move :H. progress. move => H0 H1 H2. split. move :H. progress. move => H3. split. move :H. progress. rewrite valid_gen_rand => />*. move :H. progress.
    sp. if{2}. sp. wp. call (_: true) => />*.  auto => />. 
    conseq (_: (F.valid_inputs c1{1} xs{1} /\ valid_corrupted_set cr{1} /\ P.valid_rands c{2} rs{2}) /\ !((F.valid_inputs c1{1} xs{1} /\ valid_corrupted_set cr{1} /\ P.valid_rands c{2} rs{2})) ==> _).
    move => &1 &2 H. split. move :H. progress. move :H. progress. smt(). conseq (_:false ==> _). progress. smt(). auto => />.
    seq 0 1 : (#pre). rnd{2} => />. auto => />. move => &2 H1 H2 H3 H4 H5. rewrite gen_rand_ll => />*. 
    sp. if{2}. conseq (_:false ==> _). progress. smt(). auto => />.
    wp. rnd => />. auto => />. 
    qed.

end MaurerCompatPrivacy.
