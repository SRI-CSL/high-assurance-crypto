require import AllCore Int List Distr Ring.
require import Aux AuxList.
require import NextMsgArray NextMsgFixedArray NextMsgISet NextMsgIMap NextMsgTrace NextMsgProtocol NextMsgStatefulProtocol NextMsgCircuit.
require import NextMsgWeak NextMsgMPC NextMsgMPCReveal.
require import NextMsgMaurerP NextMsgMaurerAPI.
require import Array5 Array6 Array9 Array10.

import ISet IMap Array AuxFSet AuxSmtMap.

theory MaurerAdd.

  import MaurerAPI.

  clone include Gate with
    theory GT.P = MaurerP,
    type GT.msg = unit,
    type GT.local_rand = unit,
    type Gate = wid * (wid * wid), (* destination wire + two input wires *)
    type share = wire_st * pub_st,
    type local_msgs = unit,

    op local_gate_start _ wij st r = tt,
    op local_gate_end _ (wij:Gate) (st:share) _ =
      (add wij.`2.`1 wij.`2.`2 st.`1,st.`2),
    op consistent_inputs (wij:Gate) i j si sj =
      add_valid_share wij si /\ add_valid_share wij sj /\ consistent_shares i j si sj,
    
    op gate_valid_rand wij rs = true,
    op valid_local_messages _ _ _ = true,
    op valid_msg _ _ _ = true,
    op GT.eq_msg m1 m2 = true,
    op from_local_messages (msgs:local_messages) = MaurerP.init (fun i => tt),
    op to_local_messages (msgs:ST.pmsgs) = tt,
    op send_messages (msgs:out_messages) = MaurerP.init (fun i => tt)
    proof *.
    realize valid_send_messages.
    rewrite /valid_messages /all => |>*. qed.
    realize valid_stateful_local_protocol_round.
    rewrite /valid_local_messages => |>*. qed.
    realize to_from_local_messages.
    rewrite /to_local_messages /from_local_messages => |>*. qed.
    realize from_to_local_messages.
    rewrite /from_local_messages /to_local_messages => |>*. rewrite MaurerP.tP => |>*. qed.
    realize ppswap_from_messages.
    rewrite /from_messages /send_messages => |>*. rewrite ST.ppmap_eqP => />. qed.
    realize GT.eq_msgP. progress. qed.
    realize valid_pmsgs_from. rewrite /valid_local_messages /valid_pmsgs => |>p r xs. rewrite ST.P.allP => |>. move => /> i Hi1 Hi2. qed.
    realize get_local_messages_eqP. 
    rewrite /from_local_messages => |>. qed.
    realize valid_local_messages_to.
    rewrite /valid_pmsgs /valid_local_messages /to_local_messages => />. qed.

end MaurerAdd.

theory MaurerSMul.

  import MaurerAPI.

  clone include Gate with
    theory GT.P = MaurerP,

    type GT.msg = unit,
    type GT.local_rand = unit,
    type Gate = wid * (wid * wid), (* destination wire + secret wire + public wire *)
    type share = wire_st * pub_st,
    type local_msgs = unit,

    op local_gate_start _ (wij:Gate) (st:share) (r:GT.local_rand) = tt,
    op local_gate_end _ (wij:Gate) (st:share) pmsgs =
      (smul wij.`2.`1 wij.`2.`2 st.`1,st.`2),
    op consistent_inputs (wij:Gate) i j si sj =
      smul_valid_share wij si /\ smul_valid_share wij sj /\ consistent_shares i j si sj,
    
    op gate_valid_rand wij rs = true,
    op valid_local_messages _ _ _ = true,
    op valid_msg _ _ _ = true,
    op GT.eq_msg m1 m2 = true,
    op to_local_messages = MaurerAdd.to_local_messages,
    op from_local_messages = MaurerAdd.from_local_messages,
    op send_messages = MaurerAdd.send_messages
    proof *.
    realize valid_send_messages.
    rewrite /valid_messages /all => |>*. qed.
    realize valid_stateful_local_protocol_round.
    rewrite /valid_local_messages => |>*. qed.
    realize to_from_local_messages.
    rewrite /to_local_messages /from_local_messages => |>*. qed.
    realize from_to_local_messages.
    rewrite /from_local_messages /to_local_messages => |>*. rewrite MaurerP.tP => |>*. qed.
    realize ppswap_from_messages.
    rewrite /from_messages /send_messages => |>*. rewrite ST.ppmap_eqP => />. qed.
    realize GT.eq_msgP. progress. qed.
    realize valid_pmsgs_from. rewrite /valid_local_messages /valid_pmsgs => |>p r xs. rewrite ST.P.allP => |>. move => /> i Hi1 Hi2. qed.
    realize get_local_messages_eqP. 
    rewrite /from_local_messages => |>. qed.
    realize valid_local_messages_to.
    rewrite /valid_pmsgs /valid_local_messages /to_local_messages => />. qed.

end MaurerSMul.

theory MaurerConst.

  import MaurerAPI.

  clone include Gate with
    theory GT.P = MaurerP,

    type GT.msg = unit,
    type GT.local_rand = unit,
    type Gate = wid * val, (* destination wire + public value *)
    type share = wire_st * pub_st,
    type local_msgs = unit,

    op local_gate_start _ (wc:Gate) (st:share) (r:GT.local_rand) = tt,
    op local_gate_end i (wc:Gate) (st:share) pmsgs =
      (cnst i wc.`2 st.`1,ISet.add st.`2 (get_wire_st_next st.`1)),
    op consistent_inputs (wij:Gate) i j si sj =
      const_valid_share wij si /\ const_valid_share wij sj /\ consistent_shares i j si sj,

    op gate_valid_rand wij rs = true,
    op valid_local_messages _ _ _ = true,
    op valid_msg _ _ _ = true,
    op GT.eq_msg m1 m2 = true,
    op to_local_messages = MaurerAdd.to_local_messages,
    op from_local_messages = MaurerAdd.from_local_messages,
    op send_messages = MaurerAdd.send_messages
    proof *.
    realize valid_send_messages.
    rewrite /valid_messages /all => |>*. qed.
    realize valid_stateful_local_protocol_round.
    rewrite /valid_local_messages => |>*. qed.
    realize to_from_local_messages.
    rewrite /to_local_messages /from_local_messages => |>*. qed.
    realize from_to_local_messages.
    rewrite /from_local_messages /to_local_messages => |>*. rewrite MaurerP.tP => |>*. qed.
    realize ppswap_from_messages.
    rewrite /from_messages /send_messages => |>*. rewrite ST.ppmap_eqP => />. qed.
    realize GT.eq_msgP. progress. qed.
    realize valid_pmsgs_from. rewrite /valid_local_messages /valid_pmsgs => |>p r xs. rewrite ST.P.allP => |>. move => /> i Hi1 Hi2. qed.
    realize get_local_messages_eqP. 
    rewrite /from_local_messages => |>. qed.
    realize valid_local_messages_to.
    rewrite /valid_pmsgs /valid_local_messages /to_local_messages => />. qed.

end MaurerConst.

theory MaurerMul.

  import MaurerAPI.

  clone include Gate with
    theory GT.P = MaurerP,
    type GT.msg = msg,
    type GT.local_rand = rand,
    type Gate = wid * (wid * wid), (* destination wire + two input wires *)
    type share = wire_st * pub_st,
    type local_msgs = msgs,

    op local_gate_start _ (wij:Gate) (st:share) (r:GT.local_rand) =
      (mul_start wij.`2.`1 wij.`2.`2 st.`1 r),
    op local_gate_end _ (wij:Gate) (st:share) pmsgs =
      (mul_end pmsgs st.`1,st.`2),
    op consistent_inputs (wij:Gate) i j si sj =
      add_valid_share wij si /\ add_valid_share wij sj /\ consistent_shares i j si sj,

    op gate_valid_rand wij rs = true,
    op valid_local_messages _ _ msgs = true,
    op valid_msg _ _ _ = true,
    op GT.eq_msg = eq_msg,
    op to_local_messages = mk_msgs,
    op from_local_messages msgs = MaurerP.init (fun i => get_msg msgs i),
    op send_messages = send_messages
    proof *.
    realize valid_send_messages.
    rewrite /valid_messages /all => |>*. qed.
    realize valid_stateful_local_protocol_round.
    rewrite /valid_local_messages => |>*. qed.
    realize to_from_local_messages.
    rewrite /to_local_messages /from_local_messages => |>p r xs H. rewrite mk_msgs_id => />. qed.
    realize from_to_local_messages.
    rewrite /to_local_messages /from_local_messages => |>*. rewrite MaurerP.tP => |>*. rewrite MaurerP.get_init andabP andaP => |>*. rewrite get_mk_msgs => |>*. qed.
    realize ppswap_from_messages.
    rewrite /from_messages /MaurerMul.send_messages => |>p r outs H. rewrite ST.ppmap_eqP /ppswap => |>x y H1 H2. rewrite !ST.get_ppinit !H1 => |>*. rewrite !ST.get_pinit !H2 => |>*. rewrite GT.get_pmap => |>*. rewrite /get_shr /from_local_messages => />. rewrite /ST.P.get /GT.P.get. rewrite !MaurerP.get_init => />. move :H1 H2. rewrite /ISet.mem /ISet.iset /partyset !iset_in_def /parties /size => />Hx1 Hx2 Hy1 Hy2. rewrite /get_msg => />. rewrite Array5.initE andabP andaP => />. qed.
    realize valid_pmsgs_from. rewrite /valid_local_messages /valid_pmsgs /from_local_messages => |>p r xs. rewrite ST.P.allP => |>. move => /> i Hi1 Hi2. qed.
    realize GT.eq_msgP. move => |>m1 m2.  qed.
    realize get_local_messages_eqP.
    rewrite /from_local_messages => |>xs ys. rewrite eq_msgsP => |>. rewrite eq_logical => |>. split. move => H x Hx. rewrite /ST.P.get /GT.P.get !MaurerP.get_init => |>. move :Hx. rewrite /ISet.mem /ISet.iset iset_in_def /parties => |>H1 H2. move :H. rewrite -eq_msgsP => |>. 
    move => H. rewrite /eq_msgs allP => |>x. rewrite in_iseq => |>H1 H2. have : MaurerP.get (MaurerP.init (get_shr xs)) x = MaurerP.get (MaurerP.init (get_shr ys)) x. rewrite /ST.P.get /GT.P.get in H. rewrite H => |>. rewrite /ISet.mem /ISet.iset iset_in_def => |>. rewrite !MaurerP.get_init !andabP !andaP => |>. qed.
    realize valid_local_messages_to.
    rewrite /valid_pmsgs /valid_local_messages /to_local_messages => />. qed.

end MaurerMul.

theory MaurerGate.

  import MaurerAPI.

  type gate = [ | Add of MaurerAdd.Gate
              | SMul of MaurerSMul.Gate
              | Const of MaurerConst.Gate
              | Mul of MaurerMul.Gate
            ].

op gate_start i g st (r:(unit,rand) either) =
    with g = Add wij => L tt
    with g = SMul wij => L tt
    with g = Const wij => L tt
    with g = Mul wij => R (MaurerMul.local_gate_start i wij st (unR r)).
op gate_end i g st ins =
    with g = Add wij => MaurerAdd.local_gate_end i wij st (unL ins)
    with g = SMul wij => MaurerSMul.local_gate_end i wij st (unL ins)
    with g = Const wij => MaurerConst.local_gate_end i wij st (unL ins)
    with g = Mul wij => MaurerMul.local_gate_end i wij st (unR ins).
op gate_consistent_inputs g i j si sj = 
    with g = Add wij => MaurerAdd.consistent_inputs wij i j si sj
    with g = SMul wij => MaurerSMul.consistent_inputs wij i j si sj
    with g = Const wij => MaurerConst.consistent_inputs wij i j si sj
    with g = Mul wij => MaurerMul.consistent_inputs wij i j si sj.
op gate_valid_local_messages g r rs =
    with g = Add wij => isL rs /\ MaurerAdd.valid_local_messages wij r (unL rs)
    with g = SMul wij => isL rs /\ MaurerSMul.valid_local_messages wij r (unL rs)
    with g = Const wij => isL rs /\ MaurerConst.valid_local_messages wij r (unL rs)
    with g = Mul wij => isR rs /\ MaurerMul.valid_local_messages wij r (unR rs).
op gate_valid_msg g r rs =
    with g = Add wij => isL rs /\ MaurerAdd.valid_msg wij r (unL rs)
    with g = SMul wij => isL rs /\ MaurerSMul.valid_msg wij r (unL rs)
    with g = Const wij => isL rs /\ MaurerConst.valid_msg wij r (unL rs)
    with g = Mul wij => isR rs /\ MaurerMul.valid_msg wij r (unR rs).

op gate_to_local_messages (ms:((unit,msg) either) MaurerP.arrayN) = if MaurerP.all (fun i => isR) ms
  then R (mk_msgs (MaurerP.map unR ms))
  else L tt.

op gate_from_local_messages (ms:(unit,msgs) either) =
  with ms = L tt => MaurerP.init (fun i => L tt)
  with ms = R ms0 => MaurerP.init (fun i => R (get_msg ms0 i)).

lemma isR_gate_from_local_messages ms i :
  0 <= i < 5 =>
  isR ms = isR (MaurerP.get (gate_from_local_messages ms) i).
  case ms => |>*. rewrite MaurerP.get_init andabP andaP => |>*.
  rewrite MaurerP.get_init andabP andaP => |>*. qed.

op gate_send_messages (ms:((unit,msgs) either) MaurerP.arrayN) : ((unit,msgs) either) MaurerP.arrayN = if MaurerP.all (fun i => isR) ms
  then MaurerP.map (fun x => R x) (MaurerAPI.send_messages (MaurerP.map unR ms))
  else ms.
 
  op gate_valid_rand' (g:gate) rs =
    with g = Add wij => isL rs /\ MaurerAdd.gate_valid_rand wij (unL rs)
    with g = SMul wij => isL rs /\ MaurerSMul.gate_valid_rand wij (unL rs)
    with g = Const wij => isL rs /\ MaurerConst.gate_valid_rand wij (unL rs)
    with g = Mul wij => isR rs /\ MaurerMul.gate_valid_rand wij (unR rs).

  clone include Gate with
    theory GT.P = MaurerP,

    type GT.msg = (unit,msg) either,
    type GT.local_rand = (unit,rand) either,
    type Gate = gate,
    type share = wire_st * pub_st,
    type local_msgs = (unit,msgs) either,

    op local_gate_start = gate_start,
    op local_gate_end = gate_end,
    op consistent_inputs = gate_consistent_inputs,

    op gate_valid_rand = gate_valid_rand',
    op valid_local_messages = gate_valid_local_messages,
    op valid_msg = gate_valid_msg,
    op GT.eq_msg m1 m2 = eq_either (=) eq_msg m1 m2,
    op to_local_messages = gate_to_local_messages,
    op from_local_messages = gate_from_local_messages,
    op send_messages = gate_send_messages
    proof *.
    realize valid_send_messages.
    rewrite /valid_messages /all /send_messages /gate_send_messages => |> outs p r. rewrite !allP => |>H x H1. 
    have : valid_local_messages p r ((MaurerP.get outs x)). rewrite H => |>*. 
    case (MaurerP.all (fun (_ : int) => isR) outs) => |>H2 H3.
    rewrite MaurerP.get_map => |>*. move :H1. rewrite in_iseq => |>*. move :H2. rewrite MaurerP.allP => |>H2. clear H. move :H3. elim p => |>g H3.
    have : isR ((MaurerP.get outs x)). rewrite H2 => |>*. move :H1. rewrite in_iseq => |>*. move :H3. case (MaurerP.get outs x) => |>*. 
    have : isR ((MaurerP.get outs x)). rewrite H2 => |>*. move :H1. rewrite in_iseq => |>*. move :H3. case (MaurerP.get outs x) => |>*. 
    have : isR ((MaurerP.get outs x)). rewrite H2 => |>*. move :H1. rewrite in_iseq => |>*. move :H3. case (MaurerP.get outs x) => |>*. rewrite /valid_local_messsages => />. qed.
    realize valid_stateful_local_protocol_round.
    rewrite /valid_local_messages /stateful_local_protocol_round /local_gate_start /gate_valid_local_messages => |>i r x st. elim x => />*. qed.
    realize to_from_local_messages.
    rewrite /valid_local_messages /to_local_messages /from_local_messages /gate_to_local_messages /gate_from_local_messages => |>p r xs H. case (MaurerP.all (fun (_ : int) => isR) (gate_from_local_messages xs)) => |>H0. move :H0. rewrite MaurerP.allP => |>H0. move :H. elim p => |>g H1 H2. 
    have : isR xs. rewrite (isR_gate_from_local_messages xs 0) => |>*. rewrite H0 => |>*. move :H2 H1 H0. case xs => |>*. 
    have : isR xs. rewrite (isR_gate_from_local_messages xs 0) => |>*. rewrite H0 => |>*. move :H2 H1 H0. case xs => |>*. 
    have : isR xs. rewrite (isR_gate_from_local_messages xs 0) => |>*. rewrite H0 => |>*. move :H2 H1 H0. case xs => |>*. 
    clear H0. move :H2 H1. elim xs => |>x H. move :H. rewrite /valid_local_messages => |>*.
    rewrite (MaurerAPI.mk_msgs_id' x _) => |>*. rewrite /get_shr => />. rewrite MaurerP.tP => />i Hi1 Hi2. rewrite !MaurerP.get_init andabP andaP => />. rewrite !MaurerP.get_init andabP andaP => />. 
    move :H0. rewrite MaurerP.allP => |>H0. move :H. elim p => |>g H1 H2.
    clear H0 H2. move :H1. case xs => |>*. 
    clear H0 H2. move :H1. case xs => |>*.
    clear H0 H2. move :H1. case xs => |>*.
    rewrite negb_forall in H0 => |>*. move :H0. progress. case (0 <= a && a < 5) => |>. move => H3 H4. move :H. rewrite -(isR_gate_from_local_messages xs a) => |>H5. smt(). smt(). qed.    
    realize from_to_local_messages.
    rewrite /valid_local_pmsgs /to_local_messages /from_local_messages /gate_to_local_messages /gate_from_local_messages => |>p r xs H. case (MaurerP.all (fun (_ : int) => isR) xs) => |>. rewrite MaurerP.allP => |>H0. rewrite MaurerP.tP => |>i Hi1 Hi2. rewrite MaurerP.get_init andabP andaP => |>. rewrite MaurerAPI.get_mk_msgs => |>. rewrite MaurerP.get_map => |>. have : isR (MaurerP.get xs i). rewrite H0 => |>. smt().
    rewrite MaurerP.allP negb_forall => |>i H1. rewrite MaurerP.tP => |>j Hj1 Hj2. rewrite MaurerP.get_init andabP andaP => |>. move :H. rewrite /valid_pmsgs ST.P.allP => |>H. have : valid_msg p r (MaurerP.get xs j). rewrite H => |>. rewrite /valid_msg => |>. move :H. case p => |>g.
    rewrite /valid_msg => /> * /#.
    rewrite /valid_msg => /> * /#.
    rewrite /valid_msg => /> * /#.
    rewrite /valid_msg => /> * /#.
    qed.
    realize ppswap_from_messages.
    rewrite /from_messages /send_messages => |>p r outs H. rewrite ST.ppmap_eqP /ppswap => |>x y Hx Hy. rewrite !ST.get_ppinit !Hx => |>*. rewrite !ST.get_pinit !Hy => |>*. rewrite !GT.get_pmap => |>. rewrite Hx => />. rewrite /gate_send_messages /from_local_messages => |>*. move :H. rewrite /valid_messages ST.P.allP => |>. move :Hx Hy. rewrite !/ISet.mem /ISet.iset !iset_in_def /parties => |>Hx1 Hx2 Hy1 Hy2. elim p => |>g H.
    have : ! MaurerP.all (fun (_ : int) => isR) outs. rewrite MaurerP.allP negb_forall => />. exists 0 => />. have : valid_local_messages (Add g) r (MaurerP.get outs 0). rewrite H => |>. smt(). rewrite /valid_local_messages => |>. case (MaurerP.get outs 0) => />. move => H1. rewrite H1 => |>. have : isL (MaurerP.get outs y). have : valid_local_messages (Add g) r (MaurerP.get outs y). rewrite H => |>. rewrite /valid_local_messages => |>. rewrite !/ST.P.get !/GT.P.get. case (MaurerP.get outs y) => |>z. rewrite MaurerP.get_init andabP andaP => |>. have : isL (MaurerP.get outs x). have : valid_local_messages (Add g) r (MaurerP.get outs x). rewrite H => |>. rewrite /valid_local_messages => |>. case (MaurerP.get outs x) => |>w. rewrite MaurerP.get_init andabP andaP => |>. 
    have : ! MaurerP.all (fun (_ : int) => isR) outs. rewrite MaurerP.allP negb_forall => |>. exists 0 => |>. have : valid_local_messages (SMul g) r (MaurerP.get outs 0). rewrite H => |>. rewrite /valid_local_messages => />. rewrite /valid_local_messages => />. case (MaurerP.get outs 0) => />. move => H1. rewrite H1 => |>. have : isL (MaurerP.get outs y). have : valid_local_messages (SMul g) r (MaurerP.get outs y). rewrite H => |>. rewrite /valid_local_messages => |>. rewrite !/ST.P.get !/GT.P.get. case (MaurerP.get outs y) => |>z. rewrite MaurerP.get_init andabP andaP => |>. have : isL (MaurerP.get outs x). have : valid_local_messages (SMul g) r (MaurerP.get outs x). rewrite H => |>. rewrite /valid_local_messages => |>. case (MaurerP.get outs x) => |>w. rewrite MaurerP.get_init andabP andaP => |>. 
    have : ! MaurerP.all (fun (_ : int) => isR) outs. rewrite MaurerP.allP negb_forall => |>. exists 0 => |>. have : valid_local_messages (Const g) r (MaurerP.get outs 0). rewrite H => |>. rewrite /valid_local_messages => />. rewrite /valid_local_messages => />. case (MaurerP.get outs 0) => />. move => H1. rewrite H1 => |>. have : isL (MaurerP.get outs y). have : valid_local_messages (Const g) r (MaurerP.get outs y). rewrite H => |>. rewrite /valid_local_messages => />. rewrite !/ST.P.get !/GT.P.get. case (MaurerP.get outs y) => |>z. rewrite MaurerP.get_init andabP andaP => |>. have : isL (MaurerP.get outs x). have : valid_local_messages (Const g) r (MaurerP.get outs x). rewrite H => |>. rewrite /valid_local_messages => |>. case (MaurerP.get outs x) => |>w. rewrite MaurerP.get_init andabP andaP => |>. 
    have : (MaurerP.all (fun (_ : int) => isR) outs). rewrite MaurerP.allP => |>i Hi1 Hi2. have : valid_local_messages (Mul g) r (MaurerP.get outs i). rewrite H => |>. rewrite /valid_local_messages => |>. move => H1. rewrite H1 => |>. rewrite !/ST.P.get !/GT.P.get MaurerP.get_map => |>. rewrite MaurerP.get_init andabP andaP => |>. rewrite MaurerAPI.get_send_messages => |>. rewrite MaurerP.get_map => |>. have : isR (MaurerP.get outs y). have : valid_local_messages (Mul g) r (MaurerP.get outs y). rewrite H => |>. rewrite /valid_local_messages => |>. case (MaurerP.get outs y) => |>m. rewrite MaurerP.get_init andabP andaP => |>. qed.
    realize valid_pmsgs_from.
    rewrite /valid_local_messages /valid_pmsgs /from_local_messages => |>p r xs. rewrite ST.P.allP => |>. elim p => |>g.
    rewrite /valid_local_messages => |>. case xs => |>x i Hi1 Hi2. rewrite !/ST.P.get !/GT.P.get  MaurerP.get_init andabP andaP => />.  
    rewrite /valid_local_messages => |>. case xs => |>x i Hi1 Hi2. rewrite !/ST.P.get !/GT.P.get MaurerP.get_init andabP andaP => />.  
    rewrite /valid_local_messages => |>. case xs => |>x i Hi1 Hi2. rewrite !/ST.P.get !/GT.P.get MaurerP.get_init andabP andaP => />.  
    rewrite /valid_local_messages => |>. case xs => |>x i Hi1 Hi2. rewrite !/ST.P.get !/GT.P.get MaurerP.get_init andabP andaP => />. qed.
    realize GT.eq_msgP. rewrite /eq_msg => |>m1 m2. case m1 => |>x. case m2 => |>y. case m2 => |>y. qed.
    realize get_local_messages_eqP.
    move => xs ys. rewrite eq_logical => |>. case xs => |>x. case ys => y H. have : MaurerP.get (from_local_messages (L x)) 0 = MaurerP.get (from_local_messages (L y)) 0. rewrite !/ST.P.get !/GT.P.get in H. rewrite H => |>. rewrite /ISet.mem /ISet.iset iset_in_def => />. rewrite /from_local_messages => |>. have : MaurerP.get (from_local_messages (L x)) 0 = MaurerP.get (from_local_messages (R y)) 0. rewrite !/ST.P.get !/GT.P.get in H. rewrite H => |>. rewrite /ISet.mem /ISet.iset iset_in_def => />. rewrite /from_local_messages => |>. rewrite !MaurerP.get_init => />. case ys => y H. have : MaurerP.get (from_local_messages (R x)) 0 = MaurerP.get (from_local_messages (L y)) 0. rewrite !/ST.P.get  !/GT.P.get in H. rewrite H => |>. rewrite /ISet.mem /ISet.iset iset_in_def => />. rewrite /from_local_messages => |>. rewrite !MaurerP.get_init => />.
    congr. rewrite MaurerAPI.eq_msgsP /eq_msgs allP => |>z. rewrite in_iseq => |>Z1 Z2. have : MaurerP.get (from_local_messages (R x)) z = MaurerP.get (from_local_messages (R y)) z. rewrite !/ST.P.get !/GT.P.get in H. rewrite H => |>. rewrite /ISet.mem /ISet.iset iset_in_def => |>. rewrite /from_local_messages => |>. rewrite !MaurerP.get_init !andabP !andaP => |>. qed.
    realize valid_local_messages_to.
    rewrite /valid_pmsgs /valid_local_messages /to_local_messages => />p r xs. rewrite ST.P.allP => />. case p => />p H.
    rewrite /gate_to_local_messages MaurerP.allP => />. have : ! (forall (i : int), 0 <= i < MaurerP.size => isR (MaurerP.get xs i)). rewrite negb_forall => />. exists 0 => />. have : valid_msg (Add p) r (ST.P.get xs 0). rewrite H => />. rewrite /valid_msg => />. rewrite /get /valid_msg => />. case (MaurerP.get xs 0) => />. move => H0. rewrite H0 => />. 
    rewrite /gate_to_local_messages MaurerP.allP => />. have : ! (forall (i : int), 0 <= i < MaurerP.size => isR (MaurerP.get xs i)). rewrite negb_forall => />. exists 0 => />. have : valid_msg (SMul p) r (ST.P.get xs 0). rewrite H => />. rewrite /valid_msg => />. rewrite /get /valid_msg => />. case (MaurerP.get xs 0) => />. move => H0. rewrite H0 => />. 
    rewrite /gate_to_local_messages MaurerP.allP => />. have : ! (forall (i : int), 0 <= i < MaurerP.size => isR (MaurerP.get xs i)). rewrite negb_forall => />. exists 0 => />. have : valid_msg (Const p) r (ST.P.get xs 0). rewrite H => />. rewrite /valid_msg => />. rewrite /get /valid_msg => />. case (MaurerP.get xs 0) => />. move => H0. rewrite H0 => />. 
    rewrite /gate_to_local_messages MaurerP.allP => />. have : (forall (i : int), 0 <= i < MaurerP.size => isR (MaurerP.get xs i)). move => /> i Hi1 Hi2. have : valid_msg (Mul p) r (ST.P.get xs i). rewrite H => />. rewrite /valid_msg => />. rewrite /get /valid_msg => />. qed.

end MaurerGate.

theory MaurerCircuit.

  import MaurerAPI.

  type circuit = MaurerGate.Gate list. 

(* just checks wire ids *)
op valid_gate' (n:int) (g:MaurerGate.Gate) pubs : (iset * bool) =
  with g = MaurerGate.Add x => (pubs,x.`1 = n /\ 0 <= snd3 x /\ snd3 x < n /\ 0 <= thr3 x /\ thr3 x < n)
  with g = MaurerGate.SMul x => (pubs,x.`1 = n /\ 0 <= snd3 x /\ snd3 x < n /\ 0 <= thr3 x /\ thr3 x < n /\ ISet.mem x.`2.`2 pubs)
  with g = MaurerGate.Const x => (ISet.add pubs x.`1,x.`1 = n)
  with g = MaurerGate.Mul x => (pubs,x.`1 = n /\ 0 <= snd3 x /\ snd3 x < n /\ 0 <= thr3 x /\ thr3 x < n). 

op valid_circuit' (n:int) (c:MaurerGate.Gate list) pubs : bool =
  with c = [] => true
  with c = g :: c' =>
    let r = valid_gate' n g pubs in
    r.`2 /\ valid_circuit' (n+1) c' r.`1.

op valid_circuit (x:circuit) n ps : bool =
  0 <= n /\ 0 < n + size x /\ ISet.subset ps (ISet.iset n) /\ valid_circuit' n (x) ps.

op g_pubs (g:MaurerGate.Gate) (pubs:iset) : iset =
  with g = MaurerGate.Add x => pubs
  with g = MaurerGate.SMul x => pubs
  with g = MaurerGate.Const x => ISet.add pubs x.`1
  with g = MaurerGate.Mul x => pubs.

op g_wire (g:MaurerGate.Gate) : int =
  with g = MaurerGate.Add x => x.`1
  with g = MaurerGate.SMul x => x.`1
  with g = MaurerGate.Const x => x.`1
  with g = MaurerGate.Mul x => x.`1.

op check_c_wire (c:MaurerGate.Gate list) (i:int) : bool =
  with c = [] => true
  with c = g :: c' => g_wire g = i /\ check_c_wire c' (i+1).

op c_pubs c (pubs:iset) = foldl (transpose g_pubs) pubs c.

  clone include Circuit with
    theory G = MaurerGate,

    op consistent_inputs (x:circuit) i j (wi wj:wire_st * pub_st) = 
      valid_circuit x (get_wire_st_next wi.`1) wi.`2 /\
      g_valid_share wi /\ g_valid_share wj /\
      consistent_shares i j wi wj.

end MaurerCircuit.

theory MaurerReveal.

  import MaurerAPI.

  clone include Reveal with
    theory M = MaurerCircuit,

    type pub_input = MaurerCircuit.circuit,
    op pub_input_conv (x:pub_input) = x,
    type final_output = val,

    op reveal_local_start _ (ws:MaurerGate.share) = R (output_start ((get_wire_st_next ws.`1)-1) ws.`1),
    op reveal_local_end _ (ins:MaurerGate.local_msgs) = output_end (unR ins),
    op final_valid_local_messages p xs = isR xs,
    op final_valid_msg p xs = isR xs,
    op mpc_consistent_inputs = MaurerCircuit.consistent_inputs,
    op mpc_consistent_outputs (x:MaurerCircuit.circuit) i j (wi wj:wire_st * pub_st) =
      MaurerCircuit.valid_circuit x (get_wire_st_next wi.`1-size x) (ISet.intersect wi.`2 (ISet.iset (get_wire_st_next wi.`1-size x))) /\
      g_valid_share wi /\ g_valid_share wj /\
      consistent_shares i j wi wj,
    op stateful_consistent_outputs x i j oi oj = consistent_vals oi oj.

end MaurerReveal.

