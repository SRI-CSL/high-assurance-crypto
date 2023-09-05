require import AllCore Int List Distr Ring.
require import Aux AuxList.
require import NextMsgArray NextMsgFixedArray NextMsgISet NextMsgIMap.
require import NextMsgMaurerP.

import ISet IMap Array.

theory MaurerAPI.

  type shr. (* TO DEFINE *)
  type shrs. (* TO DEFINE *)
  type val. (* TO DEFINE *)
  type rshr = val.
  type msg = shr.
  type msgs. (*TO DEFINE *)
  type wid = int.
  type wire_st.  (* TO DEFINE *)
  type pid = int.
  type rand.  (* TO DEFINE *)

  op mkwire_st : pid -> int -> shr IMap.imap -> wire_st.

  op gen_party_rand : rand distr.
  op gen_parties_rand : (rand list) distr =
    djoin [gen_party_rand;gen_party_rand;gen_party_rand;gen_party_rand;gen_party_rand].

  op val_to_bool (v:val) : bool.

  (* wire_st *)
  op get_wire_st_next : wire_st -> wid.
  op get_wire_st_shr (st : wire_st) (w : wid) : shr.
  op get_wire_st_fdom (st : wire_st) : iset.

  (* Secret Sharing *)
  op get_rshr (s:shr) (i:int) : rshr.
  op party_pshare (i:pid) (v:val) : shr.
  op check_pshare (i:pid) (ss:shr) : bool.
  op party_unpshare (ss:shr) : val.
  op unshare : shrs -> val.
  op mk_shares (ss:shr MaurerP.arrayN) : shrs.
  op mk_msgs (ss:msg MaurerP.arrayN) : msgs.
  op shr_idx (i:pid) : int array6.
  op get_shr (ss:shrs) (i:int) : shr.
  op get_msg (ms:msgs) (i:int) : msg.
  op share (s : val) (r : rand) : shrs.
  op reconstruct_shrs (v:val) (cr:shr imap): shrs.
  
  (* Secure computation*)
  op add(wi wj : wid, wst : wire_st) : wire_st.
  op smul (wi : wid) (wc : wid)(wst : wire_st) : wire_st.
  op cnst (i:pid) (v:val) (st:wire_st) : wire_st.
  op mul_start (wi wj : wid) (wst : wire_st) (r : rand) : msgs.
  op mul_end (ms : msgs) (wst : wire_st) : wire_st.
  op output_start (wid:wid) (st : wire_st) :  msgs.
  op output_end (ms : msgs) : val.
  op send_messages (ins:msgs MaurerP.arrayN) : msgs MaurerP.arrayN.

  op eq_msg : msg -> msg -> bool.

  op eq_msgs (m1 m2 : msgs) : bool =
    all (fun i => eq_msg (get_msg m1 i) (get_msg m2 i) ) (iseq 5).

  op shrs_to_msgs : shrs -> msgs = fun ss =>
    mk_msgs (MaurerP.init (fun i => get_shr ss i)).
  op msgs_to_shrs : msgs -> shrs = fun ms =>
    mk_shares (MaurerP.init (fun i => get_msg ms i)).
    
(* need to keep which wires are public for validity checking *)
  type pub_st = iset.
  type g_sec = wid * val imap.

  op g_unshare (xs:(wire_st * pub_st) MaurerP.arrayN) : g_sec =
      let pivot = (MaurerP.get xs 0).`1 in
      let unshr = fun wid =>
        let shares = MaurerP.map (fun (x:wire_st * pub_st) => get_wire_st_shr x.`1 wid) xs in
        unshare (mk_shares shares) in
      (get_wire_st_next pivot,IMap.ofset unshr (get_wire_st_fdom pivot)).

  op add_val : val -> val -> val.
  op mul_val : val -> val -> val.
  op zero_val : val.

  op g_valid_share (s:wire_st * pub_st) : bool =
  0 <= get_wire_st_next s.`1 /\ 
  (* all wires up to the next wire must be defined *)
  ISet.equal (get_wire_st_fdom s.`1) (ISet.iset (get_wire_st_next s.`1)) /\
  (* public wires should be defined *)
  ISet.subset s.`2 (get_wire_st_fdom s.`1).

  op add_valid_share (wij:wid*(wid*wid)) (s:wire_st * pub_st) : bool =
  g_valid_share s /\
  (* destination wire should be next wire *)
  wij.`1 = get_wire_st_next s.`1 /\
  (* used wires must be defined *)
  ISet.mem wij.`2.`1 (get_wire_st_fdom s.`1) /\ ISet.mem wij.`2.`2 (get_wire_st_fdom s.`1).

  op smul_valid_share (wij:wid*(wid*wid)) (s:wire_st * pub_st) : bool =
  add_valid_share wij s /\ ISet.mem wij.`2.`2 s.`2.

  op const_valid_share (wij:wid*val) (s:wire_st * pub_st) : bool =
  g_valid_share s /\
  (* destination wire should be next wire *)
  wij.`1 = get_wire_st_next s.`1.
  
op consistent_pub_shares i j (p1 p2 : shr) : bool =
  check_pshare i p1 /\ check_pshare j p2 /\ party_unpshare p1 = party_unpshare p2.

op raw_shares (i:pid) (s:shr) : rshr imap =
  foldl_iseq (fun  (m:rshr imap) k => let j = nth_array6 (shr_idx i) k in IMap.set m j (get_rshr s k) ) IMap.empty 6.

op consistent_raw_shares (i j:pid) (s1 s2 : shr) : bool =
  IMap.all (fun _ (xy:_*_) => xy.`1 = xy.`2) (IMap.zip (raw_shares i s1) (raw_shares j s2)).

op valid_raw_shares (ss:shrs) : bool =
  forall i j, 0 <= i /\ i < 5 /\ 0 <= j /\ j < 5 => consistent_raw_shares i j (get_shr ss i) (get_shr ss j).

op consistent_shares i j (s1 s2 : wire_st * pub_st) : bool =
  (* same next wire *)
  get_wire_st_next s1.`1 = get_wire_st_next s2.`1 /\
  (* same defined wires *)
  get_wire_st_fdom s1.`1 = get_wire_st_fdom s2.`1 /\
  (* same public wires *)
  s1.`2 = s2.`2 /\
  (* publicly-tagged shares must be sharings of the same public value *)
  ISet.all (fun wid => consistent_pub_shares i j (get_wire_st_shr s1.`1 wid) (get_wire_st_shr s2.`1 wid)) s1.`2 /\
  (* redundant raw shares must be consistent among different shares *)
  all_iseq (fun wid => consistent_raw_shares i j (get_wire_st_shr s1.`1 wid) (get_wire_st_shr s2.`1 wid)) (get_wire_st_next s1.`1).

op consistent_vals (v1 v2 : val) : bool =
  val_to_bool v1 = val_to_bool v2.

end MaurerAPI.
