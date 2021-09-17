require import AllCore Int List Distr DList.
require import Aux AuxList.
require import FSet AuxFSet.
require import SmtMap AuxSmtMap.
require import Maurer5Spec.
require import Maurer5SS.
require import NextMsgISet NextMsgIMap NextMsgMaurerP NextMsgArray.
require import Array5 Array6 Array9 Array10.
import ISet IMap Array.

theory MaurerAPI.

  import Maurer5Spec.
  import Maurer5SS.
  

  type shr = Maurer5SS.shr. (* TO DEFINE *)
  type shrs = Maurer5SS.shrs. (* TO DEFINE *)
  type val = Maurer5SS.val. (* TO DEFINE *)
  type rshr = val.
  type msg = shr.
  type msgs = Maurer5SS.shrs.
  type wid = int.
  type wire_st = Maurer5Spec.wire_st.  (* TO DEFINE *)
  type pid = int.
  type rand = Maurer5SS.rand.  (* TO DEFINE *)

  op mkwire_st (p:pid) (i:int) (xs:shr IMap.imap) : wire_st = (i,xs).

  op gen_party_rand : rand distr = Maurer5SS.gen_rand.
  op gen_parties_rand : (rand list) distr =
    dlist gen_party_rand 5.

  op val_to_bool (v:val) : bool = (v = fzero).

  (* wire_st *)
  op get_wire_st_next (st:wire_st) : wid = fst (st).

  op get_wire_st_shr (st : wire_st) (w : wid) : shr = (oget st.`2.[w]).

  op get_wire_st_fdom (st : wire_st) : iset = (fdom (st).`2).

  (* Secret Sharing *)
  op get_rshr (s:shr) (i:int) : rshr = s.[i].

  op party_pshare (i:pid) (v:val) : shr = (Maurer5SS.pshare (v)).[i].

  op check_pshare (i:pid) (ss:shr) : bool = (ss = party_pshare i (get_rshr ss 0)).

  op party_unpshare (ss:shr) : val = get_rshr ss 0.

  op unshare (ss:shrs) : val = (Maurer5SS.unshare (ss)).

  op mk_shares (ss:shr MaurerP.arrayN) : shrs = (Array5.init (fun i => (MaurerP.get ss i))).
  op mk_msgs (ss:msg MaurerP.arrayN) : msgs = (Array5.init (fun i => (MaurerP.get ss i))).

  op shr_idx (i:pid) : int array6 = list_to_array6 (Maurer5SS.shr_idx i).

  op get_shr (ss:shrs) (i:int) : shr = ((ss).[i]).

  op get_msg (ss:msgs) (i:int) : msg = ((ss).[i]).

  op share (s : val) (r : rand) : shrs = (Maurer5SS.share (s) (r)).

  op add(wi wj : wid, wst : wire_st) : wire_st = (Maurer5Spec.add wi wj (wst)).

  op smul (wi : wid) (wc : wid)(wst : wire_st) : wire_st = (Maurer5Spec.smul wi wc (wst)).

  op cnst (i:pid) (v:val) (st:wire_st) : wire_st = (Maurer5Spec.cnst i (v) (st)).

  op mul_start (wi wj : wid) (wst : wire_st) (r : rand) : msgs = (Maurer5Spec.mul_start wi wj (wst) (r)).

  op mul_end (ms : msgs) (wst : wire_st) : wire_st = (Maurer5Spec.mul_end (ms) (wst)).

  op output_start (wid:wid) (st : wire_st) :  msgs = (Maurer5Spec.output_start wid (st)).

  op output_end (ms : msgs) : val = (Maurer5Spec.output_end (ms)).

  op reconstruct_shrs (v:val) (cr:shr imap): shrs = (Maurer5Spec.reconstruct_shrs (v) ( (cr))).

  op send_messages (ins:msgs MaurerP.arrayN) : msgs MaurerP.arrayN = MaurerP.init (fun i => (Array5.init (fun j => ((MaurerP.get ins j)).[i])) ).

  op eq_msg (m1 m2: msg) : bool = (m1 = m2).

  op eq_msgs (m1 m2 : msgs) : bool =
    all (fun i => eq_msg (get_msg m1 i) (get_msg m2 i) ) (iseq 5).
  op eq_rmsgs (m1 m2 : msg array) : bool =
    size m1 = size m2 /\ all (fun i => eq_msg (get m1 i) (get m2 i) ) (iseq (size m1)).

  op shrs_to_msgs : shrs -> msgs = fun ss =>
    mk_msgs (MaurerP.init (fun i => get_shr ss i)).
  op msgs_to_shrs : msgs -> shrs = fun ms =>
    mk_shares (MaurerP.init (fun i => get_msg ms i)).

  lemma shrs_to_msgs_id ss :
    shrs_to_msgs ss = ss.
    rewrite /shrs_to_msgs /mk_msgs /get_shr => />. rewrite Array5.tP => />i Hi1 Hi2. rewrite Array5.initE andabP andaP => />. rewrite MaurerP.get_init andabP andaP => />. qed.

  lemma msgs_to_shrs_id ss :
    msgs_to_shrs ss = ss.
    rewrite /msgs_to_shrs /mk_shrs /get_msg => />. rewrite Array5.tP => />i Hi1 Hi2. rewrite Array5.initE andabP andaP => />. rewrite MaurerP.get_init andabP andaP => />. qed.

(* need to keep which wires are public for validity checking *)
  type pub_st = iset.
  type g_sec = wid * val imap.

  op g_unshare (xs:(wire_st * pub_st) MaurerP.arrayN) : g_sec =
      let pivot = (MaurerP.get xs 0).`1 in
      let unshr = fun wid =>
        let shares = MaurerP.map (fun (x:wire_st * pub_st) => get_wire_st_shr x.`1 wid) xs in
        unshare (mk_shares shares) in
      (get_wire_st_next pivot,IMap.ofset unshr (get_wire_st_fdom pivot)).

  op add_val (v1 v2 : val) : val = (fadd (v1) (v2)).

  op mul_val (v1 v2 : val) : val = (fmul (v1) (v2)).

  op zero_val : val = fzero.

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
  val_to_bool v1 && val_to_bool v2.

  lemma mk_msgs_id xs :
    mk_msgs ((MaurerP.init (get_msg xs))) = xs.
    rewrite /mk_msgs => |>. 
    rewrite Array5.tP => |>i Hi1 Hi2.
    rewrite Array5.initE andabP andaP => |>. rewrite MaurerP.get_init /get_msg andabP andaP => |>. qed.

  lemma mk_msgs_id' xs ys :
    ys = (MaurerP.init (get_msg xs)) =>
    mk_msgs ys = xs.
    progress. rewrite mk_msgs_id => |>*. qed.

  lemma mk_shares_id xs :
    mk_shares ((MaurerP.init (get_shr xs))) = xs.
    rewrite /mk_shares => |>. 
    rewrite Array5.tP => |>i Hi1 Hi2.
    rewrite Array5.initE andabP andaP => |>. rewrite MaurerP.get_init /get_shr andabP andaP => |>. qed.

  lemma mk_shares_id' xs ys :
    ys = (MaurerP.init (get_shr xs)) =>
    mk_shares ys = xs.
    progress. rewrite mk_shares_id => |>*. qed.

  lemma get_mk_msgs xs i :
    0 <= i /\ i < 5 =>
    get_msg (mk_msgs xs) i = (MaurerP.get xs i).
    rewrite /get_msg /mk_msgs => |>Hi1 Hi2. rewrite Array5.initE andabP andaP => |>. qed.

  lemma get_mk_shares xs i :
    0 <= i /\ i < 5 =>
    get_shr (mk_shares xs) i = (MaurerP.get xs i).
    rewrite /get_shr /mk_shares => |>Hi1 Hi2. rewrite Array5.initE andabP andaP => |>. qed.

  lemma get_send_messages outs x y :
    0 <= x /\ x < 5 =>
    0 <= y /\ y < 5 =>
    get_msg (MaurerP.get (send_messages outs) x) y = get_msg (MaurerP.get outs y) x.
    rewrite /get_msg /send_messages => |>X1 X2 Y1 Y2. rewrite !MaurerP.get_init andabP andaP => |>. rewrite Array5.initE andabP andaP => |>. qed.

  lemma eq_msgsP m1 m2 :
    (m1 = m2) = eq_msgs m1 m2.
    rewrite /eq_msgs allP => |>. rewrite eq_logical. split. move => H x. rewrite in_iseq => |>H1 H2. rewrite H. rewrite /eq_msg => |>. 
    move => H. rewrite -(mk_msgs_id m1) -(mk_msgs_id m2). congr. 
    rewrite MaurerP.tP => |>i Hi1 Hi2. rewrite !MaurerP.get_init !andabP !andaP => |>. rewrite H => />. rewrite in_iseq => />. qed.

end MaurerAPI.
