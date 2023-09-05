require import AllCore IntDiv CoreMap List SmtMap FSet.
from Jasmin require import JModel.
require import Array6 Array4.

require import Maurer5SS.

require import Zp25519.
require import Maurer5_jazz_Zp.

require import Maurer5_jazz.

import Maurer5SS.
import Spec.
import PF W64x4 Zp.

lemma add5_correct mem st (cwire wr1 wr2 : int) (wst : wire_st) :
  wst.`1 = cwire =>
  elems (fdom wst.`2) = iota_ 0 cwire =>
  0 <= wr1 < cwire => 0 <= wr2 < cwire =>
   good_wire st cwire =>
   good_wire_shares mem st cwire => 
   wst = lift_state_mem mem st cwire =>
  equiv [ 
   M.add5 ~ MZp.add5 :
   Glob.mem{1} = mem /\ to_uint status{1} = st /\ to_uint curwire{1} = cwire /\
   to_uint w1{1} = wr1 /\ to_uint w2{1} = wr2 /\
   ={arg,Glob.mem} ==> 
   good_wire_shares Glob.mem{1} st (cwire + 1) /\ 
   lift_state_mem Glob.mem{1} st (cwire+1) = add wr1 wr2 wst /\
   touches mem Glob.mem{1} (st+cwire*6*8*4) 6 /\
   ={res,Glob.mem} ].
proof.
move => cwr stdom w1v w2v gw gws lst.
move : gw; rewrite /good_wire /= => gw.

transitivity  M25519.add5  (={arg,Glob.mem} ==> ={res,Glob.mem}) 
   (
   Glob.mem{1} = mem /\ to_uint status{1} = st /\ to_uint curwire{1} = cwire /\
   to_uint w1{1} = wr1 /\ to_uint w2{1} = wr2 /\
   ={arg,Glob.mem} ==> 
   good_wire_shares Glob.mem{1} st (cwire + 1) /\ 
   lift_state_mem Glob.mem{1} st (cwire+1) = add wr1 wr2 wst /\
   touches mem Glob.mem{1} (st+cwire*6*8*4) 6 /\
   ={res,Glob.mem}
   ); 
        [by smt() | by smt() | by apply M25519_add5 |] .

proc.
 sp 5 5; wp.
while (
  #{/~Glob.mem{1} = mem}pre /\ 
   0 <= shareN{1} <= 6 /\ ={shareN, w1, w2, wi} /\
  (forall k, 0<=k< shareN{1} => good_wire_share Glob.mem{1} st cwire k) /\
   touches mem Glob.mem{1} (st+cwire*6*8*4) 6 /\
   (forall k, 0<=k<shareN{1} =>
      load_wire_share Glob.mem{1} st cwire k =
           ( (load_wire_share mem st wr1 k) + (load_wire_share mem st wr2 k))));
        last first.

(****** TERMINATION ************)

wp;skip => /= &1 &2 [#] ????????????????????.

split; first by smt(). 

move =>/= memL?????[#]????????????????????????? gwo tou str.

split; first by smt().
split; last by smt().
move : lst.
rewrite /lift_state_mem /add /=.
have -> : wst = (wst.`1,wst.`2); first by smt().
simplify => [#] wst1 wst2; split; first by smt().
move => *;rewrite wst2.

apply fmap_eqP => x.
case (0<= x < cwire).
move => xb.
rewrite get_set_neqE /=; first by smt().
rewrite /(SmtMap."_.[_]") !ofmapK /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire+1)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota /=; smt(Map.offunE).
exists (iota_ 0 (cwire)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota /=; smt(Map.offunE). 
rewrite !Map.offunE /=.
have -> : (0 <= x && x < cwire + 1); first by smt().
have -> : (0 <= x && x < cwire); first by smt().
simplify.
apply Array6.ext_eq => k kb.
rewrite !initiE /=; first 2 by smt().
rewrite /load_zp.
move : tou; rewrite /touches => tou.
by rewrite -(tou (st + 8 * (24 * x + 4 * k))); smt().

move => *.
case (x = cwire).
move  => xval.
rewrite get_set_eqE; first by smt().
rewrite /(SmtMap."_.[_]") !ofmapK /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire+1)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
exists (iota_ 0 (cwire)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
rewrite !Map.offunE /=.
have -> : (0 <= x && x < cwire + 1); first by smt().
simplify.
rewrite /add_shr map2E.
apply Array6.ext_eq => k kb.
rewrite !initiE /=; first 2 by smt().
move : (str k _); first by smt().
rewrite /load_wire_share xval => ->. 
have -> : (0 <= wr1 && wr1 < cwire); first by smt().
have -> : (0 <= wr2 && wr2 < cwire); first by smt().
by simplify; rewrite !initiE /=; smt().

move => *.
rewrite get_set_neqE /=; first by smt().
rewrite /(SmtMap."_.[_]") !ofmapK /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire+1)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota /=; smt(Map.offunE).
exists (iota_ 0 (cwire)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota /=; smt(Map.offunE). 
rewrite !Map.offunE /=.
smt().

(*************)

exists* Glob.mem{1}, shareN{1}.
elim* => mm k.
wp; call (MZp_add_wrapper mm (st + 8*(24*cwire + 4*k)) (load_wire_share mm st wr1 k) (load_wire_share mm st wr2 k)).
wp;skip => /= &1 &2.
rewrite /good_wire.
move => [#] ???????????????????? shnl shnh ????? gsn mms shnhh ?.
rewrite !to_uintD_small /=; first 3 by rewrite !to_uintM_small /= !to_uintD_small /= !to_uintM_small /= ?of_uintK ?modz_small;  by smt(W64.to_uint_cmp).
rewrite !to_uintM_small; first 3 by rewrite  /= !to_uintD_small /= !to_uintM_small /=  /= ?of_uintK ?modz_small;smt(W64.to_uint_cmp). 
rewrite !of_uintK !modz_small; first  by smt().

rewrite !to_uintD_small /= ; first 3 by  rewrite !to_uintM_small /= ?of_uintK ?modz_small;smt(W64.to_uint_cmp).
rewrite !to_uintM_small; first 9 by rewrite  /= ;smt(W64.to_uint_cmp). 
rewrite !of_uintK !modz_small; first 2  by smt().
by smt().

move => *.
split. 

do 7! (split; first by smt()).
 split.
  move: (gws (to_uint w1S{1}) _ shareN{1} _); smt().
 split.
  move: (gws (to_uint w2S{1}) _ shareN{1} _); smt().
(do split); smt().

move => [#] mmv ???????????? memL memR [#] ?tou memLv memLb.

split; last by smt().
split. 
(do split); smt().
split. 
(do split); smt().
split. 
(do split); smt().
split.
smt().
split.
smt(). 
move=> i Hi.
case: (i = shareN{1}) => Hi'.
 by rewrite {1}/load_wire_share (_:i=k) 1:/# memLv /#.
rewrite -(shnhh i _) 1:/# /load_wire_share /load_zp -tou 1:/#; congr.
smt().
qed.
