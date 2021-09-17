require import AllCore IntDiv CoreMap List SmtMap FSet.
from Jasmin require import JModel.
require import Array10 Array9 Array6 Array5 Array4.

require import Maurer5SS.

require import Zp25519.
require import Maurer5_jazz_Zp.

require import Maurer5_jazz.

import Spec Maurer5SS.

import Zp W64x4.

lemma MZp_copy_share mem outp inp shr:
equiv [
   M25519.copy_share ~ MZp.copy_share:
     separate outp (4*8) inp (4*8) /\
     outp + 4*8 <= 18446744073709551616 /\
     inp + 4*8 <= 18446744073709551616 /\
     inbounds (load_array mem inp) /\
     shr = load_zp mem inp /\
     mem = Glob.mem{1} /\ 
     to_uint out{1} = outp /\ to_uint in_0{1} = inp /\
     ={arg,Glob.mem} ==> 
     ={res,Glob.mem} /\
     load_zp Glob.mem{1} outp = shr /\
     inbounds (load_array Glob.mem{1} outp) /\
     touches mem Glob.mem{1} outp 1
   ].
proc.
while (#{/~mem = Glob.mem{1}}pre /\ ={i} /\ 0 <= i{1} <= 4 /\
       touches mem Glob.mem{1} outp  1 /\
       (forall k, 0<=k<i{1} => loadW64 Glob.mem{1} (outp + k*8) = 
                               loadW64 mem (inp + k*8))); last first.
wp; skip => /= &1 &2 [#]spp??ibb ls ??????.


split; first by smt().
move => mL?????[#]????????????? pres vv; rewrite /load_zp.

have -> : load_array mL outp = load_array mem inp. 
   rewrite /load_array /=; apply Array4.ext_eq => x xb.
   rewrite !initiE /=;  by smt(). 

by smt().

wp; skip => /= &1 &2 [#]spp??ibb ls ov iv?????? pr vl ??.

split; last by smt().

do split; first 14 by smt().

move : pr; rewrite /touches => tou a sep.
rewrite tou; first by smt().
rewrite /load_array.
rewrite Array4.tP => x xb.
rewrite !initiE /=; first 2 by smt(). 
rewrite !to_uintD_small; first 2 by smt(@W64). 
rewrite !of_uintK !modz_small;  first  by smt(@W64). 
by rewrite load_store_W64_neq;  smt().

move => k kb.

rewrite !to_uintD_small; first 2 by smt(@W64).
rewrite !of_uintK !modz_small;  first by smt(@W64).

case (k = i{1}); last first.

by move => *; rewrite -vl; smt(load_store_W64_neq).
move => ->; rewrite ov -iv load_store_W64_eq. 
move : pr; rewrite /touches => tou.
move : spp (tou inp _); rewrite /separate => sep.
smt().
rewrite /load_array Array4.tP /=.
move => pres; move :(pres i{1}_); first by smt(). 
by rewrite !initiE /=;  smt().
qed.


lemma mu_end_correct mem st cwire (wst : wire_st) inp msgs:
  wst.`1 = cwire =>
  elems (fdom wst.`2) = iota_ 0 cwire =>
   good_wire st (cwire+1) =>
   good_wire_shares mem st cwire => 
   wst = lift_state_mem mem st cwire =>
   good_wire inp 6 =>
   good_wire_shares mem inp 6 => 
   lift_msgs (load_msgs mem inp) = msgs =>
   separate (st+cwire*6*4*8) (6*4*8) inp (6*5*4*8) =>
  equiv [ 
   M.mult_end5 ~ MZp.mult_end5 :
   Glob.mem{1} = mem /\ to_uint status{1} = st /\ to_uint curwire{1} = cwire /\
   to_uint all_messages{1} = inp /\ 
   ={arg,Glob.mem} ==> 
   good_wire_shares Glob.mem{1} st (cwire + 1) /\ 
   lift_state_mem Glob.mem{1} st (cwire+1) = mul_end msgs wst /\
   touches mem Glob.mem{1} (st+(cwire*6*4*8)) 6 /\
   ={res,Glob.mem} ].
proof.
move => cw mdom gw gws lst iw iws lsmsgs sep.

transitivity  M25519.mult_end5  (={arg,Glob.mem} ==> ={res,Glob.mem}) 
   (
   Glob.mem{1} = mem /\ to_uint status{1} = st /\ to_uint curwire{1} = cwire /\
   to_uint all_messages{1} = inp /\ 
   ={arg,Glob.mem} ==> 
   good_wire_shares Glob.mem{1} st (cwire + 1) /\ 
   lift_state_mem Glob.mem{1} st (cwire+1) = mul_end msgs wst /\
   touches mem Glob.mem{1} (st+(cwire*6*4*8)) 6 /\
   ={res,Glob.mem}   ); 
        [by smt() | by smt() | by apply M25519_mult_end5 |] .

proc. inline M.getWireIndex5.

seq 11 11 : (#pre /\ ={messages,wire,wiS} /\ to_uint wiS{1} = cwire /\
           to_uint wire{1} = st+cwire*6*4*8 /\
           to_uint messages{1} = inp).
 wp;skip =>  /= &1 &2 [#] ????????.
do split. smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
move : gw; rewrite /good_wire /= => *.
smt(). 
rewrite !to_uintD_small /=. 
   rewrite !to_uintM_small /=; smt. 
   rewrite !to_uintM_small /=; smt. 
smt().

seq 3 3 : (#{/~Glob.mem{1}=mem}pre /\ 
           touches mem Glob.mem{1} (st+(cwire*6*4*8)) 6 /\
           (forall k, 0 <= k < 6 => load_zp Glob.mem{1} (st+(cwire*6*4*8) + k*4*8) = 
                                    load_zp mem (inp + k*4*8)) /\
           (forall k, 0 <= k < 6 => inbounds (load_array Glob.mem{1} (st+(cwire*6*4*8)+ k*4*8)))
           ).
while (#{/~Glob.mem{1}=mem}pre /\ 0 <= i{1} <= 6 /\ ={i, message} /\ message{1} = messages{1} /\
           touches mem Glob.mem{1} (st+(cwire*6*4*8)) 6 /\
           (forall k, 0 <= k < i{1} => load_zp Glob.mem{1} (st+(cwire*6*4*8) + k*4*8) = 
                                    load_zp mem (inp + k*4*8)) /\
           (forall k, 0 <= k < i{1} => inbounds (load_array Glob.mem{1} (st+(cwire*6*4*8)+ k*4*8)))
           ); last by wp; skip; smt().
seq 6 6 : (#pre /\ ={sumShare,val} /\ 
         to_uint sumShare{1} = st + cwire * 6 * 4 * 8 + i{1}*32 /\
         to_uint val{1} = inp + i{1} * 32).
wp;skip => /= &1 &2 [#] ???????????wv iv????ivv?????.
rewrite !to_uintD_small.
rewrite !of_uintK !modz_small; first  by smt(@W64).
by rewrite wv; move : gw; rewrite /good_wire /= /#. 
rewrite !of_uintK !modz_small /=; first  by smt(@W64).
by move : iw; rewrite ivv iv /good_wire /= /#. 
rewrite !of_uintK !modz_small /=; first  by smt(@W64).
by smt().

exists *Glob.mem{1}, i{1}.
elim* => mm ii.

wp; call (MZp_copy_share mm (st + cwire * 6 * 4 * 8 + ii*32) (inp + ii*32) (msgs.[0].[ii])).
skip => /= &1 &2 [#] mmv ???????????????????tou????????.

split. 

do split; last 6 by smt().
move : sep; rewrite /separate /=.  smt(). 
move : gw; rewrite /good_wire;smt(). 
move : iw; rewrite /good_wire;smt().
move : tou; rewrite /touches => tou.
rewrite mmv -tou; first by smt().
move : iws; rewrite /good_wire_shares /inbounds => iws. 
move : (iws 0 _ ii _); smt().
move : iws; rewrite /good_wire_shares /inbounds => iws. 
move : (iws 0 _ ii _); smt().
move : tou; rewrite /touches => tou.
rewrite /load_zp mmv -tou; first by smt().
move : lsmsgs; rewrite /lift_msgs /load_msgs => <-.
rewrite initiE /=; first by smt().
rewrite initiE /=; first by smt().
rewrite initiE /=; first by smt().
smt().

move => [#] ?????????????[#] ????.
do split; [1..19 :by smt()].
move => k kb.
case (k = i{1}); last by smt().
move => ->. smt(). smt(). smt(). smt().

seq 2 2 : (#{/~(forall (k : int),
     0 <= k && k < 6 => load_zp Glob.mem{1} (st + cwire * 6 * 4 * 8 + k * 4 * 8) = load_zp mem (inp + k * 4 * 8))}pre /\ 0<=p{1}<=5 /\ ={p} /\
      (forall (k : int),
     0 <= k && k < 6 => 
        load_zp Glob.mem{1} (st + cwire * 6 * 4 * 8 + k * 4 * 8) = 
           foldl (fun acc (p : int) => 
              acc + (load_zp mem (inp + p*6*4*8 + k * 4 * 8))) (Zp.inzp 0) (iota_ 0 5)));
     last first.

(* Termination *)

wp;skip => &1 &2 [#] ?????????????tou rng???vv.

do split.

rewrite /good_wire_shares => w wb k kb.
case (w=cwire); last by smt().
move => ->.
move : (rng k kb); smt().

move : lst; rewrite /lift_state_mem /mul_end => /=.
have -> : (wst = (wst.`1,wst.`2)); first by smt().
simplify => /= [#] wst1 wst2.

split; first by smt().
move => *.
rewrite wst2 /=.


apply fmap_eqP => x.

rewrite /(SmtMap."_.[_]") !ofmapK /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire+1)).
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
exists (iota_ 0 (cwire)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE).

rewrite /(SmtMap."_.[_]")  /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire+1)). 
split; first by smt(iota_uniq).
move => xx.
rewrite mema_iota /=. 
split. move => /= /> * . 
rewrite Map.get_setE /=.
case (xx = wst.`1) => ?; first by done.
by rewrite Map.offunE /= /#.
case (0 <= xx && xx < cwire + 1); first by smt().
move => xb.
rewrite Map.get_set_neqE; first by smt(@W64).
rewrite Map.offunE /=. smt().
exists (iota_ 0 (cwire)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE).

case (0<= x < cwire) => xb.
move => *. 
rewrite Map.get_set_neqE; first by smt().
rewrite !Map.offunE /=.
rewrite xb.
have -> : 0 <= x && x < cwire + 1; first by smt().
simplify.
apply Array6.ext_eq => *. 
rewrite !initiE /=; first 2 by smt(). 
by smt().

case (x = cwire). 
move => ->.
have -> : (wst.`1 = cwire); first by smt().
rewrite Map.get_set_eqE; first  by smt().
rewrite !Map.offunE /=.
have -> : 0 <= cwire && cwire < cwire + 1; first by smt(@W64).
simplify.
apply Array6.ext_eq => xx xxb. 
rewrite /add_shr /map2 /= !initiE /=; first 2 by smt(). 
have -> : (st + 8 * (24 * cwire + 4 * xx)) = st + cwire * 6 * 4 * 8 + xx * 4 * 8; first by smt().
rewrite (vv xx); first by smt().
rewrite -iotaredE /=.
rewrite !initiE /=; first  by smt().
rewrite !initiE /=; first  by smt().
rewrite !initiE /=; first  by smt().
rewrite - lsmsgs; rewrite /load_msgs /lift_msgs /load_zp/=. 
rewrite !initiE /=; first 5 by smt().
rewrite !initiE /=; first 5 by smt().
have -> : inp + xx * 4 * 8 = inp + 32 * xx; first by smt().
have -> : inp + 192 + xx * 4 * 8 = inp + 192 + 32 * xx; first by smt().
have -> : inp + 384 + xx * 4 * 8 = inp + 384 + 32 * xx; first by smt().
have -> : inp + 576 + xx * 4 * 8 = inp + 576 + 32 * xx; first by smt().
have -> : inp + 768 + xx * 4 * 8 = inp + 768 + 32 * xx; first by smt().
by ring.

by smt(@Map).
by smt().
move : gw; rewrite /good_wire /=. by smt(@W64).
smt(). 



(** Preservation **)

while (#{/~(forall (k : int),
     0 <= k && k < 6 => load_zp Glob.mem{1} (st + cwire * 6 * 4 * 8 + k * 4 * 8) = load_zp mem (inp + k * 4 * 8))}pre /\ 0<=p{1}<=5 /\ ={p} /\
      (forall (k : int),
     0 <= k && k < 6 => 
        load_zp Glob.mem{1} (st + cwire * 6 * 4 * 8 + k * 4 * 8) = 
           foldl (fun acc (p : int) => 
              fadd acc (load_zp mem (inp + p*6*4*8 + k * 4 * 8))) (Zp.inzp 0) (iota_ 0 p{1})));
     last first.

wp;skip; move => /= &1 &2 [#] ??????????????vv bb.

split.

do split; first 14 by smt().
smt(). 
rewrite -iotaredE /=.
move => k kb; rewrite (vv k kb).  (*by ring.*) smt.

move => mL pL????[#]??????????????????vvv. 

do split; first 17 by smt(). smt().
move => k kb; rewrite (vvv k kb).
have -> : pL = 5; first by smt(). 
rewrite -iotaredE /=.
done.

seq 5 5 : (#pre /\ ={message} /\ to_uint message{1} = inp + p{1}*6*4*8).
wp;skip;move => /= &1 &2 [#] ????????????mv?????vv??. 
do split; first 17 by smt(). smt().
apply vv. smt(). smt(). smt(). 
rewrite to_uintD_small. rewrite of_uintK modz_small /=. smt(@W64). 
rewrite mv. move : iw; rewrite /good_wire /=. smt(). 
rewrite of_uintK modz_small /=. smt(@W64).  smt().

wp.
while(#{/~forall (k : int),
      0 <= k && k < 6 =>
      load_zp Glob.mem{1} (st + cwire * 6 * 4 * 8 + k * 4 * 8) =
      foldl (fun (acc : t) (p0 : int) => fadd acc (load_zp mem (inp + p0 * 6 * 4 * 8 + k * 4 * 8))) ((
        Zp.inzp 0))%PF (iota_ 0 p{1})}pre /\ 
    ={i} /\ 0<=i{1}<=6 /\
    (forall (k : int),
      0 <= k && k < i{1} =>
      load_zp Glob.mem{1} (st + cwire * 6 * 4 * 8 + k * 4 * 8) =
      foldl (fun (acc : t) (p0 : int) => fadd acc (load_zp mem (inp + p0 * 6 * 4 * 8 + k * 4 * 8))) ((
        Zp.inzp 0))%PF (iota_ 0 (p{1}+1))) /\
   (forall (k : int),
      i{1} <= k && k < 6 =>
      load_zp Glob.mem{1} (st + cwire * 6 * 4 * 8 + k * 4 * 8) =
      foldl (fun (acc : t) (p0 : int) => fadd acc (load_zp mem (inp + p0 * 6 * 4 * 8 + k * 4 * 8))) ((
        Zp.inzp 0))%PF (iota_ 0 p{1}))
   ); last first.

wp;skip => /= &1 &2 [#]??????????????????vv????.

split.

do split; first 22 by smt(). smt().
apply vv.

move => mL auxL iL ???[#]?????????????????????????vv1 vv2. 

do split; first 17 by smt(). smt().

move => k kb.
rewrite (vv1 k _);  by smt().
smt(). smt().

seq 8 8 : (#pre /\ ={valS,sumShareS} /\ 
   to_uint valS{1} = inp + p{1} * 6 * 4 * 8 + i{1} * 4 * 8 /\
   to_uint sumShareS{1} = st + cwire * 6 * 4 * 8 + i{1} * 4 * 8).
wp;skip => &1 &2 [#] ?????????????????????????v1 v2????vs vss.

do split; [1.. 25: by smt()].
apply v1.
apply v2.
smt().
smt().
smt().
smt().
rewrite /vs to_uintD_small; last by smt(@W64).
    rewrite of_uintK modz_small /=. smt(). move : iw; rewrite /good_wire; smt().
rewrite /vs to_uintD_small; last by smt(@W64).
    rewrite of_uintK modz_small /=. smt(). move : gw; rewrite /good_wire; smt().

exists* Glob.mem{1}, (st + cwire * 6 * 4 * 8 + i{1} * 4 * 8),
         (load_zp mem (inp + p{1} * 6 * 4 * 8 + i{1} * 4 * 8)),
         (foldl (fun (acc : t) (p0 : int) => fadd acc (load_zp mem (inp + p0 * 6 * 4 * 8 + i{1} * 4 * 8))) ((
        Zp.inzp 0))%PF (iota_ 0 p{1})).
elim* => mm ares _v1 _v2.
wp;call (MZp_add_wrapper mm ares _v1 _v2).

skip => /= &1 &2 [#] mv av v1 v2 ?????????????tou???????????vv1 vv2 ????vv vs.

split. 

do split; first 3 by smt().
rewrite vs v2. apply vv2; smt().
move : iw; rewrite /good_wire;smt().
move : gw; rewrite /good_wire;smt().
move : gw; rewrite /good_wire;smt().
   move : tou;rewrite /touches => tou.
   rewrite vv -tou.  smt(). 
   smt(R.bnk_cmp).
   move=> _.
   move : (iws p{1} _ i{1} _); smt().
move => *.
   smt(R.bnk_cmp).
   move=> _.
   move : (iws p{1} _ i{1} _); smt().
smt().
smt().
smt(). smt().
move => /= [#] mmv aav ?????????????[#]?ttou lv?.

do split; first 24 by smt(). smt().

move => k kb.
case (k = i{1}).
move => ->.
rewrite -vs -aav lv v1 v2.
rewrite iota_add /=.  smt(). done.
rewrite iota1 foldl_cat /=.
by ring.

move => *. 
move : ttou; rewrite /touches => ttou.
rewrite /load_zp -ttou. smt().
rewrite mmv. apply vv1. smt().

move => k kb.
move : ttou; rewrite /touches => ttou.
rewrite /load_zp -ttou. smt().
rewrite mmv; apply vv2. smt().
smt(). smt().
qed.


lemma MZp_create_sharing mem outp rndp rI rsum:
equiv [
   M25519.create_sharing ~ MZp.create_sharing :
   separate outp 960 rndp (9*4*8) /\
   outp + 960 < 18446744073709551616 /\
   rndp + 9*4*8 < 18446744073709551616 /\
   (forall (k : int), 0 <= k && k < 9 => inbounds (load_rnd mem rndp).[k]) /\
   rI = lift_rnd (load_rnd mem rndp) /\
   rsum = load_zp mem (outp + 4*8) /\
   inbounds (load_array mem (outp + 4*8)) /\
   mem = Glob.mem{1} /\ 
   to_uint outS{1} = outp /\ to_uint randomnessS{1} = rndp /\
   ={arg,Glob.mem} ==> 
   ={res,Glob.mem} /\
   (forall (k : int),
     0 <= k && k < 30 =>
     load_zp Glob.mem{1} (outp + 8 * 4 * k) =
     if nth witness sharing_idx k < 9 then rI.[nth witness sharing_idx k]
     else rsum) /\
      (forall (k j : int), 0 <= k && k < 5 => 0 <= j && j < 6 => inbounds (load_msgs Glob.mem{1} outp).[k].[j]) /\
    touches mem Glob.mem{1} outp 30
   ].
proof.
proc.
sp 2 2.
seq 6 6 :  (#{/~mem=Glob.mem{1}}pre /\ ={out,i} /\ 
             2<=i{1}<=30 /\ (i{1} < 30 => to_uint out{1} = outp + 8*4*i{1}) /\
  (forall (k : int),
     0 <= k && k < i{1} =>
     load_zp Glob.mem{1} (outp + 8 * 4 * k) =
     if nth witness sharing_idx k < 9 then rI.[nth witness sharing_idx k]
     else rsum) /\
  (forall (k j : int), 0 <= k && k < 5 => 0 <= j && j < 6 => 6*k+j < i{1} => inbounds (load_msgs Glob.mem{1} outp).[k].[j]) /\
   touches mem Glob.mem{1} outp 30).

 wp; call (MZp_copy_share mem (outp) (rndp+5*8*4) (rI.[5])). 

wp;skip => /= &1&2 [#] ???????rndb rIv????????. 
rewrite !to_uintD_small; first 2 by smt().
split.
do split; [1..3: by smt()]. 
move : (rndb 5 _); first by smt().
by rewrite /load_rnd;smt().
move : (rndb 5 _); first by smt().
by rewrite /load_rnd;smt().
by rewrite rIv /load_rnd /lift_rnd  /load_zp initiE /=; smt(). 
smt(). smt().  smt(). smt(). smt(). smt().
move => /= [#] ?????????????[#]????.
do split; [1.. 18: by smt()].
move => k j kb jb. 
rewrite /load_messages. 
case (k=0 /\ j=0).
move => *; rewrite /inbounds !initiE /=; first  smt().
rewrite !initiE /=;   smt().
case (k=0 /\ j=1).
move => *; rewrite /inbounds !initiE /=; first  smt().
rewrite !initiE /=;   smt().
smt().

smt().

while (#pre); last by wp;skip;smt().

exists * Glob.mem{1}, (outp + 4*8*i{1}), (if (nth witness sharing_idx i{1} = 9) then outp+32 else rndp + (nth witness sharing_idx i{1})*32).
elim* => mm oo ii.

seq 1 1: (#pre /\ ={aux2} /\ to_uint aux2{1} = if (nth witness sharing_idx i{1} = 9) then outp+32 else rndp + (nth witness sharing_idx i{1})*32). 
wp;skip => /= &1 &2. move => [#] *. 
rewrite !to_uintD_small !of_uintK !modz_small; first 6 by smt(shridx_rng). 
move => *. 
case (nth witness sharing_idx i{2} = 9). smt(). 
move => [#] *.
have -> : (nth witness sharing_idx i{1} <> 9). smt(). 
simplify. 
do split; first 30 by smt().  smt(@W64). smt(). 

wp; call (MZp_copy_share mm oo ii (load_zp mm ii)).

skip => /= &1 &2 [#] mmv ?iiv ?a2v????sep ib lr ls???? ??? bs ?? ov p1 p2 p3 ????.

split.

do split;  [1.. 3: by smt(shridx_rng) | 6..7,9..: by smt()]. 

case (nth witness sharing_idx i{1} = 9); last first.
move => ixb. rewrite iiv ixb /=.
move : p3; rewrite /touches => tou.
rewrite mmv  -(tou (rndp + nth witness sharing_idx i{1} * 32) _); first by smt(shridx_rng). 
move : (ib (nth witness sharing_idx i{1}) _); first by smt(shridx_rng).
rewrite /inbounds /load_rnd !initiE;   by smt(shridx_rng). 

move => ixb. rewrite iiv ixb /=.
move : (p2 0 1  _ _); first 2 by smt().
by rewrite /inbounds /load_msgs /=; smt().

case (nth witness sharing_idx i{1} = 9); last first.
move => ixb. rewrite iiv ixb /=.
move : p3; rewrite /touches => tou.
rewrite mmv  -(tou (rndp + nth witness sharing_idx i{1} * 32) _); first by smt(shridx_rng). 
move : (ib (nth witness sharing_idx i{1}) _); first by smt(shridx_rng).
rewrite /inbounds /load_rnd !initiE;   by smt(shridx_rng). 

move => ixb. rewrite iiv ixb /=.
move : (p2 0 1  _ _); first 2 by smt().
by rewrite /inbounds /load_msgs /=; smt().

smt().
move => [#] ??????????memL?[#]?sv  bv pres.

do split; first 21 by smt().
move => *.
rewrite to_uintD_small /= (ov _);  smt(). 

move => k kbnd.

case (k < i{1}); last first.
(* just written.*)

move => *.
have -> : (k = i{1}); first by smt().
have -> : (load_zp memL (outp + 32 * i{1}) = load_zp memL oo); first by smt().
rewrite sv mmv.


case (nth witness sharing_idx i{1} = 9); last first.  

(* in randomness *)

move => ixb.
have -> : load_zp Glob.mem{1} ii = load_zp mem ii.
rewrite /load_zp; move : p3; rewrite /touches => tou.
move : (tou ii _); rewrite iiv ixb. simplify; smt(shridx_rng). 
by smt(). 

have -> : (nth witness sharing_idx i{1} < 9). smt(shridx_rng).
simplify. 

rewrite lr /lift_rnd /load_rnd.
rewrite !initiE /=; first by smt(shridx_rng).
rewrite !initiE /=; first by smt(shridx_rng).
rewrite /load_zp /lift_zp /load_array.
congr.
congr.
smt(). 

(* summation *)

move => ixv; rewrite iiv ixv /=. 
by move : (p1 1 _); smt().  

(* previously written *)

move => *.

move : (p1 k _); first by smt().
have -> : (load_zp memL (outp + 32 * k) = load_zp Glob.mem{1} (outp + 32 * k));smt().

move => k j kbnd jbnd curr.

case (6 * k + j < i{1}); last first.
(* just written.*)

move => *.
rewrite /load_msgs.
rewrite initiE /=; first by smt().
rewrite initiE /=; first by smt().
smt().

(* previously written *)

move => *.

move : (p2 k j _ _ _); first 3 by smt(). 
rewrite /load_msgs. 
rewrite initiE /=; first by smt().
rewrite initiE /=; first by smt().
rewrite initiE /=; first by smt().
rewrite initiE /=; first by smt().

smt().
smt().
smt().
smt().
qed.

lemma MZp_createLastShare mem rndp out2p secp rI secv:
equiv [
   M25519.createLastShare ~ MZp.createLastShare :
   separate out2p (8*4) rndp (9*4*8) /\
   separate out2p (8*4) secp (4*8) /\
   out2p + 8*4 < 18446744073709551616 /\
   rndp + 9*4*8 < 18446744073709551616 /\
   secp + 9*4*8 < 18446744073709551616 /\
   (forall (k : int), 0 <= k && k < 9 => inbounds (load_rnd mem rndp).[k]) /\
   rI = lift_rnd (load_rnd mem rndp) /\
   secv = load_zp mem secp /\
   inbounds (load_array mem secp) /\
   mem = Glob.mem{1} /\ 
   to_uint out2{1} = out2p /\ to_uint randoms{1} = rndp /\ to_uint secret{1} = secp /\
   ={arg,Glob.mem} ==> 
   ={res,Glob.mem} /\
  load_zp Glob.mem{1} (out2p) =
  fsub
    secv 
    (foldl (fun (acc : t) (j : int) => fadd acc rI.[j]) ((Zp.inzp 0))%PF (iota_ 0 9)) /\
     inbounds (load_array Glob.mem{1} (out2p)) /\
   touches mem Glob.mem{1} out2p 1].
proc.
sp 3 3.

seq 1 1 : (#{/~mem=Glob.mem{1}}pre /\ load_zp Glob.mem{1} (out2p) = rI.[0] /\
           inbounds (load_array Glob.mem{1} (out2p)) /\
           touches mem Glob.mem{1} out2p 1).

exists* Glob.mem{1}.
elim* => mm.

 wp; call (MZp_copy_share mem (out2p) (rndp) (rI.[0])). 

wp;skip => /= &1&2 [#] ????????????rndb rIv??????????. 
split.
do split; [1..3: by smt()]. 
move : (rndb 0 _); first by smt().
by rewrite /load_rnd;smt().
move : (rndb 0 _); first by smt().
by rewrite /load_rnd;smt().
by rewrite rIv /load_rnd /lift_rnd  /load_zp initiE /=; smt(). 
smt(). smt().  smt(). smt(). smt(). smt().
move => /= [#] ?????????????[#]????.
do split; by smt().

sp 1 1.
seq 2 2 : (#{/~load_zp Glob.mem{1} (out2p) = rI.[0]}pre /\ ={y,i} /\ 
            i{1} = 1 /\ 1<=i{1}<=9 /\
          load_zp Glob.mem{1} (out2p) = 
            foldl (fun acc (j : int) =>
              fadd acc rI.[j]) (Zp.inzp 0) (iota_ 0 i{1})).
wp;skip => &1 &2 [#] ???????????????????????????. 
do split; first 28 by smt(). 
rewrite -iotaredE /=. smt. 

seq 1 1 : (#{/~i{1} = 1}pre /\ i{1}=9 /\ to_uint y{1} = out2p).
while (#{/~i{1} = 1}pre /\ (1 < i{1} => to_uint y{1} = out2p)); last first.
+   wp;skip; move => &1&2[#] ????????????????????????????????; smt(iota0). 

seq 5 5 : (#pre /\ ={x,y} /\ 
             to_uint x{1} = rndp + i{1}*4*8 /\
             to_uint y{1} = out2p).
       inline M25519.getShareIndex MZp.getShareIndex.
       wp; skip => &1 &2 *; rewrite !to_uintD_small !of_uintK !modz_small; first 3 by smt().
       by  do split; smt(). 

exists * Glob.mem{1}, i{1}.
elim* => mm ii.

wp; call (MZp_add_wrapper mm out2p
          (rI.[ii]) (foldl (fun acc (j : int) =>
              fadd acc rI.[j]) (Zp.inzp 0) (iota_ 0 ii))).
skip; move => &1 &2 /= [#] ??????????????? rr rv lst???????? sumb  tou ???? sumv ????? sw1v sw2v.

split. 

rewrite sw1v. 
do split; [1..2:by smt(@W64)| 4..7: by smt(@W64) | 12..: by smt()].  

rewrite rv /lift_rnd initiE /load_rnd  /load_zp /=; first by smt().
by rewrite initiE; smt().

move : (rr i{1} _); rewrite /inbounds /load_rnd; first  by smt().
by rewrite !initiE; smt().

move : (rr i{1} _); rewrite /inbounds /load_rnd; first  by smt().
by rewrite !initiE; smt().

move : (sumb); rewrite /inbounds; by smt(@W64).
move : (sumb); rewrite /inbounds; by smt(@W64).

move => [#] ??????????????? [#] memRv memLv mb?.
do split; [1..32: by smt() ].

rewrite  iota_add /=; first 2 by smt().
rewrite foldl_cat /=. 
have -> : (iota_ i{1} 1 = [i{1}]); first by smt(@List).
simplify. smt. smt(). smt(). smt().


seq 1 1 : (#{/~load_zp Glob.mem{1} out2p = foldl (fun (acc : t) (j : int) => fadd acc rI.[j]) ((Zp.inzp 0))%PF (iota_ 0 i{1})}pre /\
  load_zp Glob.mem{1} (out2p) =
  fsub
    secv
    (foldl (fun (acc : t) (j : int) => fadd acc rI.[j]) ((Zp.inzp 0))%PF (iota_ 0 9))).

exists* Glob.mem{1}.
elim* => mm.

call (MZp_sub_wrapper mm out2p secv
    (foldl (fun (acc : t) (j : int) => fadd acc rI.[j]) ((Zp.inzp 0))%PF (iota_ 0 9))).

skip; move => &1 &2 /= [#] ?????????????? rr rv lst ??????? ? sumb  tou ????  sumv ??.

split.

do split; [1..3: by smt() | 5..7:by smt() | 10..:by smt()].  
smt(). smt(). smt().

move => [#] ??????????????? [#] memRv memLv mb ?.


do split; [1..31: by smt() | 33..:by smt()].

smt().
skip; smt().
qed.


lemma mult_start5_correct mem _st rndp outp (cwire wr1 wr2 : int) (wst : wire_st) (rI : t Array9.t) :
  wst.`1 = cwire =>
  elems (fdom wst.`2) = iota_ 0 cwire =>
  0 <= wr1 < cwire => 0 <= wr2 < cwire =>
   good_wire _st cwire =>
   good_wire_shares mem _st cwire => 
   wst = lift_state_mem mem _st cwire =>
   separate outp (5*6*4*8) _st (cwire*6*4*8) =>
   separate outp (5*6*4*8) rndp (9*4*8) =>
   outp + 5*6*4*8 < W64.modulus =>
   rndp + 9*4*8 < W64.modulus =>
   (forall k, 0<=k<9 => inbounds (load_rnd mem rndp).[k]) =>
   rI = lift_rnd (load_rnd mem rndp) =>
  equiv [ 
   M.mult_start5 ~ MZp.mult_start5 :
   Glob.mem{1} = mem /\ to_uint status{1} = _st /\ 
   to_uint w1{1} = wr1 /\ to_uint w2{1} = wr2 /\
   to_uint outI{1} = outp /\ to_uint randomnessI{1} = rndp /\
   ={arg,Glob.mem} ==> 
   good_wire_shares Glob.mem{1} _st cwire /\ 
   lift_state_mem Glob.mem{1} _st cwire = wst /\
   (forall k, 0<=k<9 => inbounds (load_rnd Glob.mem{1} rndp).[k]) /\
   rI = lift_rnd (load_rnd Glob.mem{1} rndp) /\
   (forall k j, 0<=k<5 => 0<=j<6 => inbounds (load_msgs Glob.mem{1} outp).[k].[j]) /\
   mul_start wr1 wr2 wst rI = lift_msgs (load_msgs Glob.mem{1} outp) /\
    touches mem Glob.mem{1} outp 30 /\
   ={res,Glob.mem} ].
proof.
move => /= cwr stdom w1v w2v gw gws lst sepos sepor  ogood rgood rbnd rl.
move : gw; rewrite /good_wire /= => gw.

transitivity  M25519.mult_start5  (={arg,Glob.mem} ==> ={res,Glob.mem}) 
   (
   Glob.mem{1} = mem /\ to_uint status{1} = _st /\ 
   to_uint w1{1} = wr1 /\ to_uint w2{1} = wr2 /\
   to_uint outI{1} = outp /\ to_uint randomnessI{1} = rndp /\
   ={arg,Glob.mem} ==> 
   good_wire_shares Glob.mem{1} _st cwire /\ 
   lift_state_mem Glob.mem{1} _st cwire = wst /\
   (forall k, 0<=k<9 => inbounds (load_rnd Glob.mem{1} rndp).[k]) /\
   rI = lift_rnd (load_rnd Glob.mem{1} rndp) /\
   (forall k j, 0<=k<5 => 0<=j<6 => inbounds (load_msgs Glob.mem{1} outp).[k].[j]) /\
   mul_start wr1 wr2 wst rI = lift_msgs (load_msgs Glob.mem{1} outp) /\
    touches mem Glob.mem{1} outp 30 /\
   ={res,Glob.mem}   ); 
        [by smt() | by smt() | by apply M25519_mult_start5 |] .

proc. 

move : lst; rewrite /lift_state_mem => /=.
have -> : (wst = (wst.`1,wst.`2)); first by smt().
simplify => /= [#] wst1 wst2.

seq 1 1 : (#{/~Glob.mem{1}=mem}pre /\ load_zp Glob.mem{1} outp = Zp.inzp 0 /\
          inbounds (load_array Glob.mem{1} outp) /\
          good_wire_shares Glob.mem{1} _st cwire /\
          wst = lift_state_mem Glob.mem{1} _st cwire /\
          (forall k, 0<=k<9 => inbounds (load_rnd Glob.mem{1} rndp).[k]) /\
          rI = lift_rnd (load_rnd Glob.mem{1} rndp) /\
          touches mem Glob.mem{1} outp 30
).
+ call (ops_set0 mem outp). 
 skip;move => /= &1 &2 [#] ????????????.
 split; first by smt(). 
 move => ? mem_L memR [#] memLv tou ?? ; do split; first 14 by smt(load_store_zp_eq load_store_zp_bound).
  smt(). 
 rewrite  /lift_state_mem /=; move => *.
  have -> : (wst = (wst.`1,wst.`2)); first by smt().
  simplify => /=; split; first by smt().  
  move => *; rewrite wst2.
  apply fmap_eqP => x.

rewrite /(SmtMap."_.[_]") !ofmapK /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire)).
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
exists (iota_ 0 (cwire)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
  rewrite /(SmtMap."_.[_]") /=.
  rewrite !Map.offunE /=.

 case (0<= x < cwire) => xb; last by smt().
congr.
apply Array6.ext_eq => *. 
rewrite !initiE /=; first 2 by smt(). 
by smt().

move => k kbnd. 
rewrite /load_rnd initiE /=; first by smt(). 
move : rbnd; rewrite /load_rnd.
move => H; move :(H k kbnd).
by rewrite initiE => /#.

rewrite rl /load_rnd /lift_rnd /=. 
apply Array9.ext_eq => x xbnd.
rewrite !initiE /=; first 2 by smt().
rewrite !initiE /=; first 2 by smt().
by   smt().
by   smt().

seq 8 8 : (#pre /\ ={valmult,randomness,sw1,sw2,out,st} /\ to_uint randomness{1} = rndp /\
      to_uint sw1{1} = wr1 /\ to_uint sw2{1} = wr2 /\ to_uint out{1} = outp /\ st{1} = status{1} /\
      to_uint valmult{1} = outp+32); first by
     auto => />; move => *; rewrite to_uintD_small;  by smt(@W64).

seq 2 2 : (#{/~load_zp Glob.mem{1} outp = (Zp.inzp 0)}pre /\ 
          load_zp Glob.mem{1} outp = 
            foldl (fun acc (cij : (int*int)) =>
              fadd acc (fmul (oget wst.`2.[wr1]).[cij.`1] 
                             (oget wst.`2.[wr2]).[cij.`2]))
                (Zp.inzp 0) cross_idx).
while (#{/~load_zp Glob.mem{1} outp = (Zp.inzp 0)}pre /\ 
          load_zp Glob.mem{1} outp = 
            foldl (fun acc (cij : (int*int)) =>
              fadd acc (fmul (oget wst.`2.[wr1]).[cij.`1] 
                             (oget wst.`2.[wr2]).[cij.`2]))
                (Zp.inzp 0) (take crossc{1} cross_idx) /\
          0<= crossc{1} <= 20 /\ ={crossc}); last first.
+   wp;skip => />; progress.
    rewrite H19. congr. smt.

+inline M25519.mult_pair5 MZp.mult_pair5.
seq 25 25 : (#pre /\
           ={resvalS,val1S,val2S} /\
           resvalS{1}=valmult{1} /\
           to_uint val1S{1} = _st + 8*(6*4*wr1+((nth witness cross_idx crossc{1}).`1)*4) /\
           to_uint val2S{1} = _st + 8*(6*4*wr2+((nth witness cross_idx crossc{1}).`2)*4)).
wp;skip;move => &1 &2 [#] ??????????????????????????????????? val1S_L val2S_L.


have ? : (0<= val2S_L.`1 < 6); first by smt(cross_rng). 
have ? : (0<= val2S_L.`2 < 6); first by smt(cross_rng). 
 
do split; first 39 by smt(). 


rewrite !to_uintD_small /=; last first.
rewrite !to_uintM_small /=; last first.
rewrite !to_uintD_small /=; last first.
rewrite !to_uintM_small /=; smt(@W64).
rewrite !to_uintM_small /=; smt(@W64).
rewrite !to_uintD_small /=; last first.
rewrite !to_uintM_small /=; smt(@W64).
rewrite !to_uintM_small /=; smt(@W64).
rewrite !to_uintM_small /=; smt(@W64).
rewrite !to_uintD_small /=; last first.
rewrite !to_uintM_small /=; last first.
rewrite !to_uintD_small /=; last first.
rewrite !to_uintM_small /=; smt(@W64).
rewrite !to_uintM_small /=; smt(@W64).
rewrite !to_uintD_small /=; last first.
rewrite !to_uintM_small /=; smt(@W64).
rewrite !to_uintM_small /=; smt(@W64).
rewrite !to_uintM_small /=; smt(@W64).


seq 1 1 : (#pre /\ 
          load_zp Glob.mem{1} (to_uint valmult{1}) = 
                (fmul (oget wst.`2.[wr1]).[(nth witness cross_idx crossc{1}).`1] 
                      (oget wst.`2.[wr2]).[(nth witness cross_idx crossc{1}).`2]) /\
          inbounds (load_array Glob.mem{1} (to_uint valmult{1}))).
exists* Glob.mem{1}, (to_uint valmult{1}), crossc{1}.
elim* => mm valmult cc.
call (MZp_mul_wrapper mm valmult (oget wst.`2.[wr1]).[(nth witness cross_idx cc).`1] (oget wst.`2.[wr2]).[(nth witness cross_idx cc).`2]).
skip. 
move => /= &1 &2 [#] ?????????????? ibb gwsh lstss rbndd rIv tou ???????????? fld ????????? v1sv v2sv.
split.
do split; [1..2: by smt() | 5..7:smt(cross_rng)| 12..:smt()].

have -> : ( wst.`2 = (lift_state_mem Glob.mem{1} _st cwire).`2); first by smt().
rewrite /lift_state_mem /=.
rewrite /(SmtMap."_.[_]") !ofmapK /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire)).
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
simplify => /=. 
rewrite Map.offunE /= w1v /= initiE /=; smt(cross_rng). 

have -> : ( wst.`2 = (lift_state_mem Glob.mem{1} _st cwire).`2); first by smt().
rewrite /lift_state_mem /=.
rewrite /(SmtMap."_.[_]") !ofmapK /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire)).
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
simplify => /=. 
rewrite Map.offunE /= w2v /= initiE /=; smt(cross_rng). 

rewrite v1sv.
move : gwsh; rewrite /good_wire_shares => H; move : (H wr1 _ (nth witness cross_idx crossc{1}).`1 _); by smt(cross_rng).

rewrite v1sv.
move : gwsh; rewrite /good_wire_shares => H; move : (H wr1 _ (nth witness cross_idx crossc{1}).`1 _); by smt(cross_rng).

rewrite v2sv.
move : gwsh; rewrite /good_wire_shares => H; move : (H wr2 _ (nth witness cross_idx crossc{1}).`2 _); by smt(cross_rng).

rewrite v2sv.
move : gwsh; rewrite /good_wire_shares => H; move : (H wr2 _ (nth witness cross_idx crossc{1}).`2 _); by smt(cross_rng).

move => [#] mmv ??????????????[#]? memlv memll memlr.
do split; [1..14: by smt() | 18..: by smt()]. 


have -> : (wst = (wst.`1,wst.`2)); first by smt().
have -> : ( wst.`2 = (lift_state_mem Glob.mem{1} _st cwire).`2); first by smt().
rewrite /lift_state_mem /=.
split; first by smt().
move => *.

apply fmap_eqP => x.
rewrite /(SmtMap."_.[_]") !ofmapK /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire)).
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
exists (iota_ 0 (cwire)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
  rewrite /(SmtMap."_.[_]") /=.
  rewrite !Map.offunE /=.

 case (0<= x < cwire) => xb; last by smt().
congr.
apply Array6.ext_eq => *. 
rewrite !initiE /=; first 2 by smt().
smt().

move : rbndd.
rewrite  /load_rnd => rbndd k kbnd.  
move : memlv; rewrite /touches => ttou. 
rewrite initiE /=; first by smt().
rewrite -(ttou (rndp + k * 8 * 4)). smt(). 
move : (rbndd k kbnd). 
rewrite initiE /=; first by smt().
smt().

rewrite rIv /lift_rnd /=.
apply Array9.ext_eq => k kb.
rewrite !Array9.initiE /=; first 2 by smt().
rewrite  /load_rnd.  
rewrite !initiE /=; first 2 by smt().
move : memlv; rewrite /touches => ttou. 
rewrite -(ttou (rndp + k * 8 * 4)). smt(). 
smt().

exists* Glob.mem{1}, (to_uint valmult{1}), crossc{1}.
elim* => mm valmult cc.

wp; call (MZp_add_wrapper mm outp (fmul (oget wst.`2.[wr1]).[(nth witness cross_idx cc).`1]
    (oget wst.`2.[wr2]).[(nth witness cross_idx cc).`2]) 
     (foldl
       (fun (acc : t) (cij : int * int) => fadd acc (fmul (oget wst.`2.[wr1]).[cij.`1] (oget wst.`2.[wr2]).[cij.`2]))
       ((Zp.inzp 0))%PF (take cc cross_idx))).

skip; move => &1 &2 [#] ??????????????ibb gwsh lstss rbndd rIv ????????????? fld ????????? v1sv v2sv H1 H2.

split; first by smt().

move => [#] mmv ????????????????[#] ?? tou lv ibbb crossl ?.

do split; [1..14: by smt() | 18..30: by smt() | 32..:by smt()]. 

have -> : (wst = (wst.`1,wst.`2)); first by smt().
have -> : ( wst.`2 = (lift_state_mem Glob.mem{1} _st cwire).`2); first by smt().
rewrite /lift_state_mem /=.
split; first by smt().
move => *.

apply fmap_eqP => x.
rewrite /(SmtMap."_.[_]") !ofmapK /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire)).
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
exists (iota_ 0 (cwire)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
  rewrite /(SmtMap."_.[_]") /=.
  rewrite !Map.offunE /=.

 case (0<= x < cwire) => xb; last by smt().
congr.
apply Array6.ext_eq => *. 
rewrite !initiE /=; first 2 by smt().
smt().

rewrite /load_rnd => k kbnd. rewrite initiE /=; first by smt(). 
move : (rbndd k _); rewrite /load_rnd; first by smt().
rewrite initiE; by smt().

rewrite rIv /lift_rnd /load_rnd.
apply Array9.ext_eq => x xbnd.
rewrite !initiE /=; first 2 by smt().
rewrite !initiE /=; first 2 by smt().
by smt().

rewrite lv.   


have -> : (take (crossc{1} + 1) cross_idx = 
           (take crossc{1} cross_idx)++[nth witness cross_idx (crossc{1})]);
   first by smt(@List).

by rewrite foldl_cat /=; smt().

sp.

seq 1 1 : (#{/~load_zp Glob.mem{1} outp =
   foldl (fun (acc : t) (cij : int * int) => fadd acc (fmul (oget wst.`2.[wr1]).[cij.`1] (oget wst.`2.[wr2]).[cij.`2]))
     ((Zp.inzp 0))%PF cross_idx}
           {~inbounds (load_array Glob.mem{1} outp)}pre /\
  load_zp Glob.mem{1} (outp +  4 * 8) =
  fsub
    (foldl (fun (acc : t) (cij : int * int) => fadd acc (fmul (oget wst.`2.[wr1]).[cij.`1] (oget wst.`2.[wr2]).[cij.`2]))
     ((Zp.inzp 0))%PF cross_idx) 
    (foldl (fun (acc : t) (j : int) => fadd acc rI.[j]) ((Zp.inzp 0))%PF (iota_ 0 9)) /\
     inbounds (load_array Glob.mem{1} (outp+32))).

(******)

exists * Glob.mem{1}.
elim* => mm.

call (MZp_createLastShare mm rndp (outp+32) (outp) rI (foldl (fun (acc : t) (cij : int * int) => fadd acc (fmul (oget wst.`2.[wr1]).[cij.`1] (oget wst.`2.[wr2]).[cij.`2]))
    ((Zp.inzp 0))%PF cross_idx)).

skip; move =>/= &1 &2 [#]????????????????lst rbb rvv??????????????.

split; first by smt(). 

move => [#] ???????????????????[#]???tou.

do split; [1..14:smt() | 18..:smt()].

move : lst; rewrite /lift_state_mem /=. 
have ->: (wst = (wst.`1,wst.`2)); first by smt().
simplify => [#] wstt1 wstt2.
split; first by smt().
rewrite wstt2 => *.
  apply fmap_eqP => x.

rewrite /(SmtMap."_.[_]") !ofmapK /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire)).
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
exists (iota_ 0 (cwire)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
  rewrite /(SmtMap."_.[_]") /=.
  rewrite !Map.offunE /=.

 case (0<= x < cwire) => xb; last by smt().
congr.
apply Array6.ext_eq =>  k kbnd. 
rewrite !initiE /=; first 2 by smt().
have load_zp_load_array : (forall mmm aa, load_zp mmm aa = lift_zp (load_array mmm aa)).
move => mmm aa.
by rewrite /load_zp /lift_zp /load_array. 
rewrite load_zp_load_array. smt().

move =>  k kbnd. rewrite /inbounds /load_rnd.
rewrite initiE /=; first by smt(). 
move : tou; rewrite /touches => tou.
rewrite -tou /=; first by smt().
move : (rbb k kbnd). rewrite /load_rnd initiE /=;  by smt(). 

rewrite /lift_rnd /load_rnd /=. 
apply Array9.ext_eq => k kbnd.
rewrite initiE /=; first by smt().
rewrite initiE /=; first by smt().
move : tou; rewrite /touches => tou.
rewrite -tou /=; first by smt().
rewrite rvv /lift_rnd /load_rnd.
rewrite initiE /=; first by smt().
rewrite initiE /=; first by smt().
smt().


(*****)

seq 1 1 : (#{/~load_zp Glob.mem{1} (outp + 4 * 8) =
  fsub
    (foldl
       (fun (acc : t) (cij : int * int) => fadd acc (fmul (oget wst.`2.[wr1]).[cij.`1] (oget wst.`2.[wr2]).[cij.`2]))
       ((Zp.inzp 0))%PF cross_idx) (foldl (fun (acc : t) (j : int) => fadd acc rI.[j]) ((Zp.inzp 0))%PF (iota_ 0 9))}
           {~ inbounds (load_array Glob.mem{1} (outp + 32))}pre /\
          (forall k, 0 <= k < 30 =>           
            load_zp Glob.mem{1} (outp + 8*4*k) = 
                if nth witness sharing_idx k < 9
                then rI.[nth witness sharing_idx k]
                else fsub
    (foldl
       (fun (acc : t) (cij : int * int) => fadd acc (fmul (oget wst.`2.[wr1]).[cij.`1] (oget wst.`2.[wr2]).[cij.`2]))
       ((Zp.inzp 0))%PF cross_idx) (foldl (fun (acc : t) (j : int) => fadd acc rI.[j]) ((Zp.inzp 0))%PF (iota_ 0 9))) /\
       (forall (k j : int), 0 <= k && k < 5 => 0 <= j && j < 6 => inbounds (load_msgs Glob.mem{1} outp).[k].[j])).

exists* Glob.mem{1}.
elim* => mm.
call (MZp_create_sharing mm outp rndp rI (fsub
    (foldl
       (fun (acc : t) (cij : int * int) => fadd acc (fmul (oget wst.`2.[wr1]).[cij.`1] (oget wst.`2.[wr2]).[cij.`2]))
       ((Zp.inzp 0))%PF cross_idx) (foldl (fun (acc : t) (j : int) => fadd acc rI.[j]) ((Zp.inzp 0))%PF (iota_ 0 9)))). 

skip =>  /= &1 &2 [#] ???????????????lst rb rv ????????????? sv bv.

split.

do split;  smt(). 

move => [#] ???rbb rvv subb?????????[#]? switch bnd pres. 

do split; first 14 by smt().

move : lst; rewrite /lift_state_mem /=. 
have ->: (wst = (wst.`1,wst.`2)); first by smt().
simplify => [#] wstt1 wstt2.
split; first by smt().
rewrite wstt2 => *.
  apply fmap_eqP => x.

rewrite /(SmtMap."_.[_]") !ofmapK /is_finite /is_finite_for /=. 
exists (iota_ 0 (cwire)).
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
exists (iota_ 0 (cwire)). 
split; first by smt(iota_uniq).
move => *; rewrite mema_iota; smt(Map.offunE). 
  rewrite /(SmtMap."_.[_]") /=.
  rewrite !Map.offunE /=.

 case (0<= x < cwire) => xb; last by smt().
congr.
apply Array6.ext_eq =>  k kbnd. 
rewrite !initiE /=; first 2 by smt().
have load_zp_load_array : (forall mmm aa, load_zp mmm aa = lift_zp (load_array mmm aa)).
move => mmm aa.
by rewrite /load_zp /lift_zp /load_array. 
rewrite load_zp_load_array. smt().

move =>  k kbnd. rewrite /inbounds /load_rnd.
rewrite initiE /=; first by smt().
 rewrite -pres /=; first by smt().
move : (rbb k kbnd). rewrite /load_rnd initiE /=; first by smt(). 
smt().

rewrite /lift_rnd /load_rnd /=. 
apply Array9.ext_eq => k kbnd.
rewrite initiE /=; first by smt().
rewrite initiE /=; first by smt().
rewrite - pres.  smt(). 
rewrite rvv /lift_rnd /load_rnd.
rewrite initiE /=; first by smt().
rewrite initiE /=; first by smt().
smt().

smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().

skip;move => &1 &2 [#] ??????????????lst???????????????ov ob.

do split. smt(). 

move : lst; rewrite /lift_state_mem.
have -> : (wst = (wst.`1,wst.`2)); first by smt().
simplify => [#] wstt1 wstt2.
split; first by smt().
by rewrite wstt2. 
 smt(). smt(). smt(). 

rewrite /mul_start /lift_msgs /load_msgs /share /transpose /init_sh /=.

apply Array5.ext_eq =>  /= x xbnd.
have -> : (wst = (wst.`1,wst.`2)); first by smt().
rewrite !initiE /=; first by smt().
rewrite !initiE /=; first 2 by smt().
apply Array6.ext_eq =>  /= xx xxbnd.
rewrite !initiE /= /shr_idx /=; first 2 by smt().
rewrite (nth_map witness) /=; first by smt().
rewrite !initiE /=; first by smt().
    case (x = 0); first by smt().
    case (x = 1); first by smt().
    case (x = 2); first by smt().
    case (x = 3); first by smt().
    case (x = 4); first by smt().
    by smt().
have -> : (lift_zp (load_array Glob.mem{1} (outp + 192 * x + 32 * xx)) = 
           load_zp  Glob.mem{1} (outp + 8*4*(6*x+xx))); first by rewrite /load_zp /=; smt(). 
rewrite (ov (6*x+xx) _); first by smt().
rewrite /sharing_idx  /cross_idx -iotaredE /sum_rand  /cross /=.
have -> : to_list rI = rI.[0]::rI.[1]::rI.[2]::rI.[3]::rI.[4]::rI.[5]::rI.[6]::rI.[7]::rI.[8]::[]; first by rewrite /to_list /mkseq -iotaredE /=. 
simplify. 
case (x = 0).
case (xx = 0).
by move => -> -> /=.
case (xx = 1).
by move => -> ?-> /=;ring.
case (xx = 2).
by move => -> ?? -> /=.
case (xx = 3).
by move => -> ??? -> /=.
case (xx = 4).
by move => -> ???? -> /=.
case (xx = 5).
by move => -> ????? -> /=.
smt().

case (x = 1).
case (xx = 0).
by move => -> -> /=.
case (xx = 1).
by move => -> ?-> /=.
case (xx = 2).
by move => -> ?? -> /=; ring.
case (xx = 3).
by move => -> ??? -> /=.
case (xx = 4).
by move => -> ???? -> /=.
case (xx = 5).
by move => -> ????? -> /=.
smt().

case (x = 2).
case (xx = 0).
by move => -> -> /=.
case (xx = 1).
by move => -> ?-> /=.
case (xx = 2).
by move => -> ?? -> /=.
case (xx = 3).
by move => -> ??? -> /=.
case (xx = 4).
by move => -> ???? -> /=; ring.
case (xx = 5).
by move => -> ????? -> /=.
smt().

case (x = 3).
case (xx = 0).
by move => -> -> /=.
case (xx = 1).
by move => -> ?-> /=.
case (xx = 2).
by move => -> ?? -> /=.
case (xx = 3).
by move => -> ??? -> /=.
case (xx = 4).
by move => -> ???? -> /=.
case (xx = 5).
by move => -> ????? -> /=.
smt().

case (x = 4).
case (xx = 0).
by move => -> -> /=.
case (xx = 1).
by move => -> ?-> /=.
case (xx = 2).
by move => -> ?? -> /=.
case (xx = 3).
by move => -> ??? -> /=.
case (xx = 4).
by move => -> ???? -> /=.
case (xx = 5).
by move => -> ????? -> /=.
smt().

smt().
smt().
smt().
qed.
