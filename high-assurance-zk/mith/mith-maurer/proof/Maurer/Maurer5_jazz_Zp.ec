require import AllCore IntDiv CoreMap List SmtMap FSet.
from Jasmin require import JModel.

require import Bn_p25519_proof.

require import Maurer5_jazz.
require import Zp25519.
require import Maurer5Spec.

require import Array6 Array4 Array9 Array5.

lemma load_storeW64_eq mem a x:
 loadW64 (storeW64 mem a x) a = x.
proof.
rewrite /loadW64 /storeW64 -(W8u8.unpack8K x); congr.
apply W8u8.Pack.all_eq_eq; rewrite /all_eq !storesE /=.
rewrite !get_setE => |>. smt().
qed.

lemma load_storeW64_neq mem a1 a2 x:
 (a2 + 8 <= a1 || a1 + 8 <= a2) => 
 loadW64 (storeW64 mem a1 x) a2 = loadW64 mem a2.
proof.
move => H; rewrite /loadW64 /storeW64; congr.
apply W8u8.Pack.all_eq_eq; rewrite /all_eq !storesE /=.
rewrite !get_setE => |>. smt(). 
qed.

clone import Maurer5Spec as Spec with
  theory Maurer5SS.PF <- Zp25519.Zp.

import Zp W64x4.
import Maurer5SS.

op load_array(mem : global_mem_t, ptr : int) = 
    Array4.init (fun i => (loadW64 mem (ptr + (i * 8)))).

op store_array(mem: global_mem_t, a: int, w4: W64.t Array4.t):  global_mem_t =
 let mem = storeW64 mem (a + 0*8) w4.[0] in
 let mem = storeW64 mem (a + 1*8) w4.[1] in
 let mem = storeW64 mem (a + 2*8) w4.[2] in
           storeW64 mem (a + 3*8) w4.[3].

lemma load_store_array_eq mem ptr x:
 load_array (store_array mem ptr x) ptr = x.
proof.
rewrite /load_array /store_array.
apply Array4.all_eq_eq.
rewrite /a /all_eq /=. 
rewrite load_storeW64_eq load_storeW64_neq => |>. smt(). 
rewrite load_storeW64_neq => |>. smt().
rewrite load_storeW64_neq => |>. 
rewrite load_storeW64_eq load_storeW64_neq => |>. smt().
rewrite load_storeW64_neq => |>.
rewrite load_storeW64_eq load_storeW64_neq => |>.
rewrite load_storeW64_eq => |>.
qed.

lemma load_store_array_neq mem a1 a2 x:
 (a2 + 32 <= a1 || a1 + 32 <= a2) => 
 load_array (store_array mem a1 x) a2 = load_array mem a2.
proof.
move=> H; rewrite /load_array /store_array.
apply Array4.all_eq_eq.
rewrite /a /all_eq /=.
rewrite !load_storeW64_neq => |>. smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). 
qed.

op lift_zp(v : W64.t Array4.t) = inzp (valR v).

op unlift_zp (x: zp) : R = R.bn_ofint (asint x).

lemma lift_unlift_zp v: lift_zp (unlift_zp v) = v.
proof.
rewrite /lift_zp /unlift_zp R.bn_ofintK.
apply asint_inj; rewrite inzpK /=.
rewrite (modz_small _ modulusR). smt.
rewrite modz_small; smt(rg_asint).
qed.

lemma unlift_lift_zp x: valR x < P => unlift_zp (lift_zp x) = x.
proof.
move => Hx.
rewrite /unlift_zp /lift_zp inzpK modz_small. smt.
by rewrite R.bnK.
qed.

op load_zp(mem : global_mem_t, a : int) =
   lift_zp (load_array mem a).

op store_zp(mem : global_mem_t, a : int, v : zp) =
  store_array mem a (unlift_zp v).

lemma load_store_zp_eq mem a x: load_zp (store_zp mem a x) a =  x.
proof.
rewrite /load_zp /store_zp load_store_array_eq.
by rewrite lift_unlift_zp.
qed.

op inbounds(v : W64.t Array4.t) = 0 <= valR v < P.

op separate(ptr1 len1 ptr2 len2 :int) =
      (ptr1 + len1 <= ptr2) \/ (ptr2 + len2 <= ptr1).

op touches(premem postmem: global_mem_t, ptr len : int) : bool =
    forall a, separate a (8*4) ptr (len*8*4) => 
          load_array premem a = load_array postmem a.

op lift_rnd(a : (W64.t Array4.t) Array9.t) : zp Array9.t =
      Array9.init (fun i => lift_zp a.[i]).

op load_rnd (mem : global_mem_t) (ptr : int) : (W64.t Array4.t) Array9.t =
  (Array9.init (fun (i : int) => load_array mem (ptr + i * 8*4))).

op lift_msgs(a : ((W64.t Array4.t) Array6.t) Array5.t) : (zp Array6.t) Array5.t =
      Array5.init (fun i => 
          (Array6.init (fun j => lift_zp a.[i].[j]))).

op load_msgs (mem : global_mem_t) (ptr : int) : ((W64.t Array4.t) Array6.t) Array5.t =
      Array5.init (fun i => 
          (Array6.init (fun j => load_array mem (ptr+8*4*6*i+8*4*j)))).

op cross_idx = (0,0)::(0,1)::(0,2)::(0,4)::
               (1,3)::(1,4)::(1,5)::
               (2,0)::(2,2)::(2,3)::(2,4)::
               (3,0)::(3,1)::(3,2)::(3,5)::
               (4,1)::(4,2)::(4,3)::
               (5,0)::(5,3)::[].

lemma cross_rng c cij : 
   0 <= c < 20 => 
   cij = nth witness cross_idx c => 
     0 <= cij.`1 < 6 /\ 0 <= cij.`2 < 6 by smt().

op sharing_idx = 5::9::8::7::4::6::
                 1::2::9::3::8::7::
                 6::0::2::5::9::3::
                 3::8::4::6::0::1::
                 7::4::0::1::2::5::[].


op good_wire(st w : int) =
      st + (24 * w + 24)*8 <= W64.modulus.

op good_wire_share(mem : global_mem_t, st w k : int) =
      inbounds (load_array mem (st + 8*(24 * w + 4*k))).

op load_wire_share(mem : global_mem_t, st w k : int) = 
      load_zp mem  (st + 8*(24 * w + 4*k)).

op store_wire_share(mem : global_mem_t, st w k : int, v : zp) = 
      store_zp mem  (st + 8*(24 * w + 4*k)) v.

op good_wire_shares(mem : global_mem_t, st wc : int) =
  forall w, 0 <= w < wc =>
    forall k, 0 <= k < 6 =>
      inbounds (load_array mem (st + 8*(24 * w + 4*k))).

op lift_state_mem(mem : global_mem_t, st wc: int) : wire_st =
         let wire_count = wc in
         let state_map = ofmap 
            (Map.offun
                (fun w : int => 
                   if 0 <= w < wire_count
                   then Some
                     (Array6.init (fun k : int =>
                               load_zp mem (st+  8*(24 * w + 4 * k))))
                   else None)) in  (wire_count, state_map).

lemma shridx_rng c : 
   0 <= c < 30 => 
   0 <= nth witness sharing_idx c < 10 by smt().

module OpsZp = {
  proc load_array(in_0 : W64.t) : zp = {
    var v : zp;
    v <- load_zp Glob.mem (to_uint in_0);
    return v;    
  }

  proc store_array(out: W64.t, in_0 : zp) : unit  = {
    Glob.mem <- store_zp Glob.mem (to_uint out) in_0;
  }

  proc set0(out: W64.t) : unit  = {
    Glob.mem <- store_zp Glob.mem (to_uint out) (inzp 0);
  }

  proc add_freeze(v1 v2 : zp) : zp = {
      return fadd v1 v2;
  }

  proc mul_freeze(v1 v2 : zp) : zp = {
      return fmul v1 v2;
  }

  proc sub_freeze(v1 v2 : zp) : zp = {
      return fsub v1 v2;
  }

}.

lemma simplify_loads (mem : global_mem_t) (in_0 : W64.t) (v : W64.t Array4.t) :
  to_uint in_0 < W64.modulus - 24 =>
  v = witness =>
  (v
     .[0 <- loadW64 mem (to_uint in_0)]
     .[1 <- loadW64 mem (to_uint (in_0 + (of_int 8)%W64))]
     .[2 <- loadW64 mem (to_uint (in_0 + (of_int 16)%W64))]
     .[3 <- loadW64 mem (to_uint (in_0 + (of_int 24)%W64))]=
       Array4.init (fun (i : int) => loadW64 mem (to_uint in_0 + i * 8))).
proof.
move => /= H ->.
apply Array4.ext_eq => x xbnd.
rewrite !initiE //=.
rewrite !to_uintD_small W64.to_uint_small //=; first 3 by smt().
by smt(@Array4).
qed.

lemma ops_load mem _a :
   equiv [ M.load_array ~ OpsZp.load_array :
        inbounds (load_array Glob.mem{1} (to_uint in_0{1}))  /\ to_uint in_0{1} = _a /\
        W64.to_uint in_0{1} < W64.modulus - 24 /\ Glob.mem{1} = mem /\
       ={arg,Glob.mem} ==> 
        inbounds res{1}  /\ Glob.mem{1} = mem /\
           res{2} = lift_zp res{1} /\ res{2} = load_zp mem _a
   ].
proof.
proc; unroll for {1} 3.
by auto => /> *; rewrite /load_array !simplify_loads //.
qed.

lemma ops_load' mem _a :
   equiv [ M.load_array ~ OpsZp.load_array :
        inbounds (load_array Glob.mem{1} (to_uint in_0{1}))  /\ in_0{1} = _a /\
        W64.to_uint in_0{1} < W64.modulus - 24 /\ Glob.mem{1} = mem /\
       ={arg,Glob.mem} ==> 
        inbounds res{1}  /\ Glob.mem{1} = mem /\
           res{2} = lift_zp res{1} /\ res{2} = load_zp mem (to_uint _a)
   ].
proof. by conseq (ops_load mem (to_uint _a)). qed.

lemma ops_load_stack mem _a :
   equiv [ M.load_array_st ~ OpsZp.load_array :
        inbounds (load_array Glob.mem{1} (to_uint in_0{1}))  /\ to_uint in_0{1} = _a /\
        W64.to_uint in_0{1} < W64.modulus - 24 /\ Glob.mem{1} = mem /\
       ={arg,Glob.mem} ==> 
        inbounds res{1}  /\ Glob.mem{1} = mem /\
           res{2} = lift_zp res{1} /\ res{2} = load_zp mem _a
   ].
proof.
proc; unroll for {1} 3.
by auto => /> *; rewrite /load_array !simplify_loads //.
qed.

lemma ops_load_stack' mem _a :
   equiv [ M.load_array_st ~ OpsZp.load_array :
        inbounds (load_array Glob.mem{1} (to_uint in_0{1}))  /\ in_0{1} = _a /\
        W64.to_uint in_0{1} < W64.modulus - 24 /\ Glob.mem{1} = mem /\
       ={arg,Glob.mem} ==> 
        inbounds res{1}  /\ Glob.mem{1} = mem /\
           res{2} = lift_zp res{1} /\ res{2} = load_zp mem (to_uint _a)
   ].
proof. by conseq (ops_load_stack mem (to_uint _a)). qed.

lemma load_store_W64_neq (mem : global_mem_t) ptr1 ptr2 (w:W64.t) :
  separate ptr1 8 ptr2 8 =>
  loadW64 (storeW64 mem ptr2 w) ptr1 = loadW64 mem ptr1.
proof. smt(load_storeW64_neq). qed.

lemma load_store_W64_eq (mem : global_mem_t) ptr (w:W64.t) :
  loadW64 (storeW64 mem ptr w) ptr = w.
proof. exact load_storeW64_eq. qed.

lemma ops_store mem _out _v :
   equiv [ M.store_array ~ OpsZp.store_array :
       W64.to_uint out{1} < W64.modulus - 24 /\ _v = lift_zp in_0{1} /\
       inbounds in_0{1} /\ Glob.mem{1} = mem /\ to_uint out{1} = _out /\
      ={out,Glob.mem} /\ in_0{2} = lift_zp in_0{1} ==> 
      ={Glob.mem} /\ 
      touches mem Glob.mem{1} _out 1 /\
      load_zp Glob.mem{1} _out = _v /\
      inbounds (load_array Glob.mem{1} _out)
   ].
proof.
proc; unroll for {1} 2.
auto => /= &1 &2 [#] ?.
rewrite !to_uintD_small to_uint_small; first 7 by smt().
move =>   vl vb ???? in2v.
split. 
+ rewrite in2v /store_zp /= unlift_lift_zp /#.
split. 
+ move => a; rewrite /touches /separate /load_array => sep.
  apply Array4.ext_eq => x xbnd.
  rewrite !initiE /=; first 2 by smt().
  smt(load_store_W64_eq load_store_W64_neq).
split. 
+ rewrite vl /load_zp; congr. 
  rewrite /load_array /=.
  apply Array4.ext_eq => /= xx xxb.
  rewrite !initiE /= 1:/#.
  smt(load_store_W64_eq load_store_W64_neq).
+ have -> : (load_array
     (storeW64
        (storeW64 (storeW64 (storeW64 Glob.mem{1} (to_uint out{1}) in_0{1}.[0]) (to_uint out{1} + 8) in_0{1}.[1])
           (to_uint out{1} + to_uint ((of_int 16))%W64) in_0{1}.[2]) (
        to_uint out{1} + to_uint ((of_int 24))%W64) in_0{1}.[3]) _out =
     in_0{1}); last by smt().
     rewrite /load_array.
  apply Array4.ext_eq => x xbnd.
  rewrite !initiE /=; first  by smt().
  smt(load_store_W64_eq load_store_W64_neq).
qed.

lemma ops_store' mem _out _v :
   equiv [ M.store_array ~ OpsZp.store_array :
       W64.to_uint out{1} < W64.modulus - 24 /\ _v = lift_zp in_0{1} /\
       inbounds in_0{1} /\ Glob.mem{1} = mem /\ out{1} = _out /\
      ={out,Glob.mem} /\ in_0{2} = lift_zp in_0{1} ==> 
      ={Glob.mem} /\ 
      touches mem Glob.mem{1} (to_uint _out) 1 /\
      load_zp Glob.mem{1} (to_uint _out) = _v /\
      inbounds (load_array Glob.mem{1} (to_uint _out))
   ].
proof. by conseq (ops_store mem (to_uint _out) _v). qed.

lemma ops_set0 mem _out :
   equiv [ M.set0 ~ OpsZp.set0 :
       W64.to_uint out{1} < W64.modulus - 24 /\ 
       Glob.mem{1} = mem /\ to_uint out{1} = _out /\
      ={out,Glob.mem} ==> 
      ={Glob.mem} /\ 
      touches mem Glob.mem{1} _out 1 /\
      load_zp Glob.mem{1} _out = inzp 0 /\
      inbounds (load_array Glob.mem{1} _out)
   ].
proof.
proc; unroll for {1} 2.
auto => /= &1 &2 [#] ?.
rewrite !to_uintD_small to_uint_small; first 7 by smt().
move => ????.
have E: R.bn_ofint 0 = Array4.init (fun i => W64.zero).
 apply R.bn_inj.
 rewrite R.bn_ofintK modz_small. smt.
 by rewrite R.bn2seq /bn_seq /= /to_list /mkseq -iotaredE.
split. 
+ rewrite /store_zp /unlift_zp /= !inzpK !modz_small /=. 
   smt(pVal).
  by rewrite E /store_array /= /#.
split. 
+ rewrite /touches /separate /load_array => a sep.
  apply Array4.ext_eq => x xbnd.
  by rewrite !initiE /=; smt(load_store_W64_eq load_store_W64_neq).
split. 
+ rewrite /load_zp /lift_zp /load_array  /=; congr.
  rewrite {5}(_:0 = valR (Array4.init (fun i => W64.zero))).
   rewrite -E R.bn_ofintK modz_small. smt.
   done.
  congr; apply Array4.ext_eq => x xbnd.
  by rewrite !initiE /=; smt(load_store_W64_eq load_store_W64_neq).
+ have -> : 
   (load_array
     (storeW64
        (storeW64 (storeW64 (storeW64 Glob.mem{1} (to_uint out{1}) W64.zero) (to_uint out{1} + 8) W64.zero)
           (to_uint out{1} + to_uint ((of_int 16))%W64) W64.zero) (to_uint out{1} + to_uint ((of_int 24))%W64) W64.zero) _out = Array4.init (fun i => W64.zero)).
    rewrite /load_array; apply Array4.ext_eq => x xb.
  rewrite !initiE /=; first 2 by smt(). 
  by smt(W4u64.get_zero load_store_W64_eq load_store_W64_neq).
  rewrite /inbounds R.bn2seq /bn_seq /to_list /mkseq -iotaredE /=.
  smt(pVal).
qed.

lemma ImplFp_xpnd v1 v2:
 ImplFp v1 v2 <=> inbounds v1 /\ v2 = lift_zp v1.
proof.
rewrite /lift_zp /inbounds; split.
 move=> ->; split.
  smt(rg_asint).
 by rewrite asintK.
move=> [Hbnd ->].
by rewrite inzpK modz_small 1:/#.
qed.

lemma ops_add_Impl:
   equiv [ M.addm ~ OpsZp.add_freeze :
           ImplFp a{1} v1{2} /\
           ImplFp b{1} v2{2}
           ==>
           ImplFp res{1} res{2}
         ].
proof.
transitivity ASpecFp.addm
 ( ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2} )
 ( a{1}=v1{2} /\ b{1}=v2{2} ==> ={res} ).
+ by move=> /> &1 &2 ??;  exists (v1{2},v2{2}).
+ by move=> /> *.
+ by apply addm_spec.
+ by proc; wp; skip; auto.
qed.

lemma ops_add _v1 _v2 mem :
   equiv [ M.addm ~ OpsZp.add_freeze :
       ={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds a{1} /\ inbounds b{1} /\
       v1{2} = lift_zp a{1} /\ v2{2} = lift_zp b{1} /\
       v1{2} = _v1 /\ v2{2} = _v2 
           ==>  
       ={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds res{1} /\ res{2} = fadd _v1 _v2 /\
        res{2} = lift_zp res{1}
   ].
proof.
transitivity OpsZp.add_freeze
 (={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds a{1} /\ inbounds b{1} /\
       v1{2} = lift_zp a{1} /\ v2{2} = lift_zp b{1} /\
       v1{2} = _v1 /\ v2{2} = _v2 
           ==>  
       ={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds res{1} /\  res{2} = lift_zp res{1})
 (={Glob.mem, v1, v2} /\ Glob.mem{1} = mem /\ v1{2}=_v1 /\ v2{2}=_v2
           ==>  
       ={Glob.mem, res} /\ Glob.mem{1} = mem /\
       res{2} = fadd _v1 _v2).
+ move=> /> &1 &2 *; exists mem (v1{2},v2{2}); smt().
+ move=> />; auto.
+ conseq ops_add_Impl.
   move => /> *.
   by rewrite !ImplFp_xpnd /#.
  move=> /> ??????????.
  rewrite ImplFp_xpnd; progress; smt().
+ proc; simplify.
  by skip => />.
qed.

lemma ops_sub_Impl:
   equiv [ M.subm ~ OpsZp.sub_freeze :
           ImplFp a{1} v1{2} /\
           ImplFp b{1} v2{2}
           ==>
           ImplFp res{1} res{2}
         ].
proof.
transitivity ASpecFp.subm
 ( ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2} )
 ( a{1}=v1{2} /\ b{1}=v2{2} ==> ={res} ).
+ by move=> /> &1 &2 ??;  exists (v1{2},v2{2}); auto.
+ by move=> /> *.
+ by apply subm_spec.
+ by proc; wp; skip; auto.
qed.

lemma ops_sub _v1 _v2 mem:
   equiv [ M.subm ~ OpsZp.sub_freeze :
       ={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds a{1} /\ inbounds b{1} /\
       v1{2} = lift_zp a{1} /\ v2{2} = lift_zp b{1} /\
       v1{2} = _v1 /\ v2{2} = _v2 
           ==>  
       ={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds res{1} /\ res{2} = fsub _v1 _v2 /\
        res{2} = lift_zp res{1}
   ].
proof.
transitivity OpsZp.sub_freeze
 (={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds a{1} /\ inbounds b{1} /\
       v1{2} = lift_zp a{1} /\ v2{2} = lift_zp b{1} /\
       v1{2} = _v1 /\ v2{2} = _v2 
           ==>  
       ={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds res{1} /\  res{2} = lift_zp res{1})
 (={Glob.mem, v1, v2} /\ Glob.mem{1} = mem /\ v1{2}=_v1 /\ v2{2}=_v2
           ==>  
       ={Glob.mem, res} /\ Glob.mem{1} = mem /\
       res{2} = fsub _v1 _v2).
+ move=> /> &1 &2 *; exists mem (v1{2},v2{2}); smt().
+ move=> />; auto.
+ conseq ops_sub_Impl.
   move => /> *.
   by rewrite !ImplFp_xpnd /#.
  move=> /> ??????????.
  rewrite ImplFp_xpnd; progress; smt().
+ proc; simplify.
  by skip => />.
qed.

lemma ops_mul_Impl:
   equiv [ M.mulm ~ OpsZp.mul_freeze :
           ImplFp a{1} v1{2} /\
           ImplFp b{1} v2{2}
           ==>
           ImplFp res{1} res{2}
         ].
proof.
transitivity ASpecFp.mulm
 ( ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2} )
 ( a{1}=v1{2} /\ b{1}=v2{2} ==> ={res} ).
+ by move=> /> &1 &2 ??;  exists (v1{2},v2{2}); auto.
+ by move=> /> *.
+ by apply mulm_spec.
+ by proc; wp; skip; auto.
qed.

lemma ops_mul _v1 _v2 mem :
   equiv [ M.mulm ~ OpsZp.mul_freeze :
       ={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds a{1} /\ inbounds b{1} /\
       v1{2} = lift_zp a{1} /\ v2{2} = lift_zp b{1} /\
       v1{2} = _v1 /\ v2{2} = _v2 
           ==>  
       ={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds res{1} /\ res{2} = fmul _v1 _v2 /\
        res{2} = lift_zp res{1}
   ].
proof.
transitivity OpsZp.mul_freeze
 (={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds a{1} /\ inbounds b{1} /\
       v1{2} = lift_zp a{1} /\ v2{2} = lift_zp b{1} /\
       v1{2} = _v1 /\ v2{2} = _v2 
           ==>  
       ={Glob.mem} /\ Glob.mem{1} = mem /\
       inbounds res{1} /\  res{2} = lift_zp res{1})
 (={Glob.mem, v1, v2} /\ Glob.mem{1} = mem /\ v1{2}=_v1 /\ v2{2}=_v2
           ==>  
       ={Glob.mem, res} /\ Glob.mem{1} = mem /\
       res{2} = fmul _v1 _v2).
+ move=> /> &1 &2 *; exists mem (v1{2},v2{2}); smt().
+ move=> />; auto.
+ conseq ops_mul_Impl.
   move => /> *.
   by rewrite !ImplFp_xpnd /#.
  move=> /> ??????????.
  rewrite ImplFp_xpnd; progress; smt().
+ proc; simplify.
  by skip => />.
qed.

module M25519 = {
  include M [-create_sharing,create_sharing_const,add5,createLastShare,input_start5,const_start5,smult5,mult_pair5,mult_start5,mult_end5,out_end5]

  proc create_sharing (outS:W64.t, randomnessS:W64.t) : unit = {
    
    var randomness:W64.t;
    var randomness1:W64.t;
    var out:W64.t;
    var aux1:W64.t;
    var aux2:W64.t;
    var i:int;
    
    randomness <- randomnessS;
    randomness1 <- randomness;
    out <- outS;
    aux2 <- (randomness1 + (W64.of_int ((5 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 16)));
    i <- 2;
    while (i < 30) {
       if (nth witness sharing_idx i = 9) {
          aux1 <- outS;
          aux2 <- (aux1 + (W64.of_int (4 * 8)));
       }
       else {
          aux2 <- (randomness1 + (W64.of_int (((nth witness sharing_idx i) * 4) * 8)));
       }
       copy_share (out, aux2);
       out <- (out + (W64.of_int (4 * 8)));
       i <- i + 1;
    }
    return ();
  }
  
  proc create_sharing_const (outS:W64.t, conS:W64.t, minusS:W64.t) : unit = {
    
    var out:W64.t;
    var x:W64.t;
    var minus:W64.t;
    
    out <- outS;
    x <- conS;
    minus <- minusS;
    out <- outS;
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    set0 (out);
    out <- (out + (W64.of_int (4 * 8)));
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    set0 (out);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    set0 (out);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    return ();
  }

  proc add5 (status:W64.t, w1:W64.t, w2:W64.t, curwire:W64.t) : W64.t = {
    var aux_0: int;
    
    var aux:W64.t;
    var wi:W64.t;
    var st:W64.t;
    var w1S:W64.t;
    var w2S:W64.t;
    var wresS:W64.t;
    var shareN:int;
    var i:int;
    var sw1:W64.t;
    var sw2:W64.t;
    var swres:W64.t;
    var xi:W64.t;
    var yi:W64.t;
    var resi:W64.t;
    var aux2:W64.t;
    var aux3:W64.t;
    var val1:W64.t;
    var val2:W64.t;
    var resval:W64.t;
    
    wi <- curwire;
    st <- status;
    w1S <- w1;
    w2S <- w2;
    wresS <- wi;
    shareN <- 0;
    while (shareN < 6) {
      i <- (shareN * 4);
      sw1 <- w1S;
      sw2 <- w2S;
      swres <- wresS;
      xi <- (sw1 * (W64.of_int 6));
      xi <- (xi * (W64.of_int 4));
      xi <- (xi + (W64.of_int i));
      yi <- (sw2 * (W64.of_int 6));
      yi <- (yi * (W64.of_int 4));
      yi <- (yi + (W64.of_int i));
      resi <- (swres * (W64.of_int 6));
      resi <- (resi * (W64.of_int 4));
      resi <- (resi + (W64.of_int i));
      aux <- (xi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      val1 <- aux3;
      aux <- (yi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      val2 <- aux3;
      aux <- (resi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      resval <- aux3;
      add_wrapper (val1, val2, resval);
      shareN <- shareN + 1;
    }
    aux <- wresS;
    aux <- (aux + (W64.of_int 1));
    return (aux);
  }
  
  proc createLastShare (randoms:W64.t, out2:W64.t, secret:W64.t) : unit = {
    var aux: int;
    
    var rd3:W64.t;
    var rd2:W64.t;
    var secretS:W64.t;
    var i:int;
    var si:int;
    var aux1:W64.t;
    var x:W64.t;
    var y:W64.t;
    
    rd3 <- randoms;
    rd2 <- out2;
    secretS <- secret;
    copy_share (rd2, rd3);
    aux <- (10 - 1);
    y <- witness;
    i <- 1;
    while (i < aux) {
      si <@ getShareIndex (i);
      rd3 <- randoms;
      aux1 <- (rd3 + (W64.of_int si));
      x <- aux1;
      y <- out2;
      add_wrapper (x, y, y);
      i <- i + 1;
    }
    sub_wrapper (secretS, y, y);
    return ();
  }

  proc input_start5 (input:W64.t, out:W64.t, randomness:W64.t) : unit = {
    
    var n:int;
    var outS:W64.t;
    var rd:W64.t;
    var outS2:W64.t;
    var randomnessS:W64.t;
    var secret:W64.t;
    
    n <- 10;
    outS <- out;
    rd <- (out + (W64.of_int 32));
    outS2 <- rd;
    rd <- randomness;
    randomnessS <- rd;
    secret <- input;
    createLastShare (randomnessS, outS2, secret);
    create_sharing (outS, randomnessS);
    return ();
  }
  
  
  proc const_start5 (input:W64.t, out:W64.t) : unit = {
    
    var conS:W64.t;
    var outS:W64.t;
    var i:int;
    var minus:W64.t;
    var minusS:W64.t;
    
    conS <- input;
    outS <- out;
    set0 (out);
    i <- ((2 * 4) * 8);
    minus <- (out + (W64.of_int i));
    minusS <- minus;
    sub_wrapper (outS, conS, minusS);
    create_sharing_const (outS, conS, minusS);
    return ();
  }
    
  proc smult5 (status:W64.t, w1:W64.t, wcons:W64.t, curwire:W64.t) : 
  W64.t = {
    var aux_0: int;
    
    var aux:W64.t;
    var wi:W64.t;
    var st:W64.t;
    var w1S:W64.t;
    var wresS:W64.t;
    var sw1:W64.t;
    var xi:W64.t;
    var aux2:W64.t;
    var aux3:W64.t;
    var val2:W64.t;
    var shareN:int;
    var i:int;
    var swres:W64.t;
    var resi:W64.t;
    var val1:W64.t;
    var resval:W64.t;
    
    wi <- curwire;
    st <- status;
    w1S <- w1;
    wresS <- wi;
    sw1 <- wcons;
    xi <- (sw1 * (W64.of_int 6));
    xi <- (xi * (W64.of_int 4));
    aux <- (xi * (W64.of_int 8));
    aux2 <- st;
    aux3 <- (aux2 + aux);
    val2 <- aux3;
    shareN <- 0;
    while (shareN < 6) {
      i <- (shareN * 4);
      sw1 <- w1S;
      swres <- wresS;
      xi <- (sw1 * (W64.of_int 6));
      xi <- (xi * (W64.of_int 4));
      xi <- (xi + (W64.of_int i));
      resi <- (swres * (W64.of_int 6));
      resi <- (resi * (W64.of_int 4));
      resi <- (resi + (W64.of_int i));
      aux <- (xi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      val1 <- aux3;
      aux <- (resi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      resval <- aux3;
      mult_wrapper (val1, val2, resval);
      shareN <- shareN + 1;
    }
    aux <- wresS;
    aux <- (aux + (W64.of_int 1));
    return (aux);
  }
  
  proc mult_pair5 (st:W64.t, resvalS:W64.t, sw1:W64.t, sw2:W64.t, share1:int,
                   share2:int) : unit = {
    
    var i1:int;
    var i2:int;
    var sw:W64.t;
    var xi:W64.t;
    var yi:W64.t;
    var aux:W64.t;
    var aux2:W64.t;
    var val1:W64.t;
    var val1S:W64.t;
    var val2:W64.t;
    var val2S:W64.t;
    
    i1 <- (share1 * 4);
    i2 <- (share2 * 4);
    sw <- sw1;
    xi <- (sw * (W64.of_int 6));
    xi <- (xi * (W64.of_int 4));
    xi <- (xi + (W64.of_int i1));
    sw <- sw2;
    yi <- (sw2 * (W64.of_int 6));
    yi <- (yi * (W64.of_int 4));
    yi <- (yi + (W64.of_int i2));
    aux <- (xi * (W64.of_int 8));
    aux2 <- st;
    val1 <- (aux2 + aux);
    val1S <- val1;
    aux <- (yi * (W64.of_int 8));
    aux2 <- st;
    val2 <- (aux2 + aux);
    val2S <- val2;
    mult_wrapper (val1S, val2S, resvalS);
    return ();
  }

  proc mult_start5 (status:W64.t, w1:W64.t, w2:W64.t, outI:W64.t,
                    randomnessI:W64.t) : unit = {
    
    var randomness:W64.t;
    var out:W64.t;
    var st:W64.t;
    var sw1:W64.t;
    var sw2:W64.t;
    var nShares:int;
    var aux1:W64.t;
    var valmult:W64.t;
    var crossc,ci,cj:int;
    
    set0 (outI);
    randomness <- randomnessI;
    out <- outI;
    st <- status;
    sw1 <- w1;
    sw2 <- w2;
    nShares <- (10 - 1);
    aux1 <- (outI + (W64.of_int 32));
    valmult <- aux1;

    crossc <- 0;
    while (crossc < 20) {
      (ci,cj) <- nth witness cross_idx crossc;
      mult_pair5 (st, valmult, sw1, sw2, ci, cj);
      add_wrapper (valmult, out, out);
      crossc <- crossc + 1;
    }

    aux1 <- out;
    createLastShare (randomness, valmult, aux1);
    create_sharing (out, randomness);
    return ();
  }
  
   
  proc mult_end5 (all_messages:W64.t, status:W64.t, curwire:W64.t) : 
  W64.t = {
    var aux: int;
    
    var aux1:W64.t;
    var wi:W64.t;
    var wiS:W64.t;
    var index:W64.t;
    var messages:W64.t;
    var st:W64.t;
    var wire:W64.t;
    var message:W64.t;
    var i:int;
    var si:int;
    var val:W64.t;
    var aux2:W64.t;
    var sumShare:W64.t;
    var p:int;
    var mi:int;
    var valS:W64.t;
    var sumShareS:W64.t;
    
    wi <- curwire;
    wiS <- wi;
    index <@ getWireIndex5 (wi);
    messages <- all_messages;
    st <- status;
    aux1 <- (st + index);
    wire <- aux1;
    message <- messages;
    i <- 0;
    while (i < 6) {
      si <- (i * 4);
      si <- (si * 8);
      aux1 <- message;
      val <- (aux1 + (W64.of_int si));
      aux2 <- wire;
      sumShare <- (aux2 + (W64.of_int si));
      copy_share (sumShare, val);
      i <- i + 1;
    }
    p <- 1;
    while (p < 5) {
      mi <- ((p * 6) * 4);
      mi <- (mi * 8);
      aux1 <- messages;
      aux2 <- (aux1 + (W64.of_int mi));
      message <- aux2;
      i <- 0;
      while (i < 6) {
        si <- (i * 4);
        si <- (si * 8);
        aux1 <- message;
        val <- (aux1 + (W64.of_int si));
        valS <- val;
        aux2 <- wire;
        sumShare <- (aux2 + (W64.of_int si));
        sumShareS <- sumShare;
        add_wrapper (valS, sumShareS, sumShareS);
        i <- i + 1;
      }
      p <- p + 1;
    }
    aux1 <- wiS;
    aux1 <- (aux1 + (W64.of_int 1));
    return (aux1);
  }
  
  proc out_end5 (all_messages:W64.t, out:W64.t, curwire:W64.t) : unit = {
    
    var wi:W64.t;
    var index:W64.t;
    var messages:W64.t;
    var sumShare:W64.t;
    var mi:int;
    var aux1:W64.t;
    var message:W64.t;
    var si:int;
    var aux2:W64.t;
    var val:W64.t;
    
    wi <- curwire;
    index <@ getWireIndex5 (wi);
    messages <- all_messages;
    sumShare <- out;
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (0 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    copy_share (out, aux2);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (1 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (2 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (3 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (4 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (5 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((1 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (0 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((1 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (1 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((1 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (3 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((2 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (1 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    return ();
  }
}.

equiv M25519_create_sharing :
   M.create_sharing ~ M25519.create_sharing :
   ={arg,Glob.mem} 
   ==> 
   ={res,Glob.mem}.
proc.
unroll for {2} 9.
rcondt {2} 65. 
move => *; inline *.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
by wp; skip => /=; move => *; rewrite /sharing_idx /=.
rcondt {2} 33. 
move => *; inline *.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
unroll for ^while.
by wp; skip => /=; move => *; rewrite /sharing_idx /=.
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
rcondf {2} ^if; 
 first by move => *;do (wp; call (_: true); auto). 
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
by wp; skip; rewrite /sharing_idx /= => /#. 
qed.

equiv M25519_add_wrapper :
   M.add_wrapper ~ M25519.add_wrapper :
   ={arg,Glob.mem} ==> ={res,Glob.mem}
by proc; inline *; sim.

equiv M25519_sub_wrapper :
   M.sub_wrapper ~ M25519.sub_wrapper :
   ={arg,Glob.mem} ==> ={res,Glob.mem}
by proc; inline *; sim.

equiv M25519_mul_wrapper :
   M.mult_wrapper ~ M25519.mult_wrapper :
   ={arg,Glob.mem} ==> ={res,Glob.mem}
by proc; inline *; sim.

equiv M25519_add5 :
   M.add5 ~ M25519.add5 :
   ={arg,Glob.mem} ==> ={res,Glob.mem}.
proc.
wp; while (={Glob.mem, shareN,wresS,st,w1S,w2S}). 
by wp; call M25519_add_wrapper; auto => />. 
by auto => />. 
qed.

equiv M25519_input_start5 :
   M.input_start5 ~ M25519.input_start5 :
   ={arg,Glob.mem} ==> ={res,Glob.mem}.
proc. inline M.createLastShare M25519.createLastShare  M.getShareIndex.
call M25519_create_sharing.
wp;call (M25519_sub_wrapper).
wp; while (={Glob.mem, i, randoms,out2, aux,outS,randomnessS,secretS} /\ (1 < i{1} => ={y})).
 by wp;call (M25519_add_wrapper); auto => />.
wp;call (_: ={Glob.mem} ); first by sim. 
auto => /> /#.
qed.

equiv M25519_const_start5 :
   M.const_start5 ~ M25519.const_start5 :
   ={arg,Glob.mem} ==> ={res,Glob.mem}.
proc.
inline M.create_sharing_const M25519.create_sharing_const.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (_: ={Glob.mem}); first by sim.
wp;call (M25519_sub_wrapper).
wp;call (_: ={Glob.mem}); first by sim.
by auto => />.
qed.

equiv M25519_smult5 :
   M.smult5 ~ M25519.smult5 :
   ={arg,Glob.mem} ==> ={res,Glob.mem}.
proc.
unroll for {1} 13.
unroll for {2} 13.
wp;call (M25519_mul_wrapper).
wp;call (M25519_mul_wrapper).
wp;call (M25519_mul_wrapper).
wp;call (M25519_mul_wrapper).
wp;call (M25519_mul_wrapper).
wp;call (M25519_mul_wrapper).
by auto => />.
qed.

equiv M25519_mult_pair5 :
   M.mult_pair5 ~ M25519.mult_pair5 :
   ={arg,Glob.mem} ==> ={res,Glob.mem}
  by proc;call M25519_mul_wrapper; auto => />. 

equiv M25519_mult_start5 :
   M.mult_start5 ~ M25519.mult_start5 :
   ={arg,Glob.mem} ==> ={res,Glob.mem}.
proc.
inline M.createLastShare M25519.createLastShare  M.getShareIndex.
unroll for {2} 11. 
call M25519_create_sharing.
call M25519_sub_wrapper.
while (#{/~(secretS{1}, y{1}, y{1}) = (secretS{2}, y{2}, y{2})}post /\ 
        ={i,randoms,out2,aux,secretS} /\ 
       (1<i{1} => ={y}) /\ 0 <= i{1} <= aux{1} /\ aux{1} = 9).
wp;call M25519_add_wrapper. 
by wp;skip; auto => /> /#. 
wp;call(_: ={Glob.mem}); first by sim.
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call M25519_add_wrapper. 
wp;call M25519_mult_pair5. 
wp;call(_: ={Glob.mem}); first by sim.
by auto => />; rewrite /cross_idx /= => /#.
qed.

equiv M25519_mult_end5 :
   M.mult_end5 ~ M25519.mult_end5 :
   ={arg,Glob.mem} ==> ={res,Glob.mem}.
proc.
wp; while (#post /\ ={p,wire,messages} /\ 1 <= p{1} <= 5).
wp; while (#post /\ ={i,message} /\ 0 <= i{1} <= 6).
wp;call M25519_add_wrapper. 
by auto => /> /#.
by auto => /> /#.
wp; while (#post /\ ={i,message} /\ 0 <= i{1} <= 6).
wp;call (_: ={Glob.mem}); first by sim.
by auto => /> /#.
wp;call(_: ={Glob.mem}); first by sim.
by auto => />.
qed.

equiv M25519_out_start5 :
   M.out_start5 ~ M25519.out_start5 :
   ={arg,Glob.mem} ==> ={res,Glob.mem} by sim.

equiv M25519_out_end5 :
   M.out_end5 ~ M25519.out_end5 :
   ={arg,Glob.mem} ==> ={res,Glob.mem}.
proc. 
wp;call(M25519_add_wrapper).
wp;call(M25519_add_wrapper).
wp;call(M25519_add_wrapper).
wp;call(M25519_add_wrapper).
wp;call(M25519_add_wrapper).
wp;call(M25519_add_wrapper).
wp;call(M25519_add_wrapper).
wp;call(M25519_add_wrapper).
wp;call(M25519_add_wrapper).
wp;call(_: ={Glob.mem}); first by sim.
by inline *; auto => />.
qed.

module MZp = {
  include M25519 [-add_wrapper, sub_wrapper, mult_wrapper,add5,create_sharing_const,createLastShare,input_start5,const_start5,smult5,mult_pair5,mult_start5,mult_end5,out_end5]

  proc add_wrapper (v1S:W64.t, v2S:W64.t, resS:W64.t) : unit = {
    
    var aux:W64.t;
    var aux2:W64.t;
    var v1:t;
    var v2:t;
    var toFreeze:W64.t Array4.t;
    var res_0:t;
    res_0 <- witness;
    toFreeze <- witness;
    v1 <- witness;
    v2 <- witness;
    aux <- v1S;
    aux2 <- v2S;
    v1 <@ OpsZp.load_array (aux);
    v2 <@ OpsZp.load_array (aux2);
    res_0 <@ OpsZp.add_freeze (v1, v2);
    aux <- resS;
    OpsZp.store_array (aux, res_0);
    return ();
  }
  
  proc mult_wrapper (v1S:W64.t, v2S:W64.t, resS:W64.t) : unit = {
    
    var aux:W64.t;
    var aux2:W64.t;
    var v1:t;
    var v2:t;
    var toFreeze:W64.t Array4.t;
    var res_0:t;
    res_0 <- witness;
    toFreeze <- witness;
    v1 <- witness;
    v2 <- witness;
    aux <- v1S;
    aux2 <- v2S;
    v1 <@ OpsZp.load_array (aux);
    v2 <@ OpsZp.load_array (aux2);
    res_0 <@ OpsZp.mul_freeze (v1, v2);
    aux <- resS;
    OpsZp.store_array (aux, res_0);
    return ();
  }
  
  proc sub_wrapper (v1S:W64.t, v2S:W64.t, resS:W64.t) : unit = {
    
    var aux:W64.t;
    var aux2:W64.t;
    var v1:t;
    var v2:t;
    var toFreeze:W64.t Array4.t;
    var res_0:t;
    res_0 <- witness;
    toFreeze <- witness;
    v1 <- witness;
    v2 <- witness;
    aux <- v1S;
    aux2 <- v2S;
    v1 <@ OpsZp.load_array (aux);
    v2 <@ OpsZp.load_array (aux2);
    res_0 <@ OpsZp.sub_freeze (v1, v2);
    aux <- resS;
    OpsZp.store_array (aux, res_0);
    return ();
  }

 proc create_sharing_const (outS:W64.t, conS:W64.t, minusS:W64.t) : unit = {
    
    var out:W64.t;
    var x:W64.t;
    var minus:W64.t;
    
    out <- outS;
    x <- conS;
    minus <- minusS;
    out <- outS;
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    OpsZp.set0 (out);
    out <- (out + (W64.of_int (4 * 8)));
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    OpsZp.set0 (out);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    OpsZp.set0 (out);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    return ();
  }

  proc add5 (status:W64.t, w1:W64.t, w2:W64.t, curwire:W64.t) : W64.t = {
    var aux_0: int;
    
    var aux:W64.t;
    var wi:W64.t;
    var st:W64.t;
    var w1S:W64.t;
    var w2S:W64.t;
    var wresS:W64.t;
    var shareN:int;
    var i:int;
    var sw1:W64.t;
    var sw2:W64.t;
    var swres:W64.t;
    var xi:W64.t;
    var yi:W64.t;
    var resi:W64.t;
    var aux2:W64.t;
    var aux3:W64.t;
    var val1:W64.t;
    var val2:W64.t;
    var resval:W64.t;
    
    wi <- curwire;
    st <- status;
    w1S <- w1;
    w2S <- w2;
    wresS <- wi;
    shareN <- 0;
    while (shareN < 6) {
      i <- (shareN * 4);
      sw1 <- w1S;
      sw2 <- w2S;
      swres <- wresS;
      xi <- (sw1 * (W64.of_int 6));
      xi <- (xi * (W64.of_int 4));
      xi <- (xi + (W64.of_int i));
      yi <- (sw2 * (W64.of_int 6));
      yi <- (yi * (W64.of_int 4));
      yi <- (yi + (W64.of_int i));
      resi <- (swres * (W64.of_int 6));
      resi <- (resi * (W64.of_int 4));
      resi <- (resi + (W64.of_int i));
      aux <- (xi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      val1 <- aux3;
      aux <- (yi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      val2 <- aux3;
      aux <- (resi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      resval <- aux3;
      add_wrapper (val1, val2, resval);
      shareN <- shareN + 1;
    }
    aux <- wresS;
    aux <- (aux + (W64.of_int 1));
    return (aux);
  }
 
 proc createLastShare (randoms:W64.t, out2:W64.t, secret:W64.t) : unit = {
    var aux: int;
    
    var rd3:W64.t;
    var rd2:W64.t;
    var secretS:W64.t;
    var i:int;
    var si:int;
    var aux1:W64.t;
    var x:W64.t;
    var y:W64.t;
    
    rd3 <- randoms;
    rd2 <- out2;
    secretS <- secret;
    copy_share (rd2, rd3);
    aux <- (10 - 1);
    y <- witness;
    i <- 1;
    while (i < aux) {
      si <@ getShareIndex (i);
      rd3 <- randoms;
      aux1 <- (rd3 + (W64.of_int si));
      x <- aux1;
      y <- out2;
      add_wrapper (x, y, y);
      i <- i + 1;
    }
    sub_wrapper (secretS, y, y);
    return ();
  }

  proc input_start5 (input:W64.t, out:W64.t, randomness:W64.t) : unit = {
    
    var n:int;
    var outS:W64.t;
    var rd:W64.t;
    var outS2:W64.t;
    var randomnessS:W64.t;
    var secret:W64.t;
    
    n <- 10;
    outS <- out;
    rd <- (out + (W64.of_int 32));
    outS2 <- rd;
    rd <- randomness;
    randomnessS <- rd;
    secret <- input;
    createLastShare (randomnessS, outS2, secret);
    create_sharing (outS, randomnessS);
    return ();
  }
  
    
  proc const_start5 (input:W64.t, out:W64.t) : unit = {
    
    var conS:W64.t;
    var outS:W64.t;
    var i:int;
    var minus:W64.t;
    var minusS:W64.t;
    
    conS <- input;
    outS <- out;
    OpsZp.set0 (out);
    i <- ((2 * 4) * 8);
    minus <- (out + (W64.of_int i));
    minusS <- minus;
    sub_wrapper (outS, conS, minusS);
    create_sharing_const (outS, conS, minusS);
    return ();
  }
    
  proc smult5 (status:W64.t, w1:W64.t, wcons:W64.t, curwire:W64.t) : 
  W64.t = {
    var aux_0: int;
    
    var aux:W64.t;
    var wi:W64.t;
    var st:W64.t;
    var w1S:W64.t;
    var wresS:W64.t;
    var sw1:W64.t;
    var xi:W64.t;
    var aux2:W64.t;
    var aux3:W64.t;
    var val2:W64.t;
    var shareN:int;
    var i:int;
    var swres:W64.t;
    var resi:W64.t;
    var val1:W64.t;
    var resval:W64.t;
    
    wi <- curwire;
    st <- status;
    w1S <- w1;
    wresS <- wi;
    sw1 <- wcons;
    xi <- (sw1 * (W64.of_int 6));
    xi <- (xi * (W64.of_int 4));
    aux <- (xi * (W64.of_int 8));
    aux2 <- st;
    aux3 <- (aux2 + aux);
    val2 <- aux3;
    shareN <- 0;
    while (shareN < 6) {
      i <- (shareN * 4);
      sw1 <- w1S;
      swres <- wresS;
      xi <- (sw1 * (W64.of_int 6));
      xi <- (xi * (W64.of_int 4));
      xi <- (xi + (W64.of_int i));
      resi <- (swres * (W64.of_int 6));
      resi <- (resi * (W64.of_int 4));
      resi <- (resi + (W64.of_int i));
      aux <- (xi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      val1 <- aux3;
      aux <- (resi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      resval <- aux3;
      mult_wrapper (val1, val2, resval);
      shareN <- shareN + 1;
    }
    aux <- wresS;
    aux <- (aux + (W64.of_int 1));
    return (aux);
  }
  
  proc mult_pair5 (st:W64.t, resvalS:W64.t, sw1:W64.t, sw2:W64.t, share1:int,
                   share2:int) : unit = {
    
    var i1:int;
    var i2:int;
    var sw:W64.t;
    var xi:W64.t;
    var yi:W64.t;
    var aux:W64.t;
    var aux2:W64.t;
    var val1:W64.t;
    var val1S:W64.t;
    var val2:W64.t;
    var val2S:W64.t;
    
    i1 <- (share1 * 4);
    i2 <- (share2 * 4);
    sw <- sw1;
    xi <- (sw * (W64.of_int 6));
    xi <- (xi * (W64.of_int 4));
    xi <- (xi + (W64.of_int i1));
    sw <- sw2;
    yi <- (sw2 * (W64.of_int 6));
    yi <- (yi * (W64.of_int 4));
    yi <- (yi + (W64.of_int i2));
    aux <- (xi * (W64.of_int 8));
    aux2 <- st;
    val1 <- (aux2 + aux);
    val1S <- val1;
    aux <- (yi * (W64.of_int 8));
    aux2 <- st;
    val2 <- (aux2 + aux);
    val2S <- val2;
    mult_wrapper (val1S, val2S, resvalS);
    return ();
  }

  proc mult_start5 (status:W64.t, w1:W64.t, w2:W64.t, outI:W64.t,
                    randomnessI:W64.t) : unit = {
    
    var randomness:W64.t;
    var out:W64.t;
    var st:W64.t;
    var sw1:W64.t;
    var sw2:W64.t;
    var nShares:int;
    var aux1:W64.t;
    var valmult:W64.t;
    var crossc,ci,cj:int;
    
    OpsZp.set0 (outI);
    randomness <- randomnessI;
    out <- outI;
    st <- status;
    sw1 <- w1;
    sw2 <- w2;
    nShares <- (10 - 1);
    aux1 <- (outI + (W64.of_int 32));
    valmult <- aux1;

    crossc <- 0;
    while (crossc < 20) {
      (ci,cj) <- nth witness cross_idx crossc;
      mult_pair5 (st, valmult, sw1, sw2, ci, cj);
      add_wrapper (valmult, out, out);
      crossc <- crossc + 1;
    }

    aux1 <- out;
    createLastShare (randomness, valmult, aux1);
    create_sharing (out, randomness);
    return ();
  }
  
  
  proc mult_end5 (all_messages:W64.t, status:W64.t, curwire:W64.t) : 
  W64.t = {
    var aux: int;
    
    var aux1:W64.t;
    var wi:W64.t;
    var wiS:W64.t;
    var index:W64.t;
    var messages:W64.t;
    var st:W64.t;
    var wire:W64.t;
    var message:W64.t;
    var i:int;
    var si:int;
    var val:W64.t;
    var aux2:W64.t;
    var sumShare:W64.t;
    var p:int;
    var mi:int;
    var valS:W64.t;
    var sumShareS:W64.t;
    
    wi <- curwire;
    wiS <- wi;
    index <@ getWireIndex5 (wi);
    messages <- all_messages;
    st <- status;
    aux1 <- (st + index);
    wire <- aux1;
    message <- messages;
    i <- 0;
    while (i < 6) {
      si <- (i * 4);
      si <- (si * 8);
      aux1 <- message;
      val <- (aux1 + (W64.of_int si));
      aux2 <- wire;
      sumShare <- (aux2 + (W64.of_int si));
      copy_share (sumShare,val);
      i <- i + 1;
    }
    p <- 1;
    while (p < 5) {
      mi <- ((p * 6) * 4);
      mi <- (mi * 8);
      aux1 <- messages;
      aux2 <- (aux1 + (W64.of_int mi));
      message <- aux2;
      i <- 0;
      while (i < 6) {
        si <- (i * 4);
        si <- (si * 8);
        aux1 <- message;
        val <- (aux1 + (W64.of_int si));
        valS <- val;
        aux2 <- wire;
        sumShare <- (aux2 + (W64.of_int si));
        sumShareS <- sumShare;
        add_wrapper (valS, sumShareS, sumShareS);
        i <- i + 1;
      }
      p <- p + 1;
    }
    aux1 <- wiS;
    aux1 <- (aux1 + (W64.of_int 1));
    return (aux1);
  }
  
  proc out_end5 (all_messages:W64.t, out:W64.t, curwire:W64.t) : unit = {
    
    var wi:W64.t;
    var index:W64.t;
    var messages:W64.t;
    var sumShare:W64.t;
    var mi:int;
    var aux1:W64.t;
    var message:W64.t;
    var si:int;
    var aux2:W64.t;
    var val:W64.t;
    
    wi <- curwire;
    index <@ getWireIndex5 (wi);
    messages <- all_messages;
    sumShare <- out;
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (0 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (1 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (2 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (3 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (4 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (5 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((1 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (0 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((1 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (1 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((1 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (3 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((2 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (1 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    return ();
  }

}.

lemma load_store_zp_bound mem a vv:
  inbounds (load_array (store_zp mem a vv) a).
proof.
rewrite /store_zp load_store_array_eq /unlift_zp /inbounds.
rewrite R.bn_ofintK modz_small. smt. smt(rg_asint).
qed.

lemma load_store_zp_array_neq mem a1 a2 vv:
  (a2 + 32 <= a1 || a1 + 32 <= a2) => 
  load_array (store_zp mem a1 vv) a2 = load_array mem a2.
proof.
by move=> H; rewrite /store_zp load_store_array_neq /#.
qed.

equiv MZp_add_wrapper mem resw _v1 _v2:
   M25519.add_wrapper ~ MZp.add_wrapper :
   mem = Glob.mem{1} /\ 
   resw = to_uint resS{1} /\
   load_zp Glob.mem{1} (to_uint v1S{1}) = _v1 /\
   load_zp Glob.mem{1} (to_uint v2S{1}) = _v2 /\
   to_uint v1S{1} < W64.modulus - 24 /\ 
   to_uint v2S{1} < W64.modulus - 24 /\ 
   to_uint resS{1} < W64.modulus - 24 /\ 
   inbounds (load_array Glob.mem{1} (to_uint v1S{1})) /\ 
   inbounds (load_array Glob.mem{1} (to_uint v2S{1})) /\
   ={arg,Glob.mem} ==> ={res,Glob.mem} /\
   touches mem Glob.mem{1} resw 1 /\
   load_zp Glob.mem{1} resw = (fadd _v1 _v2) /\
   inbounds (load_array Glob.mem{1} resw).
proof.
proc.
ecall (ops_store' mem aux{2} res_0{2}).
wp; ecall (ops_add v1{2} v2{2} mem).
ecall (ops_load' mem aux2{2}).
wp; ecall (ops_load' mem aux{2}).
wp; skip => /> /#.
qed.

equiv MZp_sub_wrapper mem resw _v1 _v2:
   M25519.sub_wrapper ~ MZp.sub_wrapper :
   mem = Glob.mem{1} /\ 
   resw = to_uint resS{1} /\
   load_zp Glob.mem{1} (to_uint v1S{1}) = _v1 /\
   load_zp Glob.mem{1} (to_uint v2S{1}) = _v2 /\
   to_uint v1S{1} < W64.modulus - 24 /\ 
   to_uint v2S{1} < W64.modulus - 24 /\ 
   to_uint resS{1} < W64.modulus - 24 /\ 
   inbounds (load_array Glob.mem{1} (to_uint v1S{1})) /\ 
   inbounds (load_array Glob.mem{1} (to_uint v2S{1})) /\
   ={arg,Glob.mem} ==> ={res,Glob.mem} /\
   touches mem Glob.mem{1} resw 1 /\
   load_zp Glob.mem{1} resw = (fsub _v1 _v2) /\
   inbounds (load_array Glob.mem{1} resw).
proof.
proc.
ecall (ops_store' mem aux{2} res_0{2}).
wp; ecall (ops_sub v1{2} v2{2} mem).
ecall (ops_load' mem aux2{2}).
wp; ecall (ops_load' mem aux{2}).
wp; skip => /> /#.
qed.

equiv MZp_mul_wrapper mem resw _v1 _v2:
   M25519.mult_wrapper ~ MZp.mult_wrapper :
   mem = Glob.mem{1} /\ 
   resw = to_uint resS{1} /\
   load_zp Glob.mem{1} (to_uint v1S{1}) = _v1 /\
   load_zp Glob.mem{1} (to_uint v2S{1}) = _v2 /\
   to_uint v1S{1} < W64.modulus - 24 /\ 
   to_uint v2S{1} < W64.modulus - 24 /\ 
   to_uint resS{1} < W64.modulus - 24 /\ 
   inbounds (load_array Glob.mem{1} (to_uint v1S{1})) /\ 
   inbounds (load_array Glob.mem{1} (to_uint v2S{1})) /\
   ={arg,Glob.mem} ==> ={res,Glob.mem} /\
   touches mem Glob.mem{1} resw 1 /\
   load_zp Glob.mem{1} resw = (fmul _v1 _v2) /\
   inbounds (load_array Glob.mem{1} resw).
proof.
proc.
ecall (ops_store' mem aux{2} res_0{2}).
wp; ecall (ops_mul v1{2} v2{2} mem).
wp; ecall (ops_load' mem aux2{2}).
wp; ecall (ops_load_stack' mem aux{2}).
wp; skip => /> /#.
qed.
