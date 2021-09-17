require import AllCore SmtMap ZModP List FSet Distr DList.

require import Array5 Array6 Array9 Array10.

require import AuxList AuxFSet AuxSmtMap AuxArray.
require import Maurer5SS.

theory Maurer5Spec.

clone import Maurer5SS.

import Maurer5SS.
import PF.

op add_shr (s1 s2 : shr) : shr = (Array6.map2 fadd s1 s2).

lemma add_shr_commute s1 s2 r1 r2 :
      let sh1 = share s1 r1 in
      let sh2 = share s2 r2 in
      let add0 = add_shr sh1.[0] sh2.[0] in
      let add1 = add_shr sh1.[1] sh2.[1] in
      let add2 = add_shr sh1.[2] sh2.[2] in
      let add3 = add_shr sh1.[3] sh2.[3] in
      let add4 = add_shr sh1.[4] sh2.[4] in
      let adds = Array5.of_list witness (add0::add1::add2::add3::add4::[]) in
      unshare adds = fadd s1  s2.
proof.
rewrite /share /rshare /add_shr /unshare /init_sh /shr_idx /sum_rand /to_list /mkseq /=.
rewrite (_: iota_ 0 9 = 0::1::2::3::4::5::6::7::8::[]); first by smt(iotaS iota0).
by simplify;ring.
qed.

lemma add_shr_strong (sh1 sh2 : shrs) : 
      let add0 = add_shr sh1.[0] sh2.[0] in
      let add1 = add_shr sh1.[1] sh2.[1] in
      let add2 = add_shr sh1.[2] sh2.[2] in
      let add3 = add_shr sh1.[3] sh2.[3] in
      let add4 = add_shr sh1.[4] sh2.[4] in
      let adds = Array5.of_list witness (add0::add1::add2::add3::add4::[]) in
      fadd (unshare sh1)  (unshare sh2) = unshare adds.
rewrite /add_shr /unshare /init_sh /shr_idx /sum_rand /to_list /mkseq /=.
by simplify;ring.
qed.

op cross(sh1 sh2 : shr) : val = 
            fadd (fmul sh1.[0] sh2.[0])
           (fadd (fmul sh1.[0] sh2.[1])
           (fadd (fmul sh1.[0] sh2.[2])
           (fadd (fmul sh1.[0] sh2.[4]) 
           (fadd (fmul sh1.[1] sh2.[3]) 
           (fadd (fmul sh1.[1] sh2.[4]) 
           (fadd (fmul sh1.[1] sh2.[5]) 
           (fadd (fmul sh1.[2] sh2.[0]) 
           (fadd (fmul sh1.[2] sh2.[2]) 
           (fadd (fmul sh1.[2] sh2.[3]) 
           (fadd (fmul sh1.[2] sh2.[4]) 
           (fadd (fmul sh1.[3] sh2.[0]) 
           (fadd (fmul sh1.[3] sh2.[1]) 
           (fadd (fmul sh1.[3] sh2.[2]) 
           (fadd (fmul sh1.[3] sh2.[5]) 
           (fadd (fmul sh1.[4] sh2.[1]) 
           (fadd (fmul sh1.[4] sh2.[2]) 
           (fadd (fmul sh1.[4] sh2.[3]) 
           (fadd (fmul sh1.[5] sh2.[0]) 
                 (fmul sh1.[5] sh2.[3]))))))))))))))))))).

lemma mul_shr_commute s1 s2 r1 r2 rc0 rc1 rc2 rc3 rc4 :      
      let sh1 = share s1 r1 in
      let sh2 = share s2 r2 in
      let cross0 = share (cross sh1.[0] sh2.[0]) rc0 in
      let cross1 = share (cross sh1.[1] sh2.[1]) rc1 in
      let cross2 = share (cross sh1.[2] sh2.[2]) rc2 in
      let cross3 = share (cross sh1.[3] sh2.[3]) rc3 in
      let cross4 = share (cross sh1.[4] sh2.[4]) rc4 in
      let add0 = add_shr cross0.[0] 
                (add_shr cross1.[0] 
                (add_shr cross2.[0] 
                (add_shr cross3.[0] cross4.[0]))) in
      let add1 = add_shr cross0.[1] 
                (add_shr cross1.[1] 
                (add_shr cross2.[1] 
                (add_shr cross3.[1] cross4.[1]))) in
      let add2 = add_shr cross0.[2] 
                (add_shr cross1.[2] 
                (add_shr cross2.[2] 
                (add_shr cross3.[2] cross4.[2]))) in
      let add3 = add_shr cross0.[3] 
                (add_shr cross1.[3] 
                (add_shr cross2.[3] 
                (add_shr cross3.[3] cross4.[3]))) in
      let add4 = add_shr cross0.[4] 
                (add_shr cross1.[4] 
                (add_shr cross2.[4] 
                (add_shr cross3.[4] cross4.[4]))) in
      let adds = Array5.of_list witness (add0::add1::add2::add3::add4::[]) in
      unshare adds = fmul s1  s2.
rewrite /share /rshare /cross /add_shr /unshare /init_sh /shr_idx /sum_rand /to_list /mkseq /=.
rewrite (_: iota_ 0 9 = 0::1::2::3::4::5::6::7::8::[]); first by smt(iotaS iota0).
by simplify; ring.
qed.

(* Data types *)

type wid = int.

type wire_st = wid * (wid,shr) fmap.

type msg = shr. 
    (* parties always prepare full sharings 
       we model own share keeping as msg so self *)
type msgs = msg Array5.t.

(* Gates that require interaction *)

op input_start(v : val, r : rand) : msgs = share v r.
op input_end(m : msg, wst : wire_st) : wire_st = 
     let (w,wires) = wst in
         (w + 1, wires.[w <- m]).

op output_start(wo : wid, wst : wire_st) : msgs = 
     let (w,wires) = wst in
        Array5.create (oget wires.[wo]).

op output_end(ms : msgs) : val = unshare ms.

op mul_start(wi wj : wid, wst : wire_st, r : rand) : msgs =      
     let (w,wires) = wst in
     let swi = oget wires.[wi] in
     let swj = oget wires.[wj] in
         share (cross swi swj) r.

op mul_end(ms : msgs, wst : wire_st) : wire_st = 
     let (w,wires) = wst in
     let ss = add_shr ms.[0] ms.[1] in
     let ss = add_shr ss     ms.[2] in
     let ss = add_shr ss     ms.[3] in
     let ss = add_shr ss     ms.[4] in
               (w + 1, wires.[w <- ss]).

(* Gates computed locally *)

op add(wi wj : wid, wst : wire_st) : wire_st =
  let (w,wires) = wst in
  let ash = add_shr (oget wires.[wi]) (oget wires.[wj]) in
  (w+1,wires.[w <- ash]).

op cnst(wi: wid) (v:val) (wst : wire_st) : wire_st =
  let (w,wires) = wst in
  let csh = (pshare v).[wi] in
  (w+1,wires.[w <- csh]).
         
op smul(wi wc : wid, wst : wire_st) : wire_st =
  let (w,wires) = wst in
  let cv = (oget wires.[wc]).[0] in
  let ash = Array6.map (fmul cv) (oget wires.[wi]) in
  (w+1,wires.[w <- ash]).

(*Additional share reconstruction functions - used in the MPC security simulator *)

  (* add party shares to raw share *)
  op add_p_shr (pid:int) (shr:Maurer5SS.shr) (rs:(Maurer5SS.val option) Array10.t) : (Maurer5SS.val option) Array10.t =
  let is = shr_idx pid in
  foldl (fun (rs:(Maurer5SS.val option) Array10.t) i => rs.[nth witness is i <- Some shr.[i] ]) rs (iseq 6).

  (* fill one raw share with one missing partial share *)
  op fill_rshr (v: zp) (rs:(zp option) Array10.t) : Maurer5SS.rshr =
  let sum = foldr (fun x y => fadd (odflt zero x) y) zero (Array10.to_list rs) in
  Array10.map (fun r => if r = None then fsub v sum else oget r) rs.

  op reconstruct_rshr (v:Maurer5SS.val) (cr:(wid,Maurer5SS.shr) fmap): Maurer5SS.rshr =
  let rs0 = Array10.create None in
  let rs1 = fold (fun pid rs =>
     let wi = oget (cr.[pid]) in
     add_p_shr pid wi rs)
        rs0 (fdom cr) in
  fill_rshr v rs1.

  op reconstruct_shrs (v:Maurer5SS.val) (cr:(wid,Maurer5SS.shr) fmap): Maurer5SS.shrs =
    share_raw (reconstruct_rshr v cr).

end Maurer5Spec.

