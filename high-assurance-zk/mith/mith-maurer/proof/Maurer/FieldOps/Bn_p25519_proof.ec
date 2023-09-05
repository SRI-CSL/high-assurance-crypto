require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

from JasminExtra require import JBigNum.


require import Maurer5_jazz.
require import Zp25519.

import Zp W64x4 R.

import Array8 Array4.


lemma x2r_h _x0 _x1 _x2 _x3:
 hoare [ M.x2r : x0=_x0 /\ x1=_x1 /\ x2=_x2 /\ x3=_x3 ==> res = Array4.of_list W64.zero [_x0; _x1; _x2; _x3] ].
proof.
proc; simplify; wp; skip => />.
by rewrite -ext_eq_all /all_eq.
qed.

lemma x2r_ll: islossless M.x2r by proc; islossless.

lemma x2r_ph _x0 _x1 _x2 _x3:
 phoare [ M.x2r : x0=_x0 /\ x1=_x1 /\ x2=_x2 /\ x3=_x3 ==> res = Array4.of_list W64.zero [_x0; _x1; _x2; _x3] ] = 1%r.
proof. by conseq x2r_ll (x2r_h _x0 _x1 _x2 _x3). qed.

lemma r2x_h _x:
 hoare [ M.r2x : x=_x ==> res = (_x.[0], _x.[1], _x.[2], _x.[3]) ].
proof. by proc; simplify; wp; skip => />. qed.

lemma r2x_ll: islossless M.r2x by proc; islossless.

lemma r2x_ph _x:
 phoare [ M.r2x : x=_x ==> res = (_x.[0], _x.[1], _x.[2], _x.[3]) ] = 1%r.
proof. by conseq r2x_ll (r2x_h _x). qed.

equiv eq_spec:
 M.bn_eq ~ ASpecFp.eqn:
  ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2}
  ==> to_uint res{1} = b2i res{2}.
proof.
transitivity 
 R.Ops.eqR
 ( ={a,b} ==> to_uint res{1} = b2i res{2} )
 ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2}
   ==> ={res} ).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1}).
+ by move=> /> *.
+ proc; simplify.
  wp; while (={a,b,i,acc} /\ 0 <= i{2} <= nlimbs).
   by wp; skip => /> /#.
  wp; skip => />; progress.
  by case: ((AND_64 acc_R acc_R).`5); smt().
+ proc; simplify.
  transitivity {1}
   { zf <@ R.Ops.eqR(a,b); }
   ( ={a,b} ==> ={zf} )
   ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} ==> zf{1} = r{2} ).
  + by move=> /> &2 *; exists a{2} b{2} => /#.
  + by auto.
  + by inline*; sim.
  + ecall {1} (R.eqR_ph a{1} b{1}).
    wp; skip => /> &m .
    case: (a{m}=b{m}) => E; first smt().
    rewrite eq_sym neqF.
    apply (contra _ (a{m}=b{m})); last done.
    by apply R.bn_inj.
qed.

equiv eq0_spec:
 M.bn_test0 ~ ASpecFp.eqn0:
  ImplZZ a{1} a{2}
  ==> to_uint res{1} = b2i res{2}.
proof.
transitivity 
 R.Ops.test0R
 ( ={a} ==> to_uint res{1} = b2i res{2} )
 ( ImplZZ a{1} a{2} ==> ={res} ).
+ by move=> /> &1 *; exists a{1}.
+ by move=> /> *.
+ proc; simplify.
  wp; while (={a,i,acc} /\ 0 <= i{2} <= nlimbs).
   by wp; skip => /> /#.
  wp; skip => />; progress.
  by case: ((AND_64 acc_R acc_R).`5); smt().
+ proc; simplify.
  transitivity {1}
   { zf <@ R.Ops.test0R(a); }
   ( ={a} ==> ={zf} )
   ( ImplZZ a{1} a{2} ==> zf{1} = r{2} ).
  + by move=> /> &2 *; exists a{2} => /#.
  + by auto.
  + by inline*; sim.
  + ecall {1} (R.test0R_ph a{1}).
    by wp; skip => /> &m .
qed.

equiv addc_spec:
 M.bn_addc ~ ASpecFp.addn:
  ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2}
  ==> res{1}.`1=res{2}.`1 /\ ImplZZ res{1}.`2 res{2}.`2.
proof.
transitivity 
 R.Ops.addcR
 ( ={a,b} /\ !c{2} ==> ={res} )
 ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ !c{1}
   ==> res{1}.`1 = res{2}.`1 /\ ImplZZ res{1}.`2 res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= nlimbs /\
         (cf,aa){1}=(c,a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k]) /\
         (forall k, i{2} <= k < nlimbs => a{1}.[k] = aa.[k])).
   wp; skip => /> &1 &2 Hi1 Hi2 H1 H2 Hi.
   split => *; first smt().
   split => *; first smt().
   split.
    move=> k Hk1 Hk2.
    pose X := (addc _ _ _)%W64.
    pose Y := (addc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?.
     by rewrite !set_eqiE /#.
    by rewrite !set_neqiE /#.
   move=> k Hk1 Hk2.
   by rewrite set_neqiE /#.
  wp; skip => /> &2.
  move=> Hc; split => *.
   split => k *.
    by rewrite (_:k=0) 1:/# !set_eqiE /#.
   by rewrite set_neqiE /#.
  by apply ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ R.Ops.addcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ !c{1} ==> ={c} /\ ImplZZ r{1} r{2} ).
  + by move=> /> &2 H; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (R.addcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> ?.
    by rewrite bn_carryE 1:/# b2i0 /bn_modulus /=.
qed.

equiv cminusP_spec:
 M.cminusP ~ ASpecFp.cminusP:
 ImplZZ x{1} a{2} ==> ImplZZ res{1} res{2}.
proof.
transitivity CSpecFp.cminusP
 ( ImplZZ x{1} a{2} ==> ImplZZ res{1} res{2} )
 ( ={a} /\ a{2} < modulusR ==> ={res} ).
+ move=> /> &2; exists (valR x{2}) => />. 
  smt.
+ by auto.
+ proc.
  seq 16 1: (#pre /\ cf{1}=c{2} /\ ImplZZ t{1} x{2}).
   transitivity {1}
    { (cf, t) <@ R.Ops.addcR(x, (Array4.of_list W64.zero 
                     [W64.of_int 19; W64.zero; W64.zero; W64.of_int (2^63)]), false); }
    ( ={x} ==> ={x, cf, t} )
    ( ImplZZ x{1} a{2} ==> ImplZZ x{1} a{2} /\ cf{1} = c{2} /\ ImplZZ t{1} x{2} ).
   + by move=> /> &1; exists x{1}.
   + by auto.
   + inline*; unroll for {2} 6; wp; skip => />; progress.
      do 2! congr.
      rewrite to_uint_eq to_uint_shl modz_small 1:/# !of_uintK 1..2:/#.
      by rewrite !modz_small /#.
     rewrite -ext_eq_all /all_eq /=.
     do 2! congr.
     rewrite to_uint_eq to_uint_shl modz_small 1:/# !of_uintK 1..2:/#.
     by rewrite !modz_small /#.
   + ecall {1} (R.addcR_ph x{1} (Array4.of_list W64.zero 
                     [W64.of_int 19; W64.zero; W64.zero; W64.of_int (2^63)]) false).
     inline*; wp; skip => /> &1 [c r] /=.
     pose X:= Array4.of_list _ _.
     rewrite bn_carryE 1:/# -exprM /bigint_modulus b2i0 /=.
     have ->/=: valR X = 2^255+19.
      by rewrite bn2seq /bn_seq /X of_listK.
     by move=> -> ->; rewrite bn_modulusE -exprM /=.
  inline*; wp; skip => &1 &2 [H1 [-> H2]] />.
  case: (c{2}) => H.
   pose X:= valR _.
   have ->//: X = valR t{1}.
   by rewrite /X; congr; rewrite -ext_eq_all /all_eq /=.
  pose X:= valR _.
  have ->//: X = valR x{1}.
  by rewrite /X; congr; rewrite -ext_eq_all /all_eq /=.
+ symmetry; conseq cminusP_eq; smt().
qed.

equiv addm_spec:
 M.addm ~ ASpecFp.addm:
  ImplFp a{1} a{2} /\ ImplFp b{1} b{2}
  ==> ImplFp res{1} res{2}.
proof.
transitivity Zp25519.CSpecFp.addm
 (ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplZZ res{1} res{2})
 (={a,b} ==> res{1}= asint res{2}).
+ by move=> /> &1 &2 H1 H2 /=; exists (a{2},b{2}) => /=.
+ by auto.
+ proc; simplify.
  inline M._addm.
  ecall {1} (x2r_ph f0{1} f1{1} f2{1} f3{1}); simplify.
  wp; ecall {1} (r2x_ph f{1}); simplify.
  call cminusP_spec.
  call addc_spec.
  ecall {1} (x2r_ph g00{1} g10{1} g20{1} g30{1}); simplify.
  ecall {1} (x2r_ph f00{1} f10{1} f20{1} f30{1}); simplify.
  wp; ecall {1} (r2x_ph b{1}); ecall {1} (r2x_ph a{1}); simplify.
  skip => /> &1 &2 H1 H2.
  have HH: forall (f: R),
            (Array4.of_list W64.zero [f.[0]; f.[1]; f.[2]; f.[3]])
            = f.
   by move=> f; rewrite -ext_eq_all /all_eq /=.
  rewrite (HH a{1}) (HH b{1}); move=> />; progress.
  rewrite (HH result_L0). smt().
+ symmetry; conseq addm_eq; smt().
qed.

equiv subc_spec:
 M.bn_subc ~ ASpecFp.subn:
  ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2}
  ==> res{1}.`1=res{2}.`1 /\ ImplZZ res{1}.`2 res{2}.`2.
proof.
transitivity 
 R.Ops.subcR
 ( (a,b,false){1}=(a,b,c){2} ==> ={res} )
 ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ !c{1}
   ==> res{1}.`1 = res{2}.`1 /\ ImplZZ res{1}.`2 res{2}.`2 ).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1},false).
+ by move=> /> *.
+ proc; simplify.
  unroll {2} 3; rcondt {2} 3; first by auto.
  exlim a{1}, b{1} => aa bb.
  while (={i,b} /\ 1 <= i{2} <= nlimbs /\
         (cf, aa){1}=(c, a){2} /\
         (forall k, 0 <= k < i{2} => a{1}.[k] = r{2}.[k]) /\
         (forall k, i{2} <= k < nlimbs => a{1}.[k] = aa.[k])).
   wp; skip => /> &1 &2 Hi1 _ Hh1 Hh2 Hi2.
   split => *; first smt().
   split => *; first smt().
   split.
    move=> k Hk1 Hk2.
    pose X := (subc _ _ _)%W64.
    pose Y := (subc _ _ _)%W64.
    have ->: X=Y by smt().
    case: (k = i{2}) => ?.
     by rewrite !set_eqiE /#.
    by rewrite !set_neqiE /#.
   move=> k Hk1 Hk2.
   by rewrite set_neqiE /#.
  wp; skip => />.
  split => *.
   split => k *.
    by rewrite (_:k=0) 1:/# !set_eqiE /#.
   by rewrite set_neqiE /#.
  by apply ext_eq; smt().
+ proc; simplify.
  transitivity {1}
   { (c,r) <@ R.Ops.subcR(a,b,c); }
   ( ={a,b,c} ==> ={c,r} )
   ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} /\ !c{1} ==> ={c} /\ ImplZZ r{1} r{2} ).
  + by move=> /> &2 H; exists a{2} b{2} false.
  + by auto.
  + by inline*; sim.
  + ecall {1} (R.subcR_ph a{1} b{1} c{1}); wp; skip => /> &m Hc [c r] /= -> ?.
    by rewrite bn_borrowE 1:/# b2i0 /bn_modulus /=.
qed.

equiv caddP_spec:
 M.caddP ~ ASpecFp.caddP:
 cf{1}=c{2} /\ ImplZZ x{1} a{2} ==> ImplZZ res{1} res{2}.
proof.
transitivity CSpecFp.caddP
 ( cf{1}=c{2} /\ ImplZZ x{1} a{2} ==> ImplZZ res{1} res{2} )
 ( ={c,a} ==> ={res} ).
+ by move=> /> &1 &2 ??; exists (c{2},a{2}) => /> /#.
+ by auto.
+ proc; simplify.
  call addc_spec.
  inline*; wp; skip => />; progress.
  case: (c{2}) => E /=.
   apply (eq_trans _ (valR pR)); last exact pRE.
   by congr; rewrite -ext_eq_all /all_eq.
  apply (eq_trans _ (valR zeroR)); last exact zeroRE.
  by congr; rewrite -ext_eq_all /all_eq.
+ symmetry; conseq caddP_eq; smt().
qed.

equiv subm_spec:
 M.subm ~ ASpecFp.subm:
  ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2}.
proof.
transitivity Zp25519.CSpecFp.subm
 (ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplZZ res{1} res{2})
 (={a,b} ==> res{1}= asint res{2}).
+ by move=> /> &1 &2 H1 H2 /=; exists (a{2},b{2}) => />.
+ by auto.
+ proc. 
  inline M._subm.
  ecall {1} (x2r_ph f0{1} f1{1} f2{1} f3{1}); simplify.
  wp; ecall {1} (r2x_ph f{1}); simplify.
  call caddP_spec.
  call subc_spec.
  ecall {1} (x2r_ph g00{1} g10{1} g20{1} g30{1}); simplify.
  ecall {1} (x2r_ph f00{1} f10{1} f20{1} f30{1}); simplify.
  wp; ecall {1} (r2x_ph b{1}); ecall {1} (r2x_ph a{1}); simplify.
  skip => /> &1 &2 H1 H2.
  have HH: forall (f: R),
            (Array4.of_list W64.zero [f.[0]; f.[1]; f.[2]; f.[3]]) = f.
   by move=> f; rewrite -ext_eq_all /all_eq /=.
  by rewrite (HH a{1}) (HH b{1}); move=> /> /#.
+ symmetry; conseq subm_eq; smt().
qed.

module AImpl = {
  proc maskOnCarry(m: int, r: W64.t, _cf: bool): W64.t = {
    (_cf, r) <- subc r r _cf;
    r <- r `&` W64.of_int m;
    return r;
  }
  proc reduce(a: R2): R = {
    var ah, al: W64.t Array4.t;
    var _of, _cf, tmp;
    (ah, al) <@ MulOps.unpackR2(a);
    (_of, _cf, a) <@ MulOps.mul1acc(0, W64.of_int 38, ah, a, false, false);
    (ah, al) <@ MulOps.unpackR2(a);
    tmp <- a.[nlimbs] * W64.of_int 38;
    (_cf, al) <@ Ops.add1R(al, tmp, false);
    tmp <@ M.maskOnCarry(38, tmp, _cf);
(*    al <- al.[0 <- al.[0] + tmp];*)
    al.[0] <- al.[0] + tmp;
    return al;
  }
}.

lemma maskOnCarry_h m cf:
 hoare [ M.maskOnCarry :
         _cf=cf /\ mask=m ==> res = if cf then W64.of_int m else W64.zero ].
proof.
proc; simplify.
wp; skip => /> &hr.
have ->: (subc r{hr} r{hr} cf).`2 = if cf then W64.onew else W64.zero.
 rewrite /subc /=.
 have ->: r{hr} - (r{hr} + W64.of_int (b2i cf)) = -W64.of_int (b2i cf) by ring.
 case: cf => E.
  by rewrite b2i1 minus_one.
 by rewrite b2i0; ring.
case: cf => Ecf.
 by rewrite W64.and1w.
by rewrite W64.and0w.
qed.

lemma maskOnCarry_ll: islossless M.maskOnCarry.
proof. by islossless. qed.

lemma maskOnCarry_ph m cf:
 phoare [ M.maskOnCarry :
         _cf=cf /\ mask=m ==> res = if cf then W64.of_int m else W64.zero ] = 1%r.
proof. by conseq maskOnCarry_ll (maskOnCarry_h m cf). qed.

equiv unpack2_eq:
 M.bn2_unpack ~ MulOps.unpackR2 :
 ={a} ==> ={res}.
proof.
proc.
unroll for {1} 4.
unroll for {2} 6.
unroll for {2} 4.
by wp; skip => /> *.
qed.

equiv mul1first_eq:
 M.mul1 ~ MulOps.mul1:
 a{1}=ak{2} /\ ={b}
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc; simplify.
wp.
while ( #pre /\ ={r,i} /\ (a,of_0,cf,_zero){1}=(ak,_of,_cf,W64.zero){2} /\ 
        1 <= i{2} <= nlimbs /\ !_of{2}).
 wp; skip => />; smt(Array8.get_setE Array8.set_set_if).
wp; skip => />; smt (Array8.set_set_if).
qed.

equiv mul1acc_eq :
 M.mul1acc ~ MulOps.mul1acc:
 ={k,a,b} /\ (_zero,of_0,cf,r){1}=(W64.zero,_of,_cf,x){2} /\
  0 <= k{2} < nlimbs
 ==>
 (res.`1,res.`2,res.`3,res.`4){1} = (W64.zero,res.`1,res.`2,res.`3){2}.
proof.
proc. simplify.
wp. while ( #pre /\ ={i} /\ (aux,_zero){1}=(nlimbs-1,W64.zero){2} /\ 
            0 <= i{2} <= nlimbs-1).
 wp; skip => />; smt(get_setE set_set_if).
wp; skip; smt(get_setE set_set_if).
qed.

equiv add1_eq:
 M.bn_add1 ~ Ops.add1R:
 ={a, b} /\ ! c{2} ==> ={res}.
proof.
proc; simplify.
while ( ={i} /\ 1 <= i{2} <= nlimbs /\
        (cf){1}=(c){2} /\
        bnk i{2} a{1} = bnk i{2} r{2} /\
        forall j, i{2} <= j < nlimbs
                  => a{1}.[j] = a{2}.[j] ).
 wp; skip => /> &1 &2 Hi1 Hi2 IH H Hcond.
 split; first smt().
 split; first smt().
 split.
  rewrite !bnkS 1..2:/# /= !get_setE 1..2:/# /=.
  rewrite !bnk_setO 1..2:/#; congr; smt().
 move=> j Hj1 Hj2; rewrite get_setE 1:/#.
 by rewrite (_:!j = i{2}) 1:/# /= H /#.
wp; skip => /> &2 Hcf.
split.
 split; first by rewrite !bnk1.
 move=> j Hj1 Hj2; rewrite get_setE 1:/#.
 by rewrite (_:!j=0) 1:/#.
move => rL i rR ????.
rewrite (_:i=nlimbs) 1:/# => E ?.
by apply bn_inj.
qed.

equiv reduce_eq:
 M.redp25519 ~ AImpl.reduce:
 ={a} /\ !_cf{1} /\ !_of{1} ==> ={res}.
proof.
proc; simplify; wp.
call (_: true). sim.
call add1_eq.
wp; call unpack2_eq.
wp; call mul1acc_eq.
call unpack2_eq.
wp; skip => />; progress.
by rewrite H4 /#. 
qed.

lemma reduce_spec:
 equiv [ M.redp25519 ~ ASpecFp.reduce :
         ImplZZ2 a{1} a{2} /\ !_cf{1} /\ !_of{1}
         ==> ImplZZ res{1} res{2} ].
proof.
transitivity AImpl.reduce
 (={a} /\ !_cf{1} /\ !_of{1} ==> ={res})
 (ImplZZ2 a{1} a{2} ==> ImplZZ res{1} res{2}).
 + by move=> /> &1 *; exists a{1} => /#.
 + by auto.
 + by apply reduce_eq.
 +
proc; simplify.
wp; ecall {1} (maskOnCarry_ph 38 _cf{1}).
ecall {1} (add1R_ph al{1} tmp{1} false).
wp; ecall {1} (unpackR2_ph2 a{1}).
wp; ecall {1} (mul1acc_ph 0 (W64.of_int 38) ah{1} a{1}).
wp; ecall {1} (unpackR2_ph2 a{1}).
skip => /> &1 [ah0 al0] /= Ea0h _ [_of0 _cf0 r0] ?? /=. 
rewrite expr0 /= => E1.
have X1: R2.bnk 5 r0 = red256 (R2.bn a{1}).
 rewrite E1.
 by rewrite -R2.bn_mod 1:/# Ea0h /red256 /split256 /= bn_modulusE expr0 /= expr0 /#.
move=> [ah1 al1] /= _ Ea1l [_cf1 r1] /=.
have {Ea1l}Ea1l: ImplZZ al1 (R2.bnk 5 r0 %% Zp25519.M).
 have ->: Zp25519.M = modulusR.
  by rewrite bn_modulusE /= expr0.
 by rewrite -R2.bn_mod 1:/# bn_modulusE modz_dvd_pow 1:/# -bn_modulusE.
have Ea1h: to_uint r0.[nlimbs] = R2.bnk 5 r0 %/  Zp25519.M.
 rewrite (_:5=4+1) 1:/# R2.bnkS 1:/# /= expr0 /=.
 rewrite divzDl ?bn_modulusE /=.
  by rewrite dvdz_mull dvdzz.
 rewrite mulzK 1:/# divz_small /=; last done.
 move: (R2.bnk_cmp nlimbs r0).
 by rewrite /= expr0 /#. 
rewrite !b2i0 /= to_uintM_small.
 move: (red256_once (valR2 a{1}) _).
  by move: (R2.bnk_cmp 8 a{1}); rewrite /= expr0 /#.
 by rewrite -X1 of_uintK modz_small /#.
rewrite of_uintK modz_small 1:/# => H1 H2.
have XX: (b2i _cf1, valR r1) = split256 (red256 (red256 (valR2 a{1}))).
 rewrite -X1 /red256 /split256 /= H2 -Ea1l -Ea1h.
 split.
  case: (_cf1) => Ecf.
   have ->: valR al1 + 38 * to_uint r0.[nlimbs]
           = Zp25519.M + (valR al1 + 38 * to_uint r0.[nlimbs] - Zp25519.M) by ring.
   rewrite divzDl 1:dvdzz divzz /=. 
   rewrite divz_small; last done.
   apply bound_abs; split.
    by move: H1; rewrite Ecf eq_sym eqT bn_modulusE /= expr0 /#.
   move=> *.
    smt.
   rewrite divz_small; last done.
   move: H1; rewrite Ecf bn_modulusE /= expr0 /= eq_sym neqF => H1.
   split; smt.
 by rewrite bn_modulusE /= expr0 /= mulrC.
move: (red256_twiceP (valR2 a{1}) (b2i _cf1) (valR r1) _ XX).
 by move: (R2.bnk_cmp 8 a{1}); rewrite /= expr0 /#.
case: (_cf1) => Ecf.
 rewrite /reduce {1}/red256 -XX /= Ecf !b2i1 /=.
 move=> Hr1.
 have Xr: forall r, valR r < W64.modulus => r = Array4.of_list W64.zero [r.[0]; W64.zero; W64.zero; W64.zero].
  move=> r Hr; apply bn_inj.
  by move: Hr; rewrite !bn2seq /bn_seq /to_list /mkseq -iotaredE /=; smt(W64.to_uint_cmp).
 rewrite (Xr _) 1:/# !bn2seq /bn_seq /to_list /mkseq -iotaredE /=.
 rewrite to_uintD_small.
  have <-: valR r1 = to_uint r1.[0].
   by rewrite Xr 1:/# !bn2seq /bn_seq /to_list /mkseq -iotaredE.
  smt().
 by rewrite of_uintK.
rewrite !b2i0 /= /reduce.
have ->: r1.[0 <- r1.[0]] = r1.
 by apply ext_eq; smt(get_setE).
by rewrite {1}/red256 -XX /= Ecf b2i0.
qed.

equiv muln_spec:
 M.bn_muln ~ ASpecFp.muln:
  ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2}
  ==> ImplZZ2 res{1}.`4 res{2}
      /\ res{1}.`1 = W64.zero /\ !res{1}.`2 /\ !res{1}.`3.
proof.
transitivity 
 MulOps.mulR
 ( ={a,b} ==> res{1}.`2=res{2}.`1 /\ res{1}.`3=res{2}.`2 /\ res{1}.`4=res{2}.`3 /\  res{1}.`1 = W64.zero )
 ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} 
   ==> !res{1}.`1 /\ !res{1}.`2 /\ ImplZZ2 res{1}.`3 res{2}).
+ by move=> /> &1 &2 H1 H2; exists (a{1},b{1}).
+ by move=> /> /#.
+ proc; simplify.
  while ( #pre /\ (i,_zero,of_0,cf,r){1}=(k,W64.zero,_of,_cf,r){2} /\
          1 <= k{2} <= nlimbs ).
   by wp; call mul1acc_eq; wp; skip => /> /#.
  by wp; call mul1first_eq; wp; skip => /> /#.
+ proc.
  transitivity {1}
    { (_of,_cf,r) <@ MulOps.mulR(a,b); }
    ( ={a,b} ==> ={_cf,_of,r} )
    ( ImplZZ a{1} a{2} /\ ImplZZ b{1} b{2} ==> !_cf{1} /\ !_of{1} /\ ImplZZ2 r{1} r{2} ).
  + by move=> /> &1; exists a{1} b{1}; auto.
  + by move=> /> *.
  + by inline MulOps.mulR; sim.
  + by ecall {1} (mulR_ph a{1} b{1}); wp; skip.
qed.

equiv mulm_spec:
 M.mulm ~ ASpecFp.mulm:
  ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2}.
proof.
transitivity Zp25519.CSpecFp.mulm
 (ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplZZ res{1} res{2})
 (={a,b} ==> res{1}= asint res{2}).
+ by move=> /> &1 &2 H1 H2 /=; exists (a{2},b{2}) => />.
+ by auto.
+ proc. inline M._mulm M.freeze CSpecFp.freeze.
  wp; ecall {1} (x2r_ph g0{1} g1{1} g2{1} g3{1}); simplify.
  wp; ecall {1} (r2x_ph g{1}); simplify.
  wp; call cminusP_spec; call cminusP_spec.
  wp; call reduce_spec.
  call muln_spec.
  ecall {1} (x2r_ph g00{1} g10{1} g20{1} g30{1}); simplify.
  wp; ecall {1} (r2x_ph b{1}); simplify.
  skip => /> &1 &2 H1 H2.
  have HH: forall (f: R.t),
            (Array4.of_list W64.zero [f.[0]; f.[1]; f.[2]; f.[3]]) = f.
   by move=> f; rewrite -ext_eq_all /all_eq /=.
  rewrite (HH b{1}); split; first smt().
  by move=> _ r Hr1 Hr2 Hr3 rr => /> /#.
+ symmetry; conseq mulm_eq; smt().
qed.
