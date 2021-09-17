require import AllCore IntDiv.
from Jasmin require import JModel.

require import Fp_bool.

require import ZModP.

lemma prime_2: prime 2.
proof.
rewrite /prime; split; first done.
move=> q H.
move: (dvdz_le _ _ _ H) => // Hq.
smt.
qed.

clone import ZModP.ZModField as Zp with
        op p <= 2
        rename "zmod" as "zp"
        proof prime_p by exact prime_2.

import Zp.

module ASpecFp = {
  (********************)
  (* Finite Field Ops *)
  (********************)
  proc addm(a b: zp): zp = {
    var r;
    r <- a + b;
    return r;
  }
  proc subm(a b: zp): zp = {
    var r;
    r <- a - b;
    return r;
  }
  proc mulm(a b: zp): zp = {
    var r;
    r <- a * b;
    return r;
  }
}.


import W64.

abbrev ImplWord x y = W64.to_uint x = y.
abbrev ImplFp a b = ImplWord a (asint b).

lemma asintBool a b:
 (a = asint b) => (a=0 /\ b=inzp 0 \/ a=1 /\ b=inzp 1).
proof.
move: (rg_asint b).
pose B := asint b.
move=> Hb.
have [Eb|Eb] : B = 0 \/ B = 1 by smt().
 by move=> ->; left => //; smt(asintK).
by move=> ->; right => //; smt(asintK).
qed.

lemma implFpE a b:
 ImplFp a b = ((a=W64.zero /\ b = inzp 0) \/ (a=W64.one /\ b = inzp 1)).
proof.
rewrite eqboolP; split.
 move=> /asintBool [[Ea Eb]|[Ea Eb]].
  left => />; smt.
 right => />; smt.
move=> [[-> ->]|[-> ->]]; smt.
qed.

equiv addm_spec:
 M.addm ~ ASpecFp.addm:
  ImplFp a{1} a{2} /\ ImplFp b{1} b{2}
  ==> ImplFp res{1} res{2}.
proof.
proc; simplify; wp; skip => &1 &2 />.
rewrite !implFpE => [[[-> ->]|[-> ->]] [[-> ->]|[-> ->]]].
+ by left; split; smt().
+ right; split; smt.
+ right; split; smt.
+ by left; split; smt().
qed.

equiv subm_spec:
 M.subm ~ ASpecFp.subm:
  ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2}.
proof.
proc; simplify; wp; skip => &1 &2 />.
rewrite !implFpE => [[[-> ->]|[-> ->]] [[-> ->]|[-> ->]]].
+ left; split; smt.
+ right; split; smt.
+ right; split; smt.
+ left; split; smt.
qed.

equiv mulm_spec:
 M.mulm ~ ASpecFp.mulm:
  ImplFp a{1} a{2} /\ ImplFp b{1} b{2} ==> ImplFp res{1} res{2}.
proof.
proc; simplify; wp; skip => &1 &2.
rewrite !implFpE => [[[[-> ->]|[-> ->]] [[-> ->]|[-> ->]]]].
+ left; split; smt.
+ left; split; smt.
+ left; split; smt.
+ right; split; smt.
qed.

