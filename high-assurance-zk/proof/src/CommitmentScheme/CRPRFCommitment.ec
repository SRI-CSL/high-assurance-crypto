require import AllCore DBool.

from Assumptions require import CRPRF.
from CommitmentScheme require import ACommitmentScheme Hiding Binding.

theory CRPRFCommitment.

clone include CRPRF.

op commit(k,m) = (f k m,k).
op verify(m : input, ci : output * key) = ci.`1 = f ci.`2 m.

clone import CommitmentScheme as CS with
  type msg_t = input,
  type rand_t = key,
  op valid_rand =  fun _ => true,
  type opening_string_t = key,
  type commitment_t = output,
  op commit = commit,
  op verify = verify
  proof correct by rewrite /commit /verify.

(*clone import Hiding with
   theory CommitmentScheme <- CS,
  type state_t = unit.

import Hiding.

module Rand : Rand_t = {
   proc gen() : rand_t = {
      var k;
      k <$ dkey;
      return k;
   }
}.

section.

declare module A :Adversary_t {RealPRF, RF}.
axiom  Achoose_ll : islossless A.choose.
axiom  Aguess_ll : islossless A.guess.

local module GameRand = {
  proc main() : bool = {
    var b : bool;
    var b' : bool;
    var r : rand_t;
    var c : commitment_t;
    var ok : opening_string_t;
    var m0 : msg_t;
    var m1 : msg_t;
    var st;
        
    b <$ {0,1};
    oquery <@ A.choose();
    if (oquery <> None) {
      (m0,m1,st) <- oget oquery;
      r <@ Rand.gen();
      c <$ doutput;
      ob' <@ A.guess(c);
      if (ob' <> None) { r <- oget ob'; }
      else { b' <${0,1}; }
    } else { b <${0,1}; }

    r <@ Rand.gen();
    b <$ {0,1};
    (m0, m1, st) <@ A.choose();
    c <$ doutput;
    b' <@ A.guess(c);
    
    return b = b';

  }
}.

module B(A : Adversary_t, O : OrclPRF)  = {
   proc main() : bool = {
    var b : bool;
    var b' : bool;
    var r : rand_t;
    var c : commitment_t;
    var ok : opening_string_t;
    var m0 : msg_t;
    var m1 : msg_t;
    
    b <$ {0,1};
    (m0, m1) <@ A.choose();
    c <@ O.f(if b then m1 else m0);
    b' <@ A.guess(c);
    
    return b = b';
   }
}.

equiv hop_left:
 Game(Rand,A).main ~ PRF(B(A),RealPRF).main :
     ={glob A} ==> ={res}.
proc; inline *. 
swap {2} 1 1.
by wp;call(_: true);wp;call(_:true);wp;rnd;rnd => />.
qed.

local equiv hop_right:
 PRF(B(A),IdealPRF).main ~ GameRand.main :
     ={glob A} ==> ={res}.
proc; inline *. 
seq 0 2  : #pre; first by wp;rnd{2};auto => />; smt(dkey_ll).
wp;call(_: true);wp;rnd;wp;call(_:true);wp;rnd => />.
by auto => />; smt(SmtMap.get_setE).
by auto => /> *; rewrite !SmtMap.get_setE SmtMap.emptyE SmtMap.mem_empty => />. 
qed.

local lemma bound &m : 
  Pr[GameRand.main() @ &m : res] = 1%r/2%r.
byphoare => //.
proc; inline *.
swap 3 3; seq 5 : true 1%r (1%r/2%r)   _ 0%r true => //. 
call(_:true); first by apply Aguess_ll.
rnd (fun _=> true);call(_:true); first by apply Achoose_ll. 
wp;rnd (fun _=> true) => />. 
auto => />; do split. 
by smt(dkey_ll). 
by smt(doutput_ll). 
by rnd (fun x => x = b'); skip => /> *; rewrite dbool1E => /#. 
qed.

lemma hiding &m :
  Pr [ Game(Rand,A).main() @ &m : res ] = 
     Pr [ PRF(B(A),RealPRF).main() @ &m : res ]
       - Pr [ PRF(B(A),IdealPRF).main() @ &m : res ] + 1%r/2%r.
rewrite (_: 
  Pr [ Game(Rand,A).main() @ &m : res ] = 
   Pr [ PRF(B(A),RealPRF).main() @ &m : res ]); first 
  by byequiv hop_left => //.
rewrite (_: 
  Pr [ PRF(B(A), IdealPRF).main() @ &m : res ] = 
   Pr [ GameRand.main() @ &m : res ]); first 
  by byequiv hop_right => //.
by rewrite bound; ring.
qed.

end section.

clone import CommitmentBinding.Binding as Binding with
   theory CommitmentScheme <- CS.

section.

declare module A :Adversary_t.
axiom  Achoose_ll : islossless A.choose.

module C(A : Adversary_t)  = {
   proc find() : (key *  input) * (key * input) = {
    var k0, i0,k1, i1, c;
    (c, i0, k0, i1, k1) <@ A.choose();
    return ((k0,i0),(k1,i1));
   }
}.

lemma binding &m : 
  Pr[ Game(A).main() @ &m : res ] <= Pr[ CR(C(A)).main() @ &m : res].
proof. 
byequiv => //.
proc; inline *.
wp; call(_: true) => />  *; first by smt().
by skip => /> *; rewrite /verify //= => /#.
qed.

end section.*)

end CRPRFCommitment.
