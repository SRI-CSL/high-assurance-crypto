require import AllCore DBool.

from Assumptions require import CRPRF.
from Commitment require import ACommitmentScheme Hiding Binding.

theory CRPRFCommitment.

  clone include CRPRF.

  op commit(k,m) = (f k m,k).
  op verify(m : input, ci : output * key) = ci.`1 = f ci.`2 m.

  clone import CommitmentScheme as CS with
    type msg_t = input,
    type rand_t = key,
    op valid_rand =  fun _ => true,
    type opening_t = key,
    type commitment_t = output,
    op commit = commit,
    op verify = verify
    proof correct by rewrite /commit /verify.

  clone import Hiding with
    theory CommitmentScheme <- CS,
    type aux_t = unit,
    op valid_query q = true.

  import Hiding.

  module Rand : Rand_t = {
    proc gen(aux : aux_t) : rand_t = {
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
        var ok : opening_t;
        var m0 : msg_t;
        var m1 : msg_t;
        var aux;

        r <@ Rand.gen();
        (m0, m1, aux) <@ A.choose();
        if (valid_query (m0,m1,aux) /\ valid_rand r) {
          c <$ doutput;
          b' <@ A.guess(c);
        } else { b' <$ {0,1}; }

        b <$ {0,1};

        return b = b';

      }
    }.

    module B(A : Adversary_t, O : OrclPRF)  = {
       proc main() : bool = {
        var b : bool;
        var b' : bool;
        var r : rand_t;
        var c : commitment_t;
        var ok : opening_t;
        var m0 : msg_t;
        var m1 : msg_t;
        var aux;

        b <$ {0,1};
        (m0, m1, aux) <@ A.choose();
        c <@ O.f(if b then m1 else m0);
        b' <@ A.guess(c);

        return b = b';
       }
    }.

    equiv hop_left:
     Game(Rand,A).main ~ PRF(B(A),RealPRF).main :
         ={glob A} ==> ={res}.
    proof.
      proc; inline *. 
      swap {2} 1 1; wp.
      rcondt{1} 8.
        by move => &m;
          wp; rnd; wp; call (_ : true); wp; rnd; skip.
      call (_ : true); wp. 
      by swap{2} 3-1; rnd; wp; call (_ : true); wp; rnd.
    qed.

    local equiv hop_right:
     PRF(B(A),IdealPRF).main ~ GameRand.main :
         ={glob A} ==> ={res}.
    proof.
      proc; inline *. 
      rcondt{2} 5.
        by move => &m; wp; call (_ : true); wp; rnd; wp.
      swap{2} 7-6; wp; call (_ : true); wp; rnd; wp; call (_ : true); wp.
      swap{2} 3-2; wp; rnd; wp; rnd{2}.
      skip; progress.
        by smt(dkey_ll).
        by smt(SmtMap.get_setE).
        by smt(@SmtMap).
    qed.

    local lemma bound &m : 
      Pr[GameRand.main() @ &m : res] = 1%r/2%r.
    proof.
      byphoare => //.
      proc; inline *.
      rcondt 5; first by call (_ : true); wp; rnd; wp.
      swap 3 3; seq 5 : true 1%r (1%r/2%r)   _ 0%r true => //. 
        call(_:true); first by apply Aguess_ll.
        rnd (fun _=> true);call(_:true); first by apply Achoose_ll. 
        wp;rnd (fun _=> true) => />. 
        auto => />; do split; first 2 by smt.
      by rnd (fun x => x = b'); wp; skip => /> *; rewrite dbool1E => /#. 
    qed.

    lemma hiding &m :
      Pr [ Game(Rand,A).main() @ &m : res ] = 
         Pr [ PRF(B(A),RealPRF).main() @ &m : res ]
           - Pr [ PRF(B(A),IdealPRF).main() @ &m : res ] + 1%r/2%r.
    proof.
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

  clone import Binding as Binding with
    theory CommitmentScheme <- CS,
    type aux_t = unit.

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
      by wp; skip => /> *; rewrite /verify //= => /#.
    qed.

  end section.

end CRPRFCommitment.
