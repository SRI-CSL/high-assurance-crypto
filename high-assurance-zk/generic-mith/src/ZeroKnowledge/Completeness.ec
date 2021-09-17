require import DBool.

from ZeroKnowledge require import AZKPProtocol.

theory Completeness.

  clone import ZKPProtocol.

  module type Rand_t = {
    proc gen() : prover_rand_t * verifier_rand_t
  }.

  module Completeness(R : Rand_t) = {
    proc main(w : witness_t, x : statement_t) : bool = {
      var r_p, r_v;
      var tr, y, b;

      (r_p, r_v) <@ R.gen();

      if (valid_inputs ((w,x),x) /\ valid_rands (r_p, r_v) ((w,x),x)) {
        (tr,y) <- protocol (r_p, r_v) ((w,x), x);
        b <- (snd y);
      }
      else { b <- true; (*{0,1};*) }

      return b;
    }
  }.

end Completeness.
