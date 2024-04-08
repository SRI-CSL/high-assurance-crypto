require import DBool.

from SigmaProtocol require import ASigmaProtocol.

theory Completeness.

  clone import SigmaProtocol.

  module type Rand_t = {
    proc gen() : prover_rand_t * verifier_rand_t
  }.

  module Completeness(R : Rand_t) = {
    proc main(w : witness_t, x : statement_t) : bool = {
      var r_p, r_v;
      var tr, y, b, otry;

      (r_p, r_v) <@ R.gen();

      if (valid_inputs ((w,x),x) /\ valid_rands (r_p, r_v) ((w,x),x)) {
        otry <- protocol (r_p, r_v) ((w,x), x);
        if (otry <> None) {
          (tr,y) <- oget otry;
          b <- (snd y);
        }
        else { b <- true; }
      }
      else { b <- true; (*{0,1};*) }

      return b;
    }
  }.

end Completeness.
