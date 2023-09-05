require import Distr Real.

from ZeroKnowledge require import AZKPProtocol.

theory Soundness.

  clone import ZKPProtocol.

  module type MProver_t = {
    proc commitment(x : statement_t) : commitment_t
    proc response(x : statement_t, ch : challenge_t) : response_t
  }.

  module type RandV_t = {
    proc gen() : verifier_rand_t
  }.
  
  module Soundness(RV : RandV_t, MP : MProver_t) = {
    proc main(x : statement_t) : bool = {
      var r_v, b, c, ch, resp, stv;

      r_v <@ RV.gen();

      c <@ MP.commitment(x);

      if (valid_rand_verifier r_v x) {
        (stv,ch) <- challenge r_v x c;
        resp <- MP.response(x, ch);
        b <- !language x /\ check stv resp;
      } else { b <- false; }

      return b;
    }
  }.
  
end Soundness.
