require import Distr Real.

from SigmaProtocol require import ASigmaProtocol.

theory SoundnessSigmaProtocol.

  clone import SigmaProtocol.
  import ZKPProtocol.
  import ZKFunctionality.

  module type MProver_t = {
    proc commitment(x : statement_t) : commitment_t
    proc response(x : statement_t, ch : challenge_t) : response_t
  }.

  module type RandV_t = {
    proc gen(lv : verifier_leakage_t) : verifier_rand_t
  }.
  
  module Soundness(RV : RandV_t, MP : MProver_t) = {
    proc main(x : statement_t) : bool = {
      var r_v, b, c, ch, resp, stv;

      r_v <@ RV.gen(SigmaProtocol.verifier_phi x);

      c <@ MP.commitment(x);

      if (ZKPProtocol.valid_rand_verifier r_v x) {
        (stv,ch) <- challenge r_v x c;
        resp <- MP.response(x, ch);
        b <- !ZKFunctionality.language x /\ check stv resp;
      } else { b <- false; }

      return b;
    }
  }.
end SoundnessSigmaProtocol.
