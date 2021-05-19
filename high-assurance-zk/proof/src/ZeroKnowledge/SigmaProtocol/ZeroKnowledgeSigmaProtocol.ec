require import DBool.

from SigmaProtocol require import ASigmaProtocol.

theory ZeroKnowledgeSigmaProtocol.

  clone import SigmaProtocol.
  import ZKPProtocol.
  import ZKFunctionality.

  module type RandP_t = {
    proc gen(_ : prover_input_t) : prover_rand_t
  }.

  module type Distinguisher_t = {
    proc guess(_ : witness_t * statement_t * bool * trace_t) : bool
  }.

  module type Evaluator_t = {
    proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : (bool * trace_t) option
  }.

  module ZKGame (D : Distinguisher_t) (RP : RandP_t) (E : Evaluator_t) = {
    proc main(w : witness_t, x : statement_t) : bool = {
      var r, rp, b', acceptance, tr;

      rp <@ RP.gen(w,x);
      if (ZKPProtocol.valid_rand_prover rp (w,x)) {
        r <@ E.eval(w,x,rp);
        (acceptance, tr) <- oget r;
        b' <@ D.guess(w,x,acceptance,tr);
      } else { b' <${0,1}; } 
      return b';
    }
  }.

  module type MVerifier_t = {
    proc challenge(x : statement_t, c : commitment_t) : challenge_t
  }.

  module RealEvaluator (MV : MVerifier_t) = {
    proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : (bool * trace_t) option = {
      var c, ch, resp, acceptance, stp;

      (stp,c) <- commitment rp (w,x);
      ch <@ MV.challenge(x, c);
      resp <- response stp ch;
      acceptance <- ZKPProtocol.accepting_conversation x (c,ch,resp);

      return Some (acceptance, (c,ch,resp));
    }
  }.

  module type Simulator_t = {
    proc gen_commitment(rp : prover_rand_t, x : statement_t) : commitment_t option
    proc gen_response(x : statement_t, ch : challenge_t) : response_t option
  }.

  module IdealEvaluator (MV : MVerifier_t) (S : Simulator_t) = {
    proc eval(w : witness_t, x : statement_t, rp : prover_rand_t) : (bool * trace_t) option = {
      var c, ch, oresp, resp, acceptance, ret, oc;

      ret <- None;
      oc <@ S.gen_commitment(rp, x);
      if (oc <> None) {
        c <- oget oc;
        ch <@ MV.challenge(x, c);
        oresp <@ S.gen_response(x, ch);
        if (oresp <> None) {
          resp <- oget oresp;
          acceptance <- ZKPProtocol.accepting_conversation x (c,ch,resp);
          ret <- Some (acceptance, (oget oc,ch, oget oresp));
        }
      }

      return ret;
    }
  }.

  module GameReal (D : Distinguisher_t) (RP : RandP_t) (MV : MVerifier_t) = ZKGame(D,RP,RealEvaluator(MV)).
  module GameIdeal (D : Distinguisher_t) (RP : RandP_t) (MV : MVerifier_t) (S : Simulator_t) = ZKGame(D,RP,IdealEvaluator(MV,S)).

end ZeroKnowledgeSigmaProtocol.
