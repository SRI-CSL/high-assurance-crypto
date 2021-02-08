require import DBool List.

from General require import Utils ListExt.
from MPC require import AGate.
from Functionalities require import AGateFunctionality.

theory Privacy.

  clone import Gate.
  import GateFunctionality.
  
  module type Rand_t = {
    proc gen(xs : inputs_t, cr : pid_t list) : rands_t
  }.

  module type Distinguisher_t = {
    proc guess(vsc : view_t list) : bool
  }.

  module type Evaluator_t = {
    proc eval(xs : inputs_t, cr : pid_t list, rs : rands_t) : view_t list
  }.

  module PrivGame(D : Distinguisher_t, R : Rand_t, E : Evaluator_t) = {
    proc main(xs : inputs_t, cr : pid_t list) : bool = {
      var r, b', vsc;

      r <@ R.gen(xs,cr);
      if (valid_rands r) {
        vsc <@ E.eval(xs, cr, r);
        b' <@ D.guess(vsc);
      } else { b' <${0,1}; } 
      return b';
    }
  }.

  module RealEvaluator = {
    proc eval(xs : inputs_t, cr : pid_t list, rs : rands_t) : view_t list = {
      var tr, y, xsc, rsc, trsc, vsc;

      (tr, y) <- gate rs xs;
      xsc <- extract_inputs xs cr;
      rsc <- extract_rands rs cr;
      trsc <- extract_traces tr cr;
      vsc <- zip3 xsc rsc trsc;

      return vsc;
    }
  }.

  op simulator : rands_t -> inputs_t -> pid_t list -> view_t list.

  module IdealEvaluator (*(S : Simulator_t)*) = {
    proc eval(xs : inputs_t, cr : pid_t list, rs : rands_t) : view_t list = {
      var xsc, vsc;

      xsc <- extract_inputs xs cr;
      (*vsc <@ S.simm(xs, cr);*)
      vsc <- simulator rs xs cr;

      return vsc;
    }
  }.

  module GameReal (D : Distinguisher_t) (R : Rand_t) = PrivGame(D,R,RealEvaluator).
  module GameIdeal (D : Distinguisher_t) (R : Rand_t) (*(S : Simulator_t)*) = PrivGame(D,R,IdealEvaluator(*(S)*)).

end Privacy.
