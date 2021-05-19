require import DBool List.

from General require import Utils ListExt.
from MPC require import AGate.
from Functionalities require import AGateFunctionality.

theory Privacy.

  clone import Gate.
  import GateFunctionality.

  type aux_t.
  type env_input_t.
  
  module type Rand_t = {
    proc gen(aux : aux_t, cr : pid_t list) : rands_t
  }.

  module type Distinguisher_t = {
    proc choose(x : env_input_t, aux : aux_t) : inputs_t * pid_t list
    proc guess(vsc : views_t) : bool
  }.

  module type Evaluator_t = {
    proc eval(xs : inputs_t, cr : pid_t list, rs : rands_t) : views_t
  }.

  op valid_corrupted_set (cr : pid_t list) : bool = 
    size cr = t /\ (forall pid, pid \in cr => pid \in pid_set).

  module Game(D : Distinguisher_t, R : Rand_t, E : Evaluator_t) = {
    proc main(x : env_input_t, aux : aux_t) : bool = {
      var r, b', vsc, xs, cr;

      (xs,cr) <@ D.choose(x,aux);
      r <@ R.gen(aux,cr);
      if (valid_rands r /\ valid_inputs xs /\ valid_corrupted_set cr) {
        vsc <@ E.eval(xs, cr, r);
        b' <@ D.guess(vsc);
      } else { b' <${0,1}; } 
      return b';
    }
  }.

  module RealEvaluator = {
    proc eval(xs : inputs_t, cr : pid_t list, rs : rands_t) : views_t = {
      var tr, y, vsc;

      (tr, y) <- gate rs xs;
      vsc <- map (fun pid => (pid, (input pid xs, rand pid rs, trace pid tr))) cr;

      return vsc;
    }
  }.

  op simulator : rands_t -> inputs_t -> pid_t list -> outputs_t -> views_t.

  module IdealEvaluator (*(S : Simulator_t)*) = {
    proc eval(xs : inputs_t, cr : pid_t list, rs : rands_t) : views_t = {
      var xsc, vsc, ys, ysc;

      ys <- GateFunctionality.f xs;
      xsc <- map (fun pid => (pid, input pid xs)) cr;
      ysc <- map (fun pid => (pid, output pid ys)) cr;
      vsc <- simulator rs xsc cr ysc;

      return vsc;
    }
  }.

  module GameReal (D : Distinguisher_t) (R : Rand_t) = Game(D,R,RealEvaluator).
  module GameIdeal (D : Distinguisher_t) (R : Rand_t) (*(S : Simulator_t)*) = Game(D,R,IdealEvaluator(*(S)*)).

end Privacy.
