require import DBool List.

from General require import Utils ListExt.
from MPC require import AProtocol.
from Functionalities require import AProtocolFunctionality.

theory Privacy.

  clone import Protocol.
  import ProtocolFunctionality.
  import Circuit.

  type aux_t.
  type env_input_t.
  
  module type Rand_t = {
    proc gen(c : circuit_t, cr : pid_t list, aux : aux_t) : rands_t
  }.

  module type Distinguisher_t = {
    proc choose(c : circuit_t, x : env_input_t, aux : aux_t) : inputs_t * pid_t list
    proc guess(vsc : views_t) : bool
  }.

  module type Evaluator_t = {
    proc eval(c : circuit_t, xs : inputs_t, cr : pid_t list, rs : rands_t) : views_t
  }.

  op valid_corrupted_set (cr : pid_t list) : bool = 
    size cr = t /\ (forall pid, pid \in cr => pid \in pid_set).

  module Game(D : Distinguisher_t, R : Rand_t, E : Evaluator_t) = {
    proc main(c : circuit_t, x : env_input_t, aux : aux_t) : bool = {
      var r, b', vsc, xs, cr;

      (xs,cr) <@ D.choose(c,x,aux);
      r <@ R.gen(c,cr,aux);
      if (valid_inputs c xs /\ valid_rands c r /\ valid_corrupted_set cr) {
        vsc <@ E.eval(c, xs, cr, r);
        b' <@ D.guess(vsc);
      } else { b' <${0,1}; } 
      return b';
    }
  }.

  module RealEvaluator = {
    proc eval(c : circuit_t, xs : inputs_t, cr : pid_t list, rs : rands_t) : views_t = {
      var tr, y, vsc;

      (tr, y) <- protocol c rs xs;
      vsc <- map (fun pid => (pid, (input pid xs, rand pid rs, trace pid tr))) cr;

      return vsc;
    }
  }.

  module type Simulator_t = {
    proc simm(c : circuit_t, xs : inputs_t, rs : rands_t, cr : pid_t list, y : ProtocolFunctionality.outputs_t) : views_t
  }.

  module IdealEvaluator (S : Simulator_t) = {
    proc eval(c : circuit_t, xs : inputs_t, cr : pid_t list, rs : rands_t) : views_t = {
      var xsc, vsc, ys;

      xsc <- extract_inputs xs cr;
      ys <- f c xs;
      ys <- map (fun pid => (pid, oget (assoc ys pid))) cr;
      vsc <- S.simm(c, xsc, rs, cr, ys);

      return vsc;
    }
  }.

  module GameReal (D : Distinguisher_t) (R : Rand_t) = Game(D,R,RealEvaluator).
  module GameIdeal (D : Distinguisher_t) (R : Rand_t) (S : Simulator_t) = Game(D,R,IdealEvaluator(S)).

end Privacy.
