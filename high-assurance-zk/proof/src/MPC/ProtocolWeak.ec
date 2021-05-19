require import DBool List.

from General require import Utils ListExt.
from MPC require import AProtocol.
from Functionalities require import AProtocolFunctionality.

theory WeakSecurity.

  clone import Protocol.
  import ProtocolFunctionality.
  import Circuit.

  type aux_t.
  type env_input_t.
  type weak_view_t = input_t * rand_t * in_messages_t.  
  type weak_views_t = (pid_t * weak_view_t) list.  

  module type Rand_t = {
    proc gen(c : circuit_t, cr : pid_t list, aux : aux_t) : rands_t
  }.

  module type Distinguisher_t = {
    proc choose(c : circuit_t, x : env_input_t, aux : aux_t) : inputs_t * pid_t list
    proc guess(ys : poutputs_t, vsc : weak_views_t) : bool
  }.

  module type Evaluator_t = {
    proc eval(c : circuit_t, xs : inputs_t, cr : pid_t list, rs : rands_t) : poutputs_t * weak_views_t
  }.

  op valid_corrupted_set (cr : pid_t list) : bool = 
    size cr = t /\ (forall pid, pid \in cr => pid \in pid_set).

  module Game(D : Distinguisher_t, R : Rand_t, E : Evaluator_t) = {
    proc main(c : circuit_t, x : env_input_t, aux : aux_t) : bool = {
      var r, b', vsc, xs, cr, ysc;

      (xs,cr) <@ D.choose(c,x,aux);
      r <@ R.gen(c,cr,aux);
      if (valid_inputs c xs /\ valid_rands c r /\ valid_corrupted_set cr) {
        (ysc,vsc) <@ E.eval(c, xs, cr, r);
        b' <@ D.guess(ysc,vsc);
      } else { b' <${0,1}; } 
      return b';
    }
  }.

  module RealEvaluator = {
    proc eval(c : circuit_t, xs : inputs_t, cr : pid_t list, rs : rands_t) : poutputs_t * weak_views_t = {
      var tr, y, vsc, yc;

      (tr, y) <- protocol c rs xs;
      vsc <- map (fun pid => (pid, (input pid xs, rand pid rs, (trace pid tr).`2))) cr;
      yc <- map (fun pid => (pid, oget (assoc (trace pid tr).`1 pid))) cr;

      return (yc,vsc);
    }
  }.

  op simulator : circuit_t -> inputs_t -> rands_t -> pid_t list -> poutputs_t * weak_views_t.

  module IdealEvaluator = {
    proc eval(c : circuit_t, xs : inputs_t, cr : pid_t list, rs : rands_t) : poutputs_t * weak_views_t = {
      var xsc, vsc, y;

      y <- f c xs;
      xsc <- extract_inputs xs cr;
      vsc <- simulator c xsc rs cr;

      return (vsc);
    }
  }.

  module GameReal (D : Distinguisher_t) (R : Rand_t) = Game(D,R,RealEvaluator).
  module GameIdeal (D : Distinguisher_t) (R : Rand_t) = Game(D,R,IdealEvaluator).

end WeakSecurity.
