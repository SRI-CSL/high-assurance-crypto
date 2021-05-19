(*  
    Formalization of Collision Resistant Pseudorandom Function.

    Syntax and security.
*)

require import Distr.
from Assumptions require import RF.

abstract theory CRPRF.

  (* Create local copy of the RF definitions *)
  clone include RF.

  (* Syntax of the PRF *)
  type key.
  op dkey : key distr.
  axiom dkey_ll : is_lossless dkey.
  axiom dkey_uni : is_uniform dkey.

  op f : key -> input -> output.


  (* Definition of the PRF security game  *)

  (* Adversarial oracle interface *)
  module type OrclPRF = {
    proc f (i:input) : output
  }.

  (* Extended adversarial oracle interface that can 
     be initialized  by main. *)
  module type PRFi= {
    proc init() : unit
    include OrclPRF
  }.

  (* The type of adversaries *)
  module type AdvPRF (O:OrclPRF) = {
    proc main() : bool
  }.

  (* Real-world oracle: PRF is used on random key *)
  module RealPRF : PRFi = {
    var k : key

    proc init () = {
      k <$ dkey;
    }

    proc f(i:input) : output = {
      return f k i;
    } 
  }.

  (* Ideal-world oracle:  RF is used *)
  module IdealPRF = {
    proc init = RF.init
    
    proc f(i:input) : output = {
      var r;
      r <@ RF.get(i);
      return r;
    } 
  }.

  (* The game: parametric on oracle and adversary *)
  module PRF(A:AdvPRF, O:PRFi) = {
    proc main() = {
      var b;
      O.init();

      b <@ A(O).main();
      return b;
    }
  }.

  (* Collision Resistance Adversary *)  
  module type AdvCR = {
    proc find() : (key * input) * (key * input)
  }.

  (* The game: parametric on adversary *)
  module CR(A:AdvCR) = {
    proc main() = {
      var ki0,ki1;
      (ki0,ki1) <@ A.find();
      return (f ki0.`1 ki0.`2 = f ki1.`1 ki1.`2) /\ (ki0.`2 <> ki1.`2);
    }
  }.

end CRPRF.
