(*  
    Formalization of a lazily sampled random function 
    as an EasyCrypt module that can be used in arbitrary
    games.

    It is an abstract theory, which means that FIX ME

    The types of inputs and outputs can be defined to
    be arbitrary types when the theory is cloned.

    Any clone will include the axioms that allow seeing
    the output as a finite type from which you can
    sample uniformly at random (MFinite).
*)

require import AllCore Distr  SmtMap.

abstract theory RF.
  
  type input.
  type output.

  op doutput : output distr.

  axiom doutput_uni : is_uniform doutput.
  axiom doutput_ll  : is_lossless doutput.

  module type OrclRF = {
    proc get(i:input) : output
  }.

  module type RFi = {
    proc init() : unit
    include OrclRF
  }.

  module RF : RFi = {
    var m : (input, output) fmap

    proc init() = { 
      m <- empty;
    } 

    proc get(i:input) = {
      var r;
      r <$ doutput;
      if (i \notin m) m.[i] <- r;
      return oget m.[i];
    }
  }.

end RF.
