from General require import Utils.

from Functionalities require import AFunctionality.

theory TwoPartyProtocol.

  type pid_t.

  type input1_t.
  type input2_t.
  type inputs_t = input1_t * input2_t.
  op valid_inputs : inputs_t -> bool.

  type rand1_t.
  type rand2_t.
  type rands_t = rand1_t * rand2_t.
  op valid_rands : rands_t -> inputs_t -> bool.

  type output1_t.
  type output2_t.
  type outputs_t = output1_t * output2_t.

  clone import Functionality with
    type input_t = inputs_t,
    pred valid_input = valid_inputs,
    type output_t = outputs_t.

  type trace_t.

  op protocol : rands_t -> inputs_t -> trace_t * outputs_t.

  axiom correct (r : rands_t) (x : inputs_t) :
    valid_inputs x =>
    valid_rands r x =>
    snd (protocol r x) = f x.

  type leakage1_t.
  type leakage2_t.
  type leakages_t = leakage1_t * leakage2_t.

  op phi1 : input1_t -> leakage1_t.
  op phi2 : input2_t -> leakage2_t.

  op phi (x : inputs_t) : leakages_t = 
    let (x1,x2) = x in
    (phi1 x1, phi2 x2).

end TwoPartyProtocol.
