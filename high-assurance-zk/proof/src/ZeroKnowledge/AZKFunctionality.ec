from General require import ECList.

from Circuit require import ACircuit.
from Functionalities require import AFunctionality.

theory ZKFunctionality.

  type witness_t.
  type statement_t.
  op relation : witness_t -> statement_t -> bool.

  op valid_witness : witness_t -> statement_t -> bool.
  op valid_statement : statement_t -> bool.

  op language (x : statement_t) =
    exists (w : witness_t), relation w x.

  lemma relation_language (w : witness_t) (x : statement_t) :
    relation w x => language x.
  proof. by move => ?; rewrite /language; exists w. qed.

  type input1_t = witness_t * statement_t.
  type input2_t = statement_t.
  type inputs_t = input1_t * input2_t.
  op valid_inputs : inputs_t -> bool.

  type output1_t = unit.
  type output2_t = bool.
  type outputs_t = output1_t * output2_t.

  op f (x : inputs_t) : outputs_t = 
    let (x1,x2) = x in
    let (w,x) = x1 in
    ((), relation w x).

  clone import Functionality with
    type input_t = inputs_t,
    pred valid_input = valid_inputs,
    type output_t = outputs_t,
    op f = f.

end ZKFunctionality.
