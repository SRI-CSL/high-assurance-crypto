open PrimeField
open FieldPolynomial
open ECList
open Utils
open Option

open Shamir

open MultiplicationGate

module BGWMultiplicationData = struct

  type input_t = t
  type inputs_t = (input_t * input_t * input_t * input_t * input_t) * 
                  (input_t * input_t * input_t * input_t * input_t)

  type rand_t = monomial list
  type rands_t = rand_t * rand_t * rand_t * rand_t * rand_t

  type output_t = t
  type outputs_t = output_t * output_t * output_t * output_t * output_t

  type message_t = t
  type messages_tuple_t = message_t * message_t * message_t * message_t * message_t

  type out_messages_t = messages_tuple_t
  type in_messages_t = messages_tuple_t

  type trace_t = in_messages_t
  type traces_t = trace_t * trace_t * trace_t * trace_t * trace_t

  let party_exec_round1 (r : rand_t) (x : input_t * input_t) : t * t * t * t * t = 
    let (x1,x2) = x in Shamir.share r (fmul x1 x2)

  let party_exec_round2 (ms : t * t * t * t * t) : output_t = 
    let (m1,m2,m3,m4,m5) = ms in
    interpolate Z.zero (Cons ((!p1,m1), Cons ((!p2,m2), Cons ((!p3,m3), Cons ((!p4,m4), Cons ((!p5,m5), Nil))))))

  let eval_gate (r : rands_t) (x : inputs_t) : traces_t * outputs_t = 
    let (r1,r2,r3,r4,r5) = r in
    let (x1,x2) = x in
    let (x11,x12,x13,x14,x15) = x1 in
    let (x21,x22,x23,x24,x25) = x2 in

    let (m11,m12,m13,m14,m15) = party_exec_round1 r1 (x11,x21) in
    let (m21,m22,m23,m24,m25) = party_exec_round1 r2 (x12,x22) in
    let (m31,m32,m33,m34,m35) = party_exec_round1 r3 (x13,x23) in
    let (m41,m42,m43,m44,m45) = party_exec_round1 r4 (x14,x24) in
    let (m51,m52,m53,m54,m55) = party_exec_round1 r5 (x15,x25) in

    let y1 = party_exec_round2 (m11,m21,m31,m41,m51) in
    let y2 = party_exec_round2 (m12,m22,m32,m42,m52) in
    let y3 = party_exec_round2 (m13,m23,m33,m43,m53) in
    let y4 = party_exec_round2 (m14,m24,m34,m44,m54) in
    let y5 = party_exec_round2 (m15,m25,m35,m45,m55) in

    let tr1 = (m11,m21,m31,m41,m51) in
    let tr2 = (m12,m22,m32,m42,m52) in
    let tr3 = (m13,m23,m33,m43,m53) in
    let tr4 = (m14,m24,m34,m44,m54) in
    let tr5 = (m15,m25,m35,m45,m55) in

    ((tr1, tr2, tr3, tr4, tr5), (y1, y2, y3, y4, y5))

  let local_party_exec (x : input_t * input_t) (r : rand_t) (tr : trace_t) : output_t = party_exec_round2 tr
  let out_messages (x : input_t * input_t) (r : rand_t) (tr : trace_t) : out_messages_t = party_exec_round1 r x
  
  type leakage_t = unit
  type leakages_t = leakage_t * leakage_t * leakage_t * leakage_t * leakage_t

  let party_phi (x : input_t * input_t) : leakage_t = ()

  type view_t = (input_t * input_t) * rand_t * trace_t

  let message_to_string (m : message_t) = if m = witness then "" else Z.to_string m

end

module BGWMultiplicationGate = MultiplicationGate (BGWMultiplicationData)
