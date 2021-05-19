open ECList
open FieldPolynomial
   
open Shamir
open BGWAddition
open BGWMultiplication
open BGWSMultiplication

open ArithmeticProtocol

module BGWGateData (PC: PartyConfiguration) = struct
  
  module BGWArithP = ArithmeticProtocolData (ShamirData (PC)) (BGWAdditionData (PC)) (BGWMultiplicationData (PC)) (BGWSMultiplicationData (PC))
  include BGWArithP

  let rec zss_to_string = function 
    | Nil -> ""
    | Cons (x,xs) -> Z.to_string (snd x) ^ zss_to_string xs

  let rec zs_to_string = function 
    | Nil -> ""
    | Cons (x,xs) -> Z.to_string x ^ zs_to_string xs

  let rec msgs_to_string = function
    | PInputLM w -> Z.to_string w
    | SInputLM w -> ""
    | ConstantLM (gid, c) -> Z.to_string c
    | AdditionLM (gid, tr, trl, trr) -> "" ^ msgs_to_string trl ^ msgs_to_string trr
    | MultiplicationLM (gid, tr, trl, trr) -> Z.to_string tr ^ msgs_to_string trl ^ msgs_to_string trr
    | SMultiplicationLM (gid, tr, trl, trr) -> "" ^ msgs_to_string trl ^ msgs_to_string trr

  let rec gate_local_trace_to_string = function
    | PInputLT w -> Z.to_string w
    | SInputLT w -> ""
    | ConstantLT (gid, c) -> Z.to_string c
    | AdditionLT (gid, m, wl, wr) -> "" ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr
    | MultiplicationLT (gid, m, wl, wr) -> zss_to_string m ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr
    | SMultiplicationLT (gid, m, wl, wr) -> "" ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr

  let rec gate_local_traces_to_string = function
    | Nil -> ""
    | Cons (x,xs) -> gate_local_trace_to_string x ^ gate_local_traces_to_string xs

  let input_to_string (x : input_t) : string =
    let (xp,xs) = x in zs_to_string xp ^ zs_to_string xs

  let gate_rand_to_string = function
    | AdditionRand r -> ""
    | MultiplicationRand r -> polynomial_to_string r
    | SMultiplicationRand r -> ""
    | BadRand -> ""

  let rec rand_to_string_concat = function
    | Nil -> ""
    | Cons (r, rs) -> gate_rand_to_string (snd r) ^ rand_to_string_concat rs

  let rand_to_string (r : rand_t) : string = rand_to_string_concat r

  let trace_to_string (tr : trace_t) : string =
    let (ys, ims) = tr in zss_to_string ys ^ gate_local_trace_to_string ims

  let view_to_string (v : view_t) : string =
    let (x,r,tr) = v in input_to_string x ^ rand_to_string r ^ trace_to_string tr

end

module BGWGate (PC : PartyConfiguration) = BGWGateData (PC)
