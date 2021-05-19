open ECList
open FieldPolynomial
   
open Shamir
open BGWAddition
open BGWMultiplication
open BGWSMultiplication
open BGWGate   
open BGWRefresh

open ArithmeticProtocol
   
open WeakPrivacyComposition

module BGWData (PC: PartyConfiguration) = struct
  
  module BGWP = WeakPrivacyComposition (ShamirData (PC)) (BGWAdditionData (PC)) (BGWMultiplicationData (PC)) (BGWSMultiplicationData (PC)) (BGWRefreshData (PC))
  include BGWP

  let rec zss_to_string = function 
    | Nil -> ""
    | Cons (x,xs) -> Z.to_string (snd x) ^ zss_to_string xs

  let rec zs_to_string = function 
    | Nil -> ""
    | Cons (x,xs) -> Z.to_string x ^ zs_to_string xs

  let rec msgs_to_string = function
    | ArithP.PInputLM w -> Z.to_string w
    | ArithP.SInputLM w -> ""
    | ArithP.ConstantLM (gid, c) -> Z.to_string c
    | ArithP.AdditionLM (gid, tr, trl, trr) -> "" ^ msgs_to_string trl ^ msgs_to_string trr
    | ArithP.MultiplicationLM (gid, tr, trl, trr) -> Z.to_string tr ^ msgs_to_string trl ^ msgs_to_string trr
    | ArithP.SMultiplicationLM (gid, tr, trl, trr) -> "" ^ msgs_to_string trl ^ msgs_to_string trr

  let rec gate_local_trace_to_string = function
    | ArithP.PInputLT w -> Z.to_string w
    | ArithP.SInputLT w -> ""
    | ArithP.ConstantLT (gid, c) -> Z.to_string c
    | ArithP.AdditionLT (gid, m, wl, wr) -> "" ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr
    | ArithP.MultiplicationLT (gid, m, wl, wr) -> zss_to_string m ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr
    | ArithP.SMultiplicationLT (gid, m, wl, wr) -> "" ^ gate_local_trace_to_string wl ^ gate_local_trace_to_string wr

  let rec gate_local_traces_to_string = function
    | Nil -> ""
    | Cons (x,xs) -> gate_local_trace_to_string x ^ gate_local_traces_to_string xs

  let input_to_string (x : input_t) : string =
    let (xp,xs) = x in zs_to_string xp ^ zs_to_string xs

  let gate_rand_to_string = function
    | ArithP.AdditionRand r -> ""
    | ArithP.MultiplicationRand r -> polynomial_to_string r
    | ArithP.SMultiplicationRand r -> ""
    | ArithP.BadRand -> ""

  let rec rand_to_string_concat = function
    | Nil -> ""
    | Cons (r, rs) -> gate_rand_to_string (snd r) ^ rand_to_string_concat rs

  let rand_to_string (r : rand_t) : string =
    let (rw, rs) = r in rand_to_string_concat rw ^ polynomial_to_string rs

  let trace_to_string (tr : trace_t) : string =
    let (ys, ims) = tr in
    let (imswp, imssp) = ims in zss_to_string ys ^ gate_local_trace_to_string imswp ^ zss_to_string imssp

  let view_to_string (v : view_t) : string =
    let (x,r,tr) = v in input_to_string x ^ rand_to_string r ^ trace_to_string tr                  
end
                                            
module BGW (PC : PartyConfiguration) = BGWData (PC)
