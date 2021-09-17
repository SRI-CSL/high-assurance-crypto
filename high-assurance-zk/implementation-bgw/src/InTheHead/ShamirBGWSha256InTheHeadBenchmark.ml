open ECList
open PrimeField
open Option
open Core

open ASecretSharingScheme
   
open InTheHeadBenchmark

open Shamir
open BGW
open CRPRFCommitment

module Sha256 (PC : PartyConfiguration) = struct 

  module BGW = BGW (PC)
  
  type input_t = BGW.view_t
  type output_t = string
  type key_t = unit

  let f (k : key_t) (x : input_t) : output_t = 
    let sha256 = Cryptokit.Hash.sha256 () in
    sha256#add_string (BGW.view_to_string x);
    String.sub (sha256#result) 0 16

end

module BGWBool (PC : PartyConfiguration) = struct

  module BGW = BGW (PC)

  type circuit_t = BGW.circuit_t

  let n : Z.t = PC.n
  let t : Z.t = PC.t

  type pid_t = PC.pid_t
  let pid_set : pid_t list = PC.pid_set

  type pinput_t = BGW.pinput_t
  type sinput_t = BGW.sinput_t
  type input_t = BGW.input_t
  type inputs_t = BGW.inputs_t

  type output_t = bool
  type outputs_t = (pid_t * output_t) list

  type rand_t = BGW.rand_t
  type rands_t = BGW.rands_t

  type msgs_t = BGW.msgs_t
  type in_messages_t = BGW.in_messages_t
  type out_messages_t = BGW.out_messages_t

  type poutput_t = BGW.poutput_t
  type poutputs_t = BGW.poutputs_t

  type trace_t = BGW.trace_t
  type traces_t = BGW.traces_t
                                  
  type view_t = BGW.view_t
  type views_t = BGW.views_t

  let out_messages = BGW.out_messages
                   
  let local_output (c : circuit_t) (pid : pid_t) (v : view_t) : output_t =
    let y = BGW.local_output c pid v in
    if Z.equal Z.zero y then true else false

  let protocol (c : circuit_t) (r : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let (tr, ys') = BGW.protocol c r xs in
    let ys = map (fun pid -> (pid, if Z.equal Z.zero (oget (assoc ys' pid)) then true else false)) pid_set in
    (tr, ys)

  (*let valid_circuit_trace = BGW.valid_circuit_trace*)

  let view_to_string = BGW.view_to_string

  let consistent_views = BGW.consistent_views
end

module InTheHeadZKData = struct

  type witness_t = t list
  type instance_t = t list
  let relation (w : witness_t) (x : instance_t) : bool = true
end

module ShamirBGWSha256InTheHeadData (PC : PartyConfiguration) = InTheHeadSigmaProtocolData (InTheHeadZKData) (ListSecretSharing (Shamir (PC))) (BGWBool (PC)) (CRPRFCommitment (Sha256 (PC)))
                       
module ShamirBGWSha256InTheHeadBenchmark (PC : PartyConfiguration) = InTheHead (InTheHeadZKData) (ListSecretSharing (Shamir (PC))) (BGWBool (PC)) (CRPRFCommitment (Sha256 (PC)))
