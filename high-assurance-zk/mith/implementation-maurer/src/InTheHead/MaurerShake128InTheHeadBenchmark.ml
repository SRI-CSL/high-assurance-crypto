open ECList
open ECOption
open ECCore

open ASecretSharingScheme
   
open InTheHeadBenchmark

open MaurerSS
open NextMsgMaurerP
open NextMsgMaurerAPI
open NextMsgMaurerCompat
open CRPRFCommitmentWrapper
   
module MaurerBool = struct

  type circuit_t = MaurerProtocolFunctionality.circuit_t

  let n : Z.t = MaurerProtocolFunctionality.n
  let t : Z.t = MaurerProtocolFunctionality.t

  type pid_t = MaurerProtocolFunctionality.pid_t
  let pid_set : pid_t list = MaurerProtocolFunctionality.pid_set

  type pinput_t = MaurerProtocolFunctionality.pinput_t
  type pinputs_t = MaurerProtocolFunctionality.pinputs_t
  type sinput_t = MaurerProtocolFunctionality.sinput_t
  type sinputs_t = MaurerProtocolFunctionality.sinputs_t
  type input_t = MaurerProtocolFunctionality.input_t
  type inputs_t = MaurerProtocolFunctionality.inputs_t

  type output_t = bool
  type outputs_t = (pid_t * output_t) list

  type rand_t = MaurerBoolProtocol.rand_t
  type rands_t = MaurerBoolProtocol.rands_t

  type in_messages_t = MaurerBoolProtocol.in_messages_t

  type poutput_t = MaurerBoolProtocol.poutput_t
  type poutputs_t = MaurerBoolProtocol.poutputs_t

  type trace_t = MaurerBoolProtocol.trace_t
  type traces_t = MaurerBoolProtocol.traces_t
                                  
  type view_t = MaurerBoolProtocol.view_t
  type views_t = MaurerBoolProtocol.views_t
                   
  let local_output (c : circuit_t) (pid : pid_t) (v : view_t) : output_t =
    MaurerBoolProtocol.local_output c pid v

  let protocol (c : circuit_t) (r : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    MaurerBoolProtocol.protocol c r xs

  let view_to_string x = "" 
  let consistent_views = MaurerProtocol.consistent_views
  let consistent_views_public_output = MaurerProtocol.consistent_views_public_output

end

module InTheHeadZKData = struct

  type witness_t = (int * int * int * int) list
  type instance_t = (int * int * int * int) list
end

module MaurerShake128InTheHead = 
 InTheHeadBenchmark (InTheHeadZKData) (ListSecretSharing (MaurerSS)) (MaurerBool) (CRPRFCommitmentWrapper)
