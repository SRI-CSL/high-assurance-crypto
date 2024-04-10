open EcList
open EcOption
open EcCore

open ACircuit
   
module type MPCProtocolData = sig

  type circuit_t

  val n : Z.t
  val t : Z.t

  type pid_t
  val pid_set : pid_t list

  type pinput_t
  type sinput_t
  type input_t = pinput_t * sinput_t
  type inputs_t = (pid_t * input_t) list

  type output_t
  type outputs_t = (pid_t * output_t) list

  type rand_t
  type rands_t = (pid_t * rand_t) list

  type msgs_t
  type in_messages_t
  type out_messages_t
                      
  type poutput_t
  type poutputs_t = (pid_t * poutput_t) list

  type trace_t = poutputs_t * in_messages_t
  type traces_t = (pid_t * trace_t) list

  type view_t = input_t * rand_t * trace_t
  type views_t = (pid_t * view_t) list

  val out_messages : circuit_t -> pid_t -> view_t -> out_messages_t
  val local_output : circuit_t -> pid_t -> view_t -> output_t

  val protocol : circuit_t -> rands_t -> inputs_t -> traces_t * outputs_t

  val view_to_string : view_t -> string

  val consistent_views : circuit_t -> pinput_t -> view_t -> view_t -> pid_t -> pid_t -> bool
    
end

module MPCProtocol (PD : MPCProtocolData) = struct
    
  let n : Z.t = PD.n
  let t : Z.t = PD.t
  type pid_t = PD.pid_t
  let pid_set = PD.pid_set

  type circuit_t = PD.circuit_t

  type pinput_t = PD.pinput_t
  type sinput_t = PD.sinput_t
  type input_t = PD.input_t
  type inputs_t = PD.inputs_t

  type output_t = PD.output_t
  type outputs_t = PD.outputs_t

  type rand_t = PD.rand_t
  type rands_t = PD.rands_t

  type msgs_t = PD.msgs_t
  type in_messages_t = PD.in_messages_t
  type out_messages_t = PD.out_messages_t

  type poutput_t = PD.poutput_t
  type poutputs_t = PD.poutputs_t

  type trace_t = PD.trace_t
  type traces_t = PD.traces_t

  type view_t = PD.view_t
  type views_t = PD.views_t
               
  let out_messages = PD.out_messages
  let local_output = PD.local_output

  let protocol = PD.protocol

  let view_to_string = PD.view_to_string

  let consistent_views = PD.consistent_views
               
end
