open EcList
open EcOption
   
module type GateData = sig

  val n : Z.t
  val t : Z.t
    
  type pid_t
  val pid_set : pid_t list

  type pinput_t
  type sinput_t
  type input_t = pinput_t * (sinput_t * sinput_t)
  type inputs_t = (pid_t * input_t) list

  type output_t
  type outputs_t = (pid_t * output_t) list

  type rand_t
  type rands_t = (pid_t * rand_t) list
  val valid_rand : rand_t -> bool

  type msgs_t

  type poutput_t
  type poutputs_t = (pid_t * poutput_t) list     

  type in_messages_t = (pid_t * msgs_t) list
  type out_messages_t = (pid_t * msgs_t) list

  type trace_t = poutputs_t * in_messages_t
  type traces_t = (pid_t * trace_t) list
     
  type view_t = input_t * rand_t * trace_t
  type views_t = (pid_t * view_t) list
     
  val out_messages : pid_t -> view_t -> out_messages_t
  val local_output : pid_t -> view_t -> output_t

  val gate : rands_t -> inputs_t -> traces_t * outputs_t

  val rand_to_string : rand_t -> string
  val msgs_to_string : msgs_t -> string
  val in_msgs_to_string : in_messages_t -> string
  val view_to_string : view_t -> string

end

module Gate (GD : GateData) = struct
  
  let n : Z.t = GD.n
  let t : Z.t = GD.t
  type pid_t = GD.pid_t
  let pid_set = GD.pid_set

  type pinput_t = GD.pinput_t
  type sinput_t = GD.sinput_t
  type input_t = GD.input_t
  type inputs_t = GD.inputs_t
                
  type output_t = GD.output_t
  type outputs_t = GD.outputs_t

  type rand_t = GD.rand_t
  type rands_t = GD.rands_t
  let valid_rand = GD.valid_rand

  type msgs_t = GD.msgs_t
  type in_messages_t = GD.in_messages_t
  type out_messages_t = GD.out_messages_t

  let get_messages_to (pid : pid_t) (oms : out_messages_t) : msgs_t = oget (assoc oms pid)
  let get_messages_from (pid : pid_t) (ims : in_messages_t) : msgs_t = oget (assoc ims pid)
  
  type poutput_t = GD.poutput_t
  type poutputs_t = GD.poutputs_t

  type trace_t = GD.trace_t
  type traces_t = GD.traces_t

  type view_t = GD.view_t
  type views_t = GD.views_t

  let out_messages = GD.out_messages
  let local_output = GD.local_output

  let gate = GD.gate

  let rand_to_string = GD.rand_to_string
  let msgs_to_string = GD.msgs_to_string
  let in_msgs_to_string = GD.in_msgs_to_string
  let view_to_string = GD.view_to_string
               
end
