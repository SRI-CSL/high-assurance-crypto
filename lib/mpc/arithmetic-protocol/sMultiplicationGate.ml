open EcPrimeField
open EcOption
open EcList

open AGate
open ASecretSharing

module type SMultiplicationGateEvalData = sig

  type pid_t
  
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

  val out_messages_in_messages : pid_t -> input_t -> rand_t -> (pid_t * msgs_t) list -> (pid_t * msgs_t) list
  val local_output_share : pid_t -> input_t -> rand_t -> (pid_t * msgs_t) list -> poutput_t
  val eval : rands_t -> inputs_t -> (pid_t * ((pid_t * msgs_t) list)) list * poutputs_t

  val rand_to_string : rand_t -> string
  val msgs_to_string : msgs_t -> string
  val in_msgs_to_string : in_messages_t -> string
  val view_to_string : view_t -> string

end

module SMultiplicationGateData
         (SSD : sig include SecretSharingSchemeData with type secret_t = t end)
         (AGED : sig include SMultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                       type pinput_t = SSD.share_t and
                                                       type sinput_t = SSD.share_t and
                                                       type output_t = SSD.secret_t and
                                                       type poutput_t = SSD.share_t end) = struct

  module S = SecretSharingScheme (SSD)
  
  let n : Z.t = SSD.n
  let t : Z.t = SSD.t

  type pid_t = SSD.pid_t
  let pid_set : pid_t list = SSD.pid_set

  type pinput_t = AGED.pinput_t
  type sinput_t = AGED.sinput_t
  type input_t = AGED.input_t
  type inputs_t = AGED.inputs_t
                
  type output_t = AGED.output_t
  type outputs_t = AGED.outputs_t
                
  type rand_t = AGED.rand_t
  type rands_t = AGED.rands_t
  let valid_rand = AGED.valid_rand
  
  type msgs_t = AGED.msgs_t
  type in_messages_t = AGED.in_messages_t
  type out_messages_t = AGED.out_messages_t
                        
  type poutput_t = AGED.poutput_t
  type poutputs_t = AGED.poutputs_t

  type trace_t = AGED.trace_t
  type traces_t = AGED.traces_t

  type view_t = AGED.view_t
  type views_t = AGED.views_t
     
  let out_messages (pid : pid_t) (v : view_t) : out_messages_t = 
    let (xi,ri,tri) = v in
    AGED.out_messages_in_messages pid xi ri (snd tri)

  let local_output (pid : pid_t) (v : view_t) : output_t =
    let (x, r, tr) = v in
    let (ys, ims) = tr in
    let yi = AGED.local_output_share pid x r (snd tr) in
    if oget (assoc ys pid) = yi then S.reconstruct ys else witness

  let gate (rs : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let (tr,ys) = AGED.eval rs xs in
    let y = S.reconstruct ys in
    (map (fun pid -> (pid, (ys, oget (assoc tr pid)))) pid_set, 
     map (fun pid -> (pid, y)) pid_set)

  let rand_to_string = AGED.rand_to_string
  let in_msgs_to_string = AGED.in_msgs_to_string
  let msgs_to_string = AGED.msgs_to_string
  let view_to_string = AGED.view_to_string
                     
end
                                                                                         
module SMultiplicationGate
         (SSD : sig include SecretSharingSchemeData with type secret_t = t end)
         (AGED : sig include SMultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                       type pinput_t = SSD.share_t and
                                                       type sinput_t = SSD.share_t and
                                                       type output_t = SSD.secret_t and
                                                       type poutput_t = SSD.share_t end) = Gate (SMultiplicationGateData (SSD) (AGED))
