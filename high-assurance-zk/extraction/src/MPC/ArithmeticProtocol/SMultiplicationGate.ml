open PrimeField
open Option
open ECList

open AGate
open ASecretSharingScheme

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

  val view_to_string : view_t -> string

end

module SMultiplicationGateData
         (SSD : sig include SecretSharingSchemeData with type secret_t = t end)
         (SMGED : sig include SMultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                       type pinput_t = SSD.share_t and
                                                       type sinput_t = SSD.share_t and
                                                       type output_t = SSD.secret_t and
                                                       type poutput_t = SSD.share_t end) = struct

  module S = SecretSharingScheme (SSD)
  
  let n : Z.t = SSD.n
  let t : Z.t = SSD.t

  type pid_t = SSD.pid_t
  let pid_set : pid_t list = SSD.pid_set

  type pinput_t = SMGED.pinput_t
  type sinput_t = SMGED.sinput_t
  type input_t = SMGED.input_t
  type inputs_t = SMGED.inputs_t
                
  type output_t = SMGED.output_t
  type outputs_t = SMGED.outputs_t
                
  type rand_t = SMGED.rand_t
  type rands_t = SMGED.rands_t
  
  type msgs_t = SMGED.msgs_t
  type in_messages_t = SMGED.in_messages_t
  type out_messages_t = SMGED.out_messages_t
                        
  type poutput_t = SMGED.poutput_t
  type poutputs_t = SMGED.poutputs_t

  type trace_t = SMGED.trace_t
  type traces_t = SMGED.traces_t

  type view_t = SMGED.view_t
  type views_t = SMGED.views_t
     
  let out_messages (pid : pid_t) (v : view_t) : out_messages_t = 
    let (xi,ri,tri) = v in
    SMGED.out_messages_in_messages pid xi ri (snd tri)

  let local_output (pid : pid_t) (v : view_t) : output_t =
    let (x, r, tr) = v in
    let (ys, ims) = tr in
    let yi = SMGED.local_output_share pid x r (snd tr) in
    if oget (assoc ys pid) = yi then S.reconstruct ys else witness

  let gate (rs : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let (tr,ys) = SMGED.eval rs xs in
    let y = S.reconstruct ys in
    (map (fun pid -> (pid, (ys, oget (assoc tr pid)))) pid_set, 
     map (fun pid -> (pid, y)) pid_set)
    
  let view_to_string = SMGED.view_to_string
                     
end
                                                                                         
module SMultiplicationGate
         (SSD : sig include SecretSharingSchemeData with type secret_t = t end)
         (SMGED : sig include SMultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                       type pinput_t = SSD.share_t and
                                                       type sinput_t = SSD.share_t and
                                                       type output_t = SSD.secret_t and
                                                       type poutput_t = SSD.share_t end) = Gate (SMultiplicationGateData (SSD) (SMGED))
    
