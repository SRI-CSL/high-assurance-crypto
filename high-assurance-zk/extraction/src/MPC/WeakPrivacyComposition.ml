open ECList
open Core
open Option
open PrimeField

open ASecretSharingScheme
open AdditionGate
open MultiplicationGate
open SMultiplicationGate
open ArithmeticProtocol
open AGate

module WeakPrivacyComposition
         (SSD : sig include SecretSharingSchemeData with type secret_t = t and type share_t = t end)
         (AGED : sig include AdditionGateEvalData with type pid_t = SSD.pid_t and
                                                       type pinput_t = unit and
                                                       type sinput_t = SSD.share_t and
                                                       type output_t = SSD.secret_t and
                                                       type poutput_t = SSD.share_t end)
         (MGED : sig include MultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                             type pinput_t = unit and
                                                             type sinput_t = SSD.share_t and
                                                             type output_t = SSD.secret_t and
                                                             type poutput_t = SSD.share_t end)
         (SMGED : sig include SMultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                               type pinput_t = SSD.share_t and
                                                               type sinput_t = SSD.share_t and
                                                               type output_t = SSD.secret_t and
                                                               type poutput_t = SSD.share_t end)
         (SGD : sig include GateData with type pid_t = SSD.pid_t and
                                         type pinput_t = unit and
                                         type sinput_t = SSD.share_t and
                                         type output_t = SSD.secret_t and
                                         type poutput_t = SSD.share_t end) = struct


  (*module ArithP = ArithmeticProtocolData (SSD) (AGED) (MGED) (SMGED)*)
  module ArithP = ArithmeticProtocolData (SSD) (AGED) (MGED) (SMGED)
  module SG = Gate (SGD)

  type circuit_t = ArithP.circuit_t
  let n : Z.t = SSD.n
  let t : Z.t = SSD.t
  type pid_t = SSD.pid_t
  let pid_set : pid_t list = SSD.pid_set

  type pinput_t = ArithP.pinput_t
  type sinput_t = ArithP.sinput_t
  type input_t = pinput_t * sinput_t
  type inputs_t = (pid_t * input_t) list
                
  type output_t = ArithP.output_t
  type outputs_t = (pid_t * output_t) list

  type rand_t = ArithP.rand_t * SG.rand_t
  type rands_t = (pid_t * rand_t) list

  type msgs_t = ArithP.msgs_t * SG.msgs_t
  type in_messages_t = ArithP.gate_local_traces_t * SG.in_messages_t
  type out_messages_t = ArithP.out_messages_t * SG.out_messages_t

  let get_messages_from (pid : pid_t) (ims : in_messages_t) : msgs_t =
    let (imwp, imsp) = ims in (ArithP.get_local_msgs_from pid imwp, SG.get_messages_from pid imsp)

  let get_messages_to (pid : pid_t) (oms : out_messages_t) : msgs_t =
    let (omwp, omsp) = oms in (ArithP.get_messages_to pid omwp, SG.get_messages_to pid omsp)
                         
  type poutput_t = SSD.share_t
  type poutputs_t = (pid_t * poutput_t) list

  type trace_t = SSD.shares_t * in_messages_t
  type traces_t = (pid_t * trace_t) list

  type view_t = input_t * rand_t * trace_t
  type views_t = (pid_t * view_t) list
               
  let protocol (c : circuit_t) (rs : rands_t) (xs : inputs_t) = 
    let (topo, gg) = c in
    let rwp = map (fun pid -> (pid, fst (oget (assoc rs pid)))) pid_set in
    let (trwp, ys) = ArithP.eval_circuit gg rwp xs in
    let rsp = map (fun pid -> (pid, snd (oget (assoc rs pid)))) pid_set in
    let xsp = map (fun pid -> (pid, ((), (oget (assoc ys pid), witness)))) pid_set in
    let (trsp, zs) = SG.gate rsp xsp in
    (map (fun pid -> (pid, (fst (oget (assoc trsp pid)), (ArithP.get_local_trace pid trwp, snd (oget (assoc trsp pid)))))) pid_set, zs)
     
  let local_output c pid v = 
    let (x, r, tr) = v in
    let (topo, gg) = c in
    let (riwp, risp) = r in
    let (ys, ims) = tr in
    let (imswp, imssp) = ims in
    let yi = ArithP.local_output_gates pid x riwp imswp in
    SG.local_output pid (((),(yi, witness)), risp, (ys, imssp))

  let out_messages c pid v = 
    let (topo, gg) = c in
    let (xi, ri, tri) = v in
    let (riwp, risp) = ri in
    let (ys, ims) = tri in
    let (triwp, trisp) = ims in
    let yi = ArithP.local_output_gates pid xi riwp triwp in
    let imwp = ArithP.out_messages_gates pid xi riwp triwp in
    let imsp = SG.out_messages pid (((),(yi, witness)), risp, (ys, trisp)) in
    (imwp, imsp)

  let valid_circuit_trace (c : circuit_t) (ims : in_messages_t) : bool =
    let (imswp, imssp) = ims in
    ArithP.valid_circuit_trace c imswp

    (* 
  let view_to_string (v : view_t) : string =
    let (x, r, tr) = v in
    let (ys, tr) = tr in
    let (trwp, trsp) = tr in
    ArithP.view_to_string (x,r,tr)*)
                 
end

(*module WeakPrivate
         (SSD : sig include SecretSharingSchemeData with type secret_t = t and type share_t = t end)
         (AGED : sig include AdditionGateEvalData with type pid_t = SSD.pid_t and
                                     G                              type pinput_t = unit and
                                                       type sinput_t = SSD.share_t and
                                                       type output_t = SSD.secret_t and
                                                       type poutput_t = SSD.share_t end)
         (MGED : sig include MultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                             type pinput_t = unit and
                                                             type sinput_t = SSD.share_t and
                                                             type output_t = SSD.secret_t and
                                                             type poutput_t = SSD.share_t end)
         (SMGED : sig include SMultiplicationGateEvalData with type pid_t = SSD.pid_t and
                                                               type pinput_t = SSD.share_t and
                                                               type sinput_t = SSD.share_t and
                                                               type output_t = SSD.secret_t and
                                                               type poutput_t = SSD.share_t end)
         (SG : sig include Gate with type pid_t = SSD.pid_t and
                                     type pinput_t = unit and
                                     type sinput_t = SSD.share_t and
                                     type output_t = SSD.secret_t and
                                     type poutput_t = SSD.share_t end) = Protocol (WeakPrivacyComposition (SSD) (AGED) (MGED) (SMEG) (SG))*)
                                                                          
