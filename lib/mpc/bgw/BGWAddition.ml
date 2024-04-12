open EcPrimeField
open EcCore
open EcOption
open EcList

open AdditionGate
open Shamir

module BGWAdditionData (PC : PartyConfiguration) = struct

  module S = Shamir(PC)

  let n : Z.t = PC.n
  let t : Z.t = PC.t
    
  type pid_t = PC.pid_t
  let pid_set : pid_t list = PC.pid_set

  type pinput_t = unit
  type sinput_t = S.share_t
  type input_t = pinput_t * (sinput_t * sinput_t)
  type inputs_t = (pid_t * input_t) list
  
  type output_t = S.secret_t
  type outputs_t = (pid_t * output_t) list

  type rand_t = unit
  type rands_t = (pid_t * rand_t) list
  let valid_rand (r : rand_t) : bool = true

  type msgs_t = unit

  type poutput_t = S.share_t
  type poutputs_t = (pid_t * poutput_t) list     

  type in_messages_t = (pid_t * msgs_t) list
  type out_messages_t = (pid_t * msgs_t) list

  type trace_t = poutputs_t * in_messages_t
  type traces_t = (pid_t * trace_t) list
     
  type view_t = input_t * rand_t * trace_t
  type views_t = (pid_t * view_t) list
               
  let party_exec (r : rand_t) (x : input_t) : output_t = 
    let (pub, sec) = x in let (x1,x2) = sec in fadd x1 x2
  let empty_trace : (pid_t * msgs_t) list = Nil

  let out_messages_in_messages (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : out_messages_t = Nil

  let local_output_share (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : poutput_t =
    let (pub, sec) = x in
    let (x1, x2) = sec in fadd x1 x2

  let eval (rs : rands_t) (xs : inputs_t) : (pid_t * ((pid_t * msgs_t) list)) list * poutputs_t =
    let tr = map (fun pid -> (pid, empty_trace)) pid_set in
    let ys = map (fun pid -> (pid, party_exec (oget (assoc rs pid)) 
                                              (oget (assoc xs pid)))) pid_set in
    (tr,ys)

  let rec zs_to_string = function 
    | Nil -> ""
    | Cons (x,xs) -> Z.to_string (snd x) ^ zs_to_string xs
                                             
  let input_to_string (x : input_t) : string = Z.to_string (fst (snd x))

  let rand_to_string (r : rand_t) : string = ""

  let in_msgs_to_string (im : in_messages_t) : string = ""
  let msgs_to_string (im : msgs_t) : string = ""
  let trace_to_string (tr : trace_t) : string = ""

  let view_to_string (v : view_t) : string =
    let (x, r, tr) = v in
    input_to_string x ^ rand_to_string r ^ trace_to_string tr

end

module BGWAdditionGate (PC : PartyConfiguration) = AdditionGate (Shamir (PC)) (BGWAdditionData (PC))
