open EcPrimeField
open EcCore
open EcOption
open EcList
open FieldPolynomial

open MultiplicationGate
open Shamir

module BGWMultiplicationData (PC : PartyConfiguration) = struct

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

  type rand_t = monomial list
  type rands_t = (pid_t * rand_t) list
  let valid_rand (r : rand_t) : bool =
    size r = Z.add Z.one t

  type msgs_t = t

  type poutput_t = S.share_t
  type poutputs_t = (pid_t * poutput_t) list     

  type in_messages_t = (pid_t * msgs_t) list
  type out_messages_t = (pid_t * msgs_t) list

  let get_messages_to (pid : pid_t) (oms : out_messages_t) : msgs_t = oget (assoc oms pid)
  let get_messages_from (pid : pid_t) (ims : in_messages_t) : msgs_t = oget (assoc ims pid)

  type trace_t = poutputs_t * in_messages_t
  type traces_t = (pid_t * trace_t) list
     
  type view_t = input_t * rand_t * trace_t
  type views_t = (pid_t * view_t) list
               
  let party_exec1 (r : rand_t) (x : input_t) : S.shares_t = 
    let (pub, sec) = x in
    let (sec1, sec2) = sec in S.share r (fmul sec1 sec2)

  let party_exec2 (ms : (pid_t * S.share_t) list) : output_t = 
    interpolate zero ms

  let out_messages_in_messages (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : out_messages_t = party_exec1 r x

  let local_output_share (pid : pid_t) (x : input_t) (r : rand_t) (ims : (pid_t * msgs_t) list) : poutput_t =
    party_exec2 ims

  let rec in_msgs_to_string (im : in_messages_t) : string =
    match im with
    | Nil -> ""
    | Cons(im', Nil) -> Z.to_string (fst im') ^ ": " ^ Z.to_string (snd im')
    | Cons (im', ims) -> Z.to_string (fst im') ^ ": " ^ Z.to_string (snd im') ^ " || " ^ in_msgs_to_string ims

  let rec out_msgs_to_string = function
    | Nil -> ""
    | Cons(x, Nil) -> let (pid_o, ms) = x in Z.to_string pid_o ^ " -> (" ^ in_msgs_to_string ms ^ ")"
    | Cons(x, xs) -> let (pid_o, ms) = x in Z.to_string pid_o ^ " -> (" ^ in_msgs_to_string ms ^ ")\n" ^ out_msgs_to_string xs

  let eval (rs : rands_t) (xs : inputs_t) : (pid_t * ((pid_t * msgs_t) list)) list * poutputs_t =
    let p1s = map (fun pid -> (pid, party_exec1 (oget (assoc rs pid)) (oget (assoc xs pid)))) pid_set in
    let ms = map (fun pid -> (pid, map (fun ms -> let (sender, m) = ms in (sender, get_messages_to pid m)) p1s)) pid_set in 
    let p2s = map (fun pid -> (pid, party_exec2 (oget (assoc ms pid)))) pid_set in
    (ms, p2s)

  let rec zs_to_string = function 
    | Nil -> ""
    | Cons (x,xs) -> Z.to_string (snd x) ^ zs_to_string xs
                                             
  let input_to_string (x : input_t) : string = Z.to_string (fst (snd x))

  let rand_to_string (r : rand_t) : string = ""


                               
  let msgs_to_string (m : msgs_t) : string = Z.to_string m

  let trace_to_string (tr : trace_t) : string = ""

  let view_to_string (v : view_t) : string =
    let (x, r, tr) = v in
    input_to_string x ^ rand_to_string r ^ trace_to_string tr

end

module BGWMultiplicationGate (PC : PartyConfiguration) = MultiplicationGate (Shamir (PC)) (BGWMultiplicationData (PC))
