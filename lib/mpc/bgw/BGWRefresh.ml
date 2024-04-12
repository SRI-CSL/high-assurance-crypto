open EcPrimeField
open EcList
open FieldPolynomial
open EcOption
   
open AGate
open Shamir

module BGWRefreshGateData (PC : PartyConfiguration) = struct

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
  let valid_rand (r : rand_t) : bool = size r = Z.add Z.one t

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

  let party_exec1 (r : rand_t) (x : input_t) : (pid_t * S.share_t) list = S.share r zero

  let party_exec2 (x : input_t) (ms : (pid_t * S.share_t) list) : output_t = fadd (fst (snd x)) (sumt (map snd ms))

  let out_messages (pid : pid_t) (v : view_t) : out_messages_t = let (x, r, tr) = v in party_exec1 r x

  let local_output (pid : pid_t) (v : view_t) : output_t = 
    let (x, r, tr) = v in 
    let (ys, ims) = tr in
    let yi = party_exec2 x (snd tr) in
    if yi = oget (assoc ys pid) then S.reconstruct ys else witness

  let gate (rs : rands_t) (xs : inputs_t) : traces_t * outputs_t =
    let p1s = map (fun pid -> (pid, party_exec1 (oget (assoc rs pid)) (oget (assoc xs pid)))) pid_set in
    let ms = map (fun pid -> (pid, map (fun ms -> let (sender, m) = ms in (sender, get_messages_to pid m)) p1s)) pid_set in 
    let pouts = map (fun pid -> (pid, party_exec2 (oget (assoc xs pid)) (oget (assoc ms pid)))) pid_set in

    let y = S.reconstruct pouts in
    let ys = map (fun pid -> (pid, y)) pid_set in
    let tr = map (fun pid -> (pid, (pouts, oget (assoc ms pid)))) pid_set in
    (tr, ys)

  let rec zs_to_string = function 
    | Nil -> ""
    | Cons (x,xs) -> Z.to_string (snd x) ^ zs_to_string xs
                                             
  let input_to_string (x : input_t) : string = Z.to_string (fst (snd x))

  let rand_to_string (r : rand_t) : string = ""

  let rec in_msgs_to_string (im : in_messages_t) : string =
    match im with
    | Nil -> ""
    | Cons(im', Nil) -> Z.to_string (fst im') ^ " -> " ^ Z.to_string (snd im')
    | Cons (im', ims) -> Z.to_string (fst im') ^ " -> " ^ Z.to_string (snd im') ^ " || " ^ in_msgs_to_string ims

  let msgs_to_string (m : msgs_t) : string = Z.to_string m
    
  let trace_to_string (tr : trace_t) : string = ""

  let view_to_string (v : view_t) : string =
    let (x, r, tr) = v in
    input_to_string x ^ rand_to_string r ^ trace_to_string tr

end

module BGWRefreshGate (PC : PartyConfiguration) = Gate (BGWRefreshGateData (PC))
