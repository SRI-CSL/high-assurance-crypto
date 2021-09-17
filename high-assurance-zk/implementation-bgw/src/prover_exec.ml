open Option
open ECList
open FieldPolynomial
open PrimeField
open Utils

open ArithmeticCircuit
open ArithmeticDomain
open ArithmeticGates

open BGWAddition
open BGWMultiplication
open BGWSMultiplication
open BGWRefresh
   
open Shamir

open ArithmeticProtocol

open BGW

open ShamirBGWSha256InTheHead

open InTheHead

let dpolynomial (d : Z.t) : monomial list =
  let poly = ref Nil in
  
  for i = 0 to Z.to_int d do
    let quit = ref false in
    let coef = ref Z.zero in
    
    while not !quit do
      coef := dt () ;
      if not (Z.equal !coef Z.zero) then quit := true
    done ;
    
    poly := Cons ({ coef = !coef ; expo = Z.of_int i}, !poly) ;
  done ;

  !poly

module PC = struct
  let n = Z.of_string "5"
  let t = Z.of_string "2"
  type pid_t = pid_mpc_t
  let pid_set = pid_mpc_set
end
          
module Shamir = Shamir (PC)
module BGWAdd = BGWAdditionGate (PC)
module BGWMul = BGWMultiplicationGate (PC)
module BGWSMul = BGWSMultiplicationGate (PC)
module BGWRefresh = BGWRefreshGate (PC)

module BGWData = ArithmeticProtocolData (ShamirData (PC)) (BGWAdditionData (PC)) (BGWMultiplicationData (PC)) (BGWSMultiplicationData (PC))

module ShamirBGWSha256InTheHeadData = ShamirBGWSha256InTheHeadData (PC)
               
let rec random_generator_gates (g : ArithmeticGates.gates_t) =
  match g with
  | PInput _ -> Nil
  | SInput _ -> Nil
  | Constant _ -> Nil
  | Addition (gid, wl, wr) -> 
     concat (concat (random_generator_gates wl) (Cons ((gid, BGWData.AdditionRand ()), Nil))) (random_generator_gates wr)
  | Multiplication (gid, wl, wr) -> 
     concat (concat (random_generator_gates wl) (Cons ((gid, BGWData.MultiplicationRand (dpolynomial PC.t)), Nil))) (random_generator_gates wr)
  | SMultiplication (gid, wl, wr) -> 
     concat (concat (random_generator_gates wl) (Cons ((gid, BGWData.SMultiplicationRand ()), Nil))) (random_generator_gates wr)

let rec random_generator = function
  | Nil -> Nil
  | Cons (g,gs) -> concat (random_generator_gates g) (random_generator gs)
                 
let rec commitment_random_generator i n =
  if Z.equal i n then Nil
  else Cons ((), commitment_random_generator (Z.add i Z.one) n)
  
let rec share_random_generator i n =
  if Z.equal i n then Nil
  else
    let r = dpolynomial PC.t in
    Cons (r, share_random_generator (Z.add i Z.one) n)
    
let int_to_pid x =
  if x = 1 then !p1
  else if x = 2 then !p2
  else if x = 3 then !p3
  else if x = 4 then !p4
  else !p5
;;
  
let verifier_randomness_generator =
  let r1 = ref 0 in
  let r2 = ref 0 in
  let quit_loop = ref false in
  Random.self_init () ;
  
  while not !quit_loop do
    let r1' = Random.int 6 in
    let r2' = Random.int 6 in
    if r1' <> r2' && r1' <> 0 && r2' <> 0 then
      begin r1 := r1' ; r2 := r2' ; quit_loop := true ; end
  done ;
  (!r1, !r2)

(** keeping a global reference of the circuit file *)
let relation_file = ref ""
let witness_file = ref ""
let instance_file = ref ""

let state = ref Nil ;;

let circuit_ref = ref ((Z.zero, Z.zero, Z.zero, Z.zero), witness) ;;

let rec pad_witness' l i ws =
  if Z.equal i l then ws
  else pad_witness' l (Z.add i Z.one) (concat (Cons (Option.witness, Nil)) ws)
  
let pad_witness l ws = pad_witness' l Z.zero ws

(** produces the commitment json *)
let commitment_to_json ns cs =

  let c0 = oget (assoc cs !p1) in 
  let c1 = oget (assoc cs !p2) in 
  let c2 = oget (assoc cs !p3) in 
  let c3 = oget (assoc cs !p4) in 
  let c4 = oget (assoc cs !p5) in 
  
  `Assoc [("action", `String "commitment"); ("data", `List [`String c0; `String c1; `String c2; `String c3; `String c4]); ("ns", `Int (Z.to_int ns))]

let commitment_msg (x : unit) =

  Format.printf "Parsing relation, instance and witness files...@." ;
  let t0 = Sys.time () in
  let statement, witness = Jsonload.parse_files [!relation_file; !instance_file; !witness_file] in
  let t1 = Sys.time () in
  Format.printf "Relation, instance and witness parsed in %f ms.@." ((t1 -. t0) *. 1000.) ;

  let instance  = statement.instance
                  |> List.rev
                  |> List.fold_left (fun sofar a -> Cons(a,sofar)) Nil
  in
  let witness = witness
                |> List.rev
                |> List.fold_left (fun sofar a -> Cons(a,sofar)) Nil
  in
  let circuit = statement.relation in
  let header = statement.header in
  PrimeField.q := header.field_characteristic ;

  let (topo, gg) = circuit in
  circuit_ref := circuit ;
  let (np,ns,m,q) = topo in
  
  let witness = pad_witness np witness in
  let ns = Z.add ns np in
  let topo = (np,ns,m,q) in
  let circuit = (topo,gg) in

  Format.printf "Generating prover randomness...@." ;

  let t0 = Sys.time () in
  
  let rss = share_random_generator (Z.zero) ns in
  let r1 = (random_generator_gates gg, dpolynomial PC.t) in
  let r2 = (random_generator_gates gg, dpolynomial PC.t) in
  let r3 = (random_generator_gates gg, dpolynomial PC.t) in
  let r4 = (random_generator_gates gg, dpolynomial PC.t) in
  let r5 = (random_generator_gates gg, dpolynomial PC.t) in
  
  let r_mpc = Cons ((!p1, r1), Cons ((!p2, r2), Cons ((!p3, r3), Cons ((!p4, r4), Cons ((!p5, r5), Nil))))) in
  
  let r_cs1 = () in
  let r_cs2 = () in
  let r_cs3 = () in
  let r_cs4 = () in
  let r_cs5 = () in
  let r_cs = Cons ((!p1, r_cs1), Cons ((!p2, r_cs2), Cons ((!p3, r_cs3), Cons ((!p4, r_cs4), Cons ((!p5, r_cs5), Nil))))) in

  let t1 = Sys.time () in

  Format.printf "Randomness generated in %f ms@." ((t1 -. t0) *. 1000.) ;

  let module RELC = struct let relc = !circuit_ref end in
  let module ShamirBGWSha256InTheHeadData = ShamirBGWSha256InTheHeadData (RELC) in

  Format.printf "Producing commitment message...@." ;
  let t0 = Sys.time () in
  let (ps, cs) = ShamirBGWSha256InTheHeadData.commitment (rss, r_mpc, r_cs) (witness, instance) in
  let t1 = Sys.time () in
  Format.printf "Commitment message generated in %f ms@." ((t1 -. t0) *. 1000.) ;
  
  state := ps ;
  let commitment_msg = Yojson.to_string (commitment_to_json ns cs) in

  commitment_msg

let pinputs_to_json xp =
  let rec aux = function
    | Nil -> []
    | Cons (x, xs) -> `String (Z.to_string x) :: aux xs
  in
  `List (aux xp)
  
let input_to_json x =
  let (xp, xs) = x in
  `Assoc [("pinputs", pinputs_to_json xp); ("sinputs", pinputs_to_json xs)]

let monomial_to_json m =
  `Assoc [("coef", `String (Z.to_string m.coef)); ("expo", `String (Z.to_string m.expo))]
  
let rec polynomial_to_json = function
  | Nil -> []
  | Cons (m, ms) -> monomial_to_json m :: polynomial_to_json ms
  
let rand_to_json r =
  let (r_mpc, r_ref) = r in
  
  let gate_rand_to_json = function
    | BGWData.AdditionRand r -> `Assoc [("Add", `List [])]
    | BGWData.MultiplicationRand r -> `Assoc [("Mul", `List (polynomial_to_json r))]
    | BGWData.SMultiplicationRand r -> `Assoc [("SMul", `List [])]
  in
    
  let rec aux = function
    | Nil -> []
    | Cons (x, xs) ->
       let (gid, gr) = x in
       (`Assoc [("gid", `Int (Z.to_int gid)); ("r", gate_rand_to_json gr)]) :: aux xs
  in
  
  `Assoc [ ("r_mpc", `List (aux r_mpc)); ("r_ref", `List (polynomial_to_json r_ref)) ]

let rec shares_to_json = function
  | Nil -> []
  | Cons (x, xs) ->
     let (pid, sh) = x in
     (`Assoc [("pid", `Int (Z.to_int pid)) ; ("sh", `String (Z.to_string sh))]) :: shares_to_json xs

let rec addition_in_messages_to_json = function
  | Nil -> []
  | Cons (x, xs) ->
     let (pid, ims) = x in
     (`Assoc [("pid", `Int (Z.to_int pid)) ; ("msg", `Null)]) :: addition_in_messages_to_json xs

let rec multiplication_in_messages_to_json = function
  | Nil -> []
  | Cons (x, xs) ->
     let (pid, ims) = x in
     (`Assoc [("pid", `Int (Z.to_int pid)) ; ("msg", `String (Z.to_string ims))]) :: multiplication_in_messages_to_json xs

let rec smultiplication_in_messages_to_json = function
  | Nil -> []
  | Cons (x, xs) ->
     let (pid, ims) = x in
     (`Assoc [("pid", `Int (Z.to_int pid)) ; ("msg", `Null)]) :: smultiplication_in_messages_to_json xs
     
let rec in_messages_to_json = function
  | BGWData.PInputLT x -> `Assoc [("PInputLT", `String (Z.to_string x))]
  | SInputLT wid -> `Assoc [("SInputLT", `Int (Z.to_int wid))]
  | ConstantLT (gid, x) -> `Assoc [("ConstantLT", `Assoc [("gid", `Int (Z.to_int gid)); ("c", `String (Z.to_string x))])]
  | AdditionLT (gid, ims, lt, rt) ->
     `Assoc [("AdditionLT", `Assoc [("gid", `Int (Z.to_int gid)); ("ims", `List (addition_in_messages_to_json ims)) ; ("lt", in_messages_to_json lt) ; ("rt", in_messages_to_json rt)])]
  | MultiplicationLT (gid, ims, lt, rt) ->
     `Assoc [("MultiplicationLT", `Assoc [("gid", `Int (Z.to_int gid)); ("ims", `List (multiplication_in_messages_to_json ims)) ; ("lt", in_messages_to_json lt) ; ("rt", in_messages_to_json rt)])]
  | SMultiplicationLT (gid, ims, lt, rt) ->
     `Assoc [("SMultiplicationLT", `Assoc [("gid", `Int (Z.to_int gid)); ("ims", `List (smultiplication_in_messages_to_json ims)) ; ("lt", in_messages_to_json lt) ; ("rt", in_messages_to_json rt)])]
  
let trace_to_json t = 
  let (pouts, ims) = t in
  let (mpc_ims, ref_ims) = ims in
  `Assoc [ ("pouts", `List (shares_to_json pouts)) ; ("mpc_ims", in_messages_to_json mpc_ims) ; ("ref_ims", `List (multiplication_in_messages_to_json ref_ims)) ]
  
let view_to_json v =
  let (x, r, t) = v in
  `Assoc [ ("input", input_to_json x) ; ("rand", rand_to_json r); ("trace", trace_to_json t) ]
  
(** produces the response message *)
let response_msg ch =

  let (i, j) = ch in

  let module RELC = struct let relc = !circuit_ref end in
  let module ShamirBGWSha256InTheHeadData = ShamirBGWSha256InTheHeadData (RELC) in

  Format.printf "Producing response message...@." ;
  let t0 = Sys.time () in
  
  let (vi, cii) = oget (assoc !state i) in
  let (ci, osi) = cii in
  let (vj, cij) = oget (assoc !state j) in
  let (cj, osj) = cij in

  let vi_json = view_to_json vi in
  let vj_json = view_to_json vj in
  
  let resp_json = `Assoc [ ("action", `String "response"); ("data", `Assoc [("viewi", vi_json) ; ("viewj", vj_json)])] in

  let t1 = Sys.time () in
  Format.printf "Response message generated in %f ms@." ((t1 -. t0) *. 1000.) ;

  Yojson.to_string (resp_json)
  
let client_fun ic oc =
  let initial_json = `Assoc [("action", `String "ready")] in
  let pmsg = ref (Yojson.to_string initial_json) in
  try
    while true do  
      flush oc ;
      output_string oc (!pmsg^"\n") ;
      flush oc ;
      
      let vmsg = input_line ic in

      let json = Yojson.Basic.from_string vmsg in
      let open Yojson.Basic.Util in
      let action = json |> member "action" |> to_string in
      
      pmsg :=
        if (action = "start") then
          begin
            Format.printf "Generating commitment...@." ;
            let cmsg = commitment_msg () in
            Format.printf "Finished commitment generation@." ;
            cmsg
          end
        else
          if (action = "challenge") then
            begin
              Format.printf "Received challenge from verifier.@." ;
              Format.printf "Generating response...@." ;
              
              let data = json |> member "data" in
              let chl = Json_utils.json_to_list data in
              let i = Json_utils.json_to_int (List.nth chl 0) in
              let j = Json_utils.json_to_int (List.nth chl 1) in
              
              let rmsg = response_msg (Z.of_int i, Z.of_int j) in
              Format.printf "Finished response generation@." ;
              rmsg 
            end
          else
            if (action = "done") then
              begin
                Format.printf "Finalizing MitH protocol...@." ;
                Yojson.to_string (`Assoc [("action", `String "done")])
              end
            else "Bad query!" ;      
    done
  with 
    Exit -> exit 0
  | End_of_file -> exit 0
  | exn -> Unix.shutdown_connection ic ; raise exn  ;;

let main_client client_fun  =
  if Array.length Sys.argv < 6
  then Printf.printf "usage :  prover verifier_ip port relation_json instance_json witness_json\n"
  else let server = Sys.argv.(1) in
       let server_addr =
         try  Unix.inet_addr_of_string server 
         with Failure("inet_addr_of_string") -> 
           try  (Unix.gethostbyname server).Unix.h_addr_list.(0) 
           with Not_found ->
             Printf.eprintf "%s : Unknown server\n" server ;
             exit 2
       in try 
         let port = int_of_string (Sys.argv.(2)) in
         let sockaddr = Unix.ADDR_INET(server_addr,port) in

         Format.printf "Files:@." ;
         
         relation_file := Sys.argv.(3) ;
         instance_file := Sys.argv.(4) ;
         witness_file := Sys.argv.(5) ;

         Format.printf "\tRelation file: %s@." !relation_file ;
         Format.printf "\tInstance file: %s@." !instance_file ;
         Format.printf "\tRelation file: %s@." !witness_file ;
         
         let ic,oc = Unix.open_connection sockaddr
         in client_fun ic oc ;
            Unix.shutdown_connection ic
       with Failure("int_of_string") -> Printf.eprintf "bad port number";
                                        exit 2 ;;

let go_prover () = main_client client_fun ;;

go_prover ()
