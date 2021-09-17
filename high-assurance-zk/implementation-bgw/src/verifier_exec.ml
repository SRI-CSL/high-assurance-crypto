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

(** 
    the following three references allow us to avoid having to reload the circuit in
    order to build the Maurer protocol MitH OCaml module
 *)
(** keeping a reference to the circuit gates *)
let gg_ref = ref witness
(** keeping a reference to the number of public inputs *)
let npinputs_ref = ref Z.zero
(** keeping a reference to the number of secret inputs *)
let nsinputs_ref = ref Z.zero
(** keeping a reference to the number of inputs *)
let ninputs_ref = ref Z.zero
(** keeping a reference to the number of gates *)
let ngates_ref = ref Z.zero
(** keeping a reference to the instance *)
let instance_ref = ref Nil

let dpolynomial (d : Z.t) : monomial list =
  let poly = ref Nil in
  
  for i = 0 to Z.to_int d - 1 do
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

let circuit_ref = ref ((Z.zero, Z.zero, Z.zero, Z.zero), witness) ;;

let rec pad_witness' l i ws =
  if Z.equal i l then ws
  else pad_witness' l (Z.add i Z.one) (concat (Cons (Option.witness, Nil)) ws)
  
let pad_witness l ws = pad_witness' l Z.zero ws

let challenge_to_json chl =
  let (i,j) = chl in
  `Assoc [("action", `String "challenge"); ("data", `List [`Int (Z.to_int i); `Int (Z.to_int j)])]

let parse_commitment_msg comm_msg =
  let rec aux i = function
    | [] -> Nil
    | x :: xs -> Cons ((Z.of_int i, Jsonload.json_to_string x), aux (i+1) xs)
  in
  aux 1 (Jsonload.json_to_list comm_msg)

let chl_ref = ref (Z.zero, Z.zero);;
  
let vs_ref = ref (Nil, Nil, (Z.zero, Z.zero)) ;;
  
let challenge_msg ns cs =

  nsinputs_ref := Z.add (Z.of_int ns) !nsinputs_ref ;

  circuit_ref := ((!npinputs_ref, !nsinputs_ref, Z.one, !ngates_ref), !gg_ref) ;
  
  let cs = parse_commitment_msg cs in
  
  let module RELC = struct let relc = !circuit_ref end in
  let module ShamirBGWSha256InTheHeadData = ShamirBGWSha256InTheHeadData (RELC) in

  Format.printf "Producing challenge message...@." ;
  let t0 = Sys.time () in
  let (i,j) = verifier_randomness_generator in
  let t1 = Sys.time () in
  Format.printf "Challenge message generated in %f ms.@." ((t1 -. t0) *. 1000.) ;
  
  let r_v = (Z.of_int i, Z.of_int j) in
  
  let (vs, chl) = ShamirBGWSha256InTheHeadData.challenge r_v !instance_ref cs in
  chl_ref := chl ;
  vs_ref := vs ;

  Yojson.to_string (challenge_to_json chl)

let json_to_pinputs xp =
  let rec aux = function
    | [] -> Nil
    | x :: xs -> Cons (Z.of_string (Jsonload.json_to_string x), aux xs)
  in
  aux (Jsonload.json_to_list xp)
  
let json_to_input x =
  let open Yojson.Basic.Util in
  let pinputs = x |> member "pinputs" in
  let sinputs = x |> member "sinputs" in
  (json_to_pinputs pinputs, json_to_pinputs sinputs)

let json_to_monomial m =
  let open Yojson.Basic.Util in
  let coef = m |> member "coef" |> Jsonload.json_to_string in
  let expo = m |> member "expo" |> Jsonload.json_to_string in
  { coef = Z.of_string coef ; expo = Z.of_string expo }
  
let rec json_to_polynomial = function
  | [] -> Nil
  | m :: ms -> Cons (json_to_monomial m, json_to_polynomial ms)
  
let json_to_rand r =
  let open Yojson.Basic.Util in
  let r_mpc = r |> member "r_mpc" |> Jsonload.json_to_list in
  let r_ref = r |> member "r_ref" |> Jsonload.json_to_list in
  
  let json_to_gate_rand obj =
    match keys obj with
    | ["Add"] -> BGWData.AdditionRand ()
    | ["Mul"] -> BGWData.MultiplicationRand (obj |> member "Mul" |> Jsonload.json_to_list |> json_to_polynomial)
    | ["SMul"] -> BGWData.SMultiplicationRand ()
  in

  let rec aux = function
    | [] -> Nil
    | x :: xs ->
       let gid = x |> member "gid" |> Jsonload.json_to_int in
       let r = x |> member "r" in
       Cons ((Z.of_int gid, json_to_gate_rand r), aux xs)
  in

  (aux r_mpc, json_to_polynomial r_ref)

let rec json_to_shares = function
  | [] -> Nil
  | x :: xs ->
     let open Yojson.Basic.Util in
     let pid = x |> member "pid" |> Jsonload.json_to_int in
     let sh = x |> member "sh" |> Jsonload.json_to_string in
     Cons ((Z.of_int pid, Z.of_string sh), json_to_shares xs)

let rec json_to_addition_in_messages = function
  | [] -> Nil
  | x :: xs ->
     let open Yojson.Basic.Util in
     let pid = x |> member "pid" |> Jsonload.json_to_int in
     Cons ((Z.of_int pid, ()), json_to_addition_in_messages xs)
     
let rec json_to_multiplication_in_messages = function
  | [] -> Nil
  | x :: xs ->
     let open Yojson.Basic.Util in
     let pid = x |> member "pid" |> Jsonload.json_to_int in
     let ims = x |> member "msg" |> Jsonload.json_to_string in
     Cons ((Z.of_int pid, Z.of_string ims), json_to_multiplication_in_messages xs)

let rec json_to_smultiplication_in_messages = function
  | [] -> Nil
  | x :: xs ->
     let open Yojson.Basic.Util in
     let pid = x |> member "pid" |> Jsonload.json_to_int in
     Cons ((Z.of_int pid, ()), json_to_smultiplication_in_messages xs)

let rec json_to_in_messages = function
  | [("PInputLT", json)] -> BGWData.PInputLT (Z.of_string (Jsonload.json_to_string json))
  | [("SInputLT", json)] -> BGWData.SInputLT (Z.of_int (Jsonload.json_to_int json))
  | [("ConstantLT", json)] ->
     let open Yojson.Basic.Util in
     let gid = json |> member "gid" |> Jsonload.json_to_int in
     let c = json |> member "c" |> Jsonload.json_to_string in
     BGWData.ConstantLT (Z.of_int gid, Z.of_string c)
  | [("AdditionLT", json)] ->
     let open Yojson.Basic.Util in
     let gid = json |> member "gid" |> Jsonload.json_to_int in
     let ims = json |> member "ims" |> Jsonload.json_to_list in
     let lt = json |> member "lt" in
     let rt = json |> member "rt" in
     BGWData.AdditionLT (Z.of_int gid, json_to_addition_in_messages ims, json_to_in_messages (Jsonload.json_to_dico lt), json_to_in_messages (Jsonload.json_to_dico rt))
  | [("MultiplicationLT", json)] ->
     let open Yojson.Basic.Util in
     let gid = json |> member "gid" |> Jsonload.json_to_int in
     let ims = json |> member "ims" |> Jsonload.json_to_list in
     let lt = json |> member "lt" in
     let rt = json |> member "rt" in
     BGWData.MultiplicationLT (Z.of_int gid, json_to_multiplication_in_messages ims, json_to_in_messages (Jsonload.json_to_dico lt), json_to_in_messages (Jsonload.json_to_dico rt))
  | [("SMultiplicationLT", json)] ->
     let open Yojson.Basic.Util in
     let gid = json |> member "gid" |> Jsonload.json_to_int in
     let ims = json |> member "ims" |> Jsonload.json_to_list in
     let lt = json |> member "lt" in
     let rt = json |> member "rt" in
     BGWData.SMultiplicationLT (Z.of_int gid, json_to_smultiplication_in_messages ims, json_to_in_messages (Jsonload.json_to_dico lt), json_to_in_messages (Jsonload.json_to_dico rt))
  | _ -> assert (false)
        
let json_to_trace t =
  let open Yojson.Basic.Util in
  let pouts = t |> member "pouts" |> Jsonload.json_to_list in
  let mpc_ims = t |> member "mpc_ims" |> Jsonload.json_to_dico in
  let ref_ims = t |> member "ref_ims" |> Jsonload.json_to_list in
  (json_to_shares pouts, (json_to_in_messages mpc_ims, json_to_multiplication_in_messages ref_ims))

let json_to_view v =
  let open Yojson.Basic.Util in
  let x = v |> member "input" in
  let r = v |> member "rand" in
  let t = v |> member "trace" in

  (json_to_input x, json_to_rand r, json_to_trace t)

let decide resp_msg =
  let open Yojson.Basic.Util in

  Format.printf "Parsing response message...@." ;
  let t0 = Sys.time () in

  let viewi = resp_msg |> member "viewi" in
  let viewj = resp_msg |> member "viewj" in
  
  let module RELC = struct let relc = !circuit_ref end in
  let module ShamirBGWSha256InTheHeadData = ShamirBGWSha256InTheHeadData (RELC) in

  let resp = ((json_to_view viewi, ()), (json_to_view viewj, ())) in
  let t1 = Sys.time () in
  Format.printf "Response message parsed in %f ms.@." ((t1 -. t0) *. 1000.) ;

  Format.printf "Checking proof...@." ;
  let t0 = Sys.time () in

  let final = ShamirBGWSha256InTheHeadData.check !vs_ref resp in
  
  let t1 = Sys.time () in
  
  Format.printf "Proof checked in %f ms.@." ((t1 -. t0) *. 1000.) ;
  Format.printf "Decision = %s@." (if final then "TRUE" else "FALSE")

let get_my_addr () =
  (Unix.gethostbyname(Unix.gethostname())).Unix.h_addr_list.(0) ;;

let handle_service ic oc =
  try while true do

        let pmsg = input_line ic in

        let json = Yojson.Basic.from_string pmsg in
        let open Yojson.Basic.Util in
        let action = json |> member "action" |> to_string in
        
        let vmsg =
          if (action = "ready") then
            begin
              Format.printf "Notifying the prover that I am ready...@." ;
              Yojson.to_string (`Assoc [("action", `String "start")])
            end
          else
            if (action = "commitment") then
              begin
                Format.printf "Received commitment from prover.@." ;
                Format.printf "Generating challenge...@." ;
          
                let data = json |> member "data" in
                let ns = json |> member "ns" |> Jsonload.json_to_int in
                let chmsg = challenge_msg ns data in
                
                Format.printf "Finished challenge generation@." ;
                chmsg
              end
            else
              if (action = "response") then
                begin
                  Format.printf "Received response from prover.@." ;
                  Format.printf "Generating final decision...@." ;
                  let data = json |> member "data" in
                  decide data ;
                  Yojson.to_string (`Assoc [("action", `String "done")])
                end
              else
                if (action = "done") then raise Sys.Break
                else
                  begin Format.eprintf "Bad query!" ; Unix.shutdown_connection ic ; exit 2 end ;
        in
        
        output_string oc (vmsg^"\n") ; flush oc

      done ;
  with
  | Sys.Break -> raise Sys.Break
  | _ ->
     begin
       Printf.printf "End of text\n" ;
       let _ = Sys.sigint in
       flush stdout ; Unix.shutdown (Unix.descr_of_in_channel ic) Unix.SHUTDOWN_ALL ; Unix.shutdown (Unix.descr_of_out_channel oc) Unix.SHUTDOWN_ALL ; exit 1 
     end

let establish_server server_fun sockaddr =
  let domain = Unix.domain_of_sockaddr sockaddr in
  let sock = Unix.socket domain Unix.SOCK_STREAM 0 
  in Unix.bind sock sockaddr ;
     Unix.listen sock 3;
     let (s, caller) = Unix.accept sock 
     in match Unix.fork() with
          0 -> if Unix.fork() <> 0 then exit 0 ; 
               let inchan = Unix.in_channel_of_descr s 
               and outchan = Unix.out_channel_of_descr s 
               in server_fun inchan outchan ;
                  close_in inchan ;
                  close_out outchan ;
                  Unix.close s ;
                  exit 0
          | id -> Unix.close s; ignore(Unix.waitpid [] id)
    
       
let main_server serv_fun =
  if Array.length Sys.argv < 4 then Printf.eprintf "usage : verifier port relation_json instance_json\n"
  else try
      let port = int_of_string Sys.argv.(1) in
      
      relation_file := Sys.argv.(2) ;
      instance_file := Sys.argv.(3) ;

      Format.printf "Files:@." ;
      Format.printf "\tRelation file: %s@." !relation_file ;
      Format.printf "\tInstance file: %s@." !instance_file ;

      Format.printf "Parsing relation, instance files...@." ;
      let t0 = Sys.time () in
      
      let statement, witness = Jsonload.parse_files [!relation_file; !instance_file] in

      let t1 = Sys.time () in
      Format.printf "Relation, instance and witness parsed in %f ms.@." ((t1 -. t0) *. 1000.) ;
      
      let instance  = statement.instance
                      |> List.rev
                      |> List.fold_left (fun sofar a -> Cons(a,sofar)) Nil
      in

      let circuit = statement.relation in
      let header = statement.header in
      PrimeField.q := header.field_characteristic ;

      let t1 = Sys.time () in
      let tparse = (t1 -. t0) *. 1000. in
      
      let (topo, gg) = circuit in
      circuit_ref := circuit ;
      let (np,ns,m,q) = topo in
      
      npinputs_ref := np ;
      nsinputs_ref := ns ;
      ngates_ref := q ;

      gg_ref := gg ;

      instance_ref := instance ;

      Format.printf "Waiting for the prover boot...@." ;
            
      let my_address = Unix.inet_addr_loopback in
      establish_server serv_fun (Unix.ADDR_INET(my_address, port)) 
    with
    | Sys.Break ->
       Unix.kill (Unix.getpid ()) Sys.sigkill ; 
       Unix.kill (Unix.getpid ()) Sys.sigquit ; 
       
    (*Unix.kill (Unix.getpid ()) 0 ; (Format.printf "i am here@." ; exit 0)*)
       
    | Failure("int_of_string") -> 
       Printf.eprintf "serv_up : bad port number\n"
    | Not_found -> Printf.eprintf "what?\n"


let go_verifier () = 
  Unix.handle_unix_error main_server handle_service ;;

go_verifier ()
