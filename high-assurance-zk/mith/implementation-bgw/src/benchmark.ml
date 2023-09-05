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

open ShamirBGWSha256InTheHeadBenchmark

open InTheHeadBenchmark

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

module ShamirBGWSha256InTheHead = ShamirBGWSha256InTheHeadData (PC)
               
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

let benchmark_8 benchmark n =
  let nf = Z.to_float (Z.of_string n) in
  let rec median8 t1 t2 t3 t4 t5 t6 t7 t8 = function
    | Nil -> (t1 /. nf, t2 /. nf, t3 /. nf, t4 /. nf, t5 /. nf, t6 /. nf, t7 /. nf, t8 /. nf)
    | Cons((a,b,c,d,e,f,g,h), s) -> median8 (t1 +. a) (t2 +. b) (t3 +. c) (t4 +. d) (t5 +. e) (t6 +. f) (t7 +. g) (t8 +. h) s
  in
  let b_n = ECList.init (Z.of_string n) (fun _ -> benchmark ()) in
  median8 0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0 b_n

let rec pad_witness' l i ws =
  if Z.equal i l then ws
  else pad_witness' l (Z.add i Z.one) (concat (Cons (Option.witness, Nil)) ws)
  
let pad_witness l ws = pad_witness' l Z.zero ws

let options = []
let usage_message = "benchmark <json input1> n"
let args = ref []

let commitment_to_json cs =

  let c0 = oget (assoc cs !p1) in 
  let c1 = oget (assoc cs !p2) in 
  let c2 = oget (assoc cs !p3) in 
  let c3 = oget (assoc cs !p4) in 
  let c4 = oget (assoc cs !p5) in 

  Format.printf "c0 = %s@." c0 ;
  
  `Assoc [("action", `String "commitment"); ("data", `List [`String c0; `String c1; `String c2; `String c3; `String c4])]

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
  `Assoc [("coef", `String (Z.to_string m.coef)); ("expo", `Int (Z.to_int m.expo))]
  
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

let response_bandwidth = ref 0
  
let () =
  Arg.parse options (fun a->args := a::!args) usage_message;
  
  let n = List.hd !args in
  args := List.tl !args ;

  Format.printf "Loading the relation, witness and instance from file...@." ;

  let t0 = Sys.time () in
  
  let statement, witness = Jsonload.parse_files (List.rev !args) in


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

  let t1 = Sys.time () in
  let tparse = (t1 -. t0) *. 1000. in

  Format.printf "File parsed and loaded in %f milliseconds\n@." tparse ;

  let rec share_list_to_string = function
    | Nil -> ""
    | Cons (x, Nil) -> Z.to_string x
    | Cons (x, xs) -> Z.to_string x ^ ", " ^ share_list_to_string xs
  in

  Format.printf "Parsed instance: %s\nParsed witness: %s\n\n@." (share_list_to_string instance) (share_list_to_string witness) ;

  let (topo, gg) = circuit in
  let (np,ns,m,q) = topo in
  
  let witness = pad_witness np witness in
  let ns = Z.add ns np in
  let topo = (np,ns,m,q) in
  let circuit = (topo,gg) in

  Format.printf "Circuit topology: #public inputs = %s | #secret inputs = %s | #output wires = %s | #gates = %s\n@." (Z.to_string np) (Z.to_string ns) (Z.to_string m) (Z.to_string q) ;
  
  let benchmark () =
  
    let t0 = Sys.time() in
    
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
    let prand_time = (t1 -. t0) *. 1000. in

    let t0 = Sys.time() in
    let (i,j) = verifier_randomness_generator in
    let t1 = Sys.time () in
    let vrand_time = (t1 -. t0) *. 1000. in

    let pi = int_to_pid i in
    let pj = int_to_pid j in
    let r_v = (pi,pj) in
    
    (*Format.printf "Randomness generated in %f milliseconds\n@." trand ;
    
    Format.printf "Running MPC-in-the-Head protocol...@." ;*)

    let module RELC = struct let relc = circuit end in
    let module ShamirBGWSha256InTheHead = ShamirBGWSha256InTheHead (RELC) in

    let (ps, cs) = ShamirBGWSha256InTheHead.commitment (rss, r_mpc, r_cs) (witness, instance) in
    let (vs, chl) = ShamirBGWSha256InTheHead.challenge r_v instance cs in
    let resp = ShamirBGWSha256InTheHead.response ps chl in

    let (vi,vj) = resp in
    response_bandwidth := String.length (String.concat "" [Yojson.to_string (view_to_json (fst vi)); Yojson.to_string (view_to_json (fst vj))]) ;
    
    let final = ShamirBGWSha256InTheHead.check vs resp in
    
    (*let (_, y) = ShamirBGWSha256InTheHead.protocol ((rss,r_mpc,r_cs), r_v) ((witness, instance), instance) in
    let (_,b) = y in*)

    (*Format.printf "MPC-in-the-Head protocol executed in %f milliseconds with output %s@." (trand +. !commit_time +. !challenge_time +. !response_time +. !check_time) (if b then "TRUE" else "FALSE") ;
    Format.printf "Verifier choosed to see party %d and party %d\n\n@." i j ;*)
    
    (prand_time, vrand_time, !mpc_time, !pcommit_time, !challenge_time, !response_time, !vcommit_time, !check_time)
  in

  Format.printf "Running benchmarks for MitH instantiated with BGW with N = %s and T = %s\n\n@." (Z.to_string PC.n) (Z.to_string PC.t) ;
  
  let (prand_time, vrand_time, mpc_time, pcommit_time, challenge_time, response_time, vcommit_time, check_time) = benchmark_8 benchmark n in
  Format.printf "MitH benchmark result:\n\tProver:\n\t\tCommitment phase:\n\t\t\tRandom generation: %f ms\n\t\t\tMPC protocol: %f ms\n\t\t\tCommit: %f ms\n\t\t\tTotal: %f ms\n\t\tResponse: %f ms\n\n\tVerifier:\n\t\tRandom generation: %f ms\n\t\tChallenge: %f ms\n\t\tDecision phase:\n\t\t\tCommit: %f ms\n\t\t\tCheck: %f ms\n\t\t\tTotal: %f ms\n\n\tProver total time: %f ms\n\tVerifier total time: %f ms\n\tProtocol time: %f ms\n\nBandwidth:\n\tCommitment: 160 B\n\tReponse: %d B@." prand_time mpc_time pcommit_time (prand_time +. mpc_time +. pcommit_time) response_time vrand_time challenge_time vcommit_time check_time (vcommit_time +. check_time) (prand_time +. mpc_time +. pcommit_time +. response_time) (vrand_time +. challenge_time +. vcommit_time +. check_time) (prand_time +. mpc_time +. pcommit_time +. response_time +. vrand_time +. challenge_time +. vcommit_time +. check_time) (!response_bandwidth)

(*  Format.printf "MPC-in-the-Head protocol executed in %f milliseconds with output %s@." thead (if b then "TRUE" else "FALSE") ;
  Format.printf "Verifier choosed to see party %d and party %d\n\n@." i j ;

  Format.printf "Total time elapsed: %f milliseconds@." (trand +. thead)*)
