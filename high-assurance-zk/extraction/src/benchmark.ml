open Option
open ECList
open FieldPolynomial
open PrimeField
open Utils

open ASecretSharingScheme
open ASigmaProtocol
  
open Shamir
open BGWAddition
open BGWMultiplication
open BGWSMultiplication
open BGWRefresh
open ArithmeticProtocol
open ArithmeticCircuit
open ArithmeticGates
open BGWGate
open WeakPrivacyComposition
open BGW

open CRPRFCommitment

open InTheHead

open ShamirBGWSha256InTheHead
   
let rec gen_pids' i n acc =
  if Z.gt i n then acc
  else
    let pid = dt () in
    if Z.equal pid Z.zero || mem acc pid then
      gen_pids' i n acc
    else gen_pids' (Z.add i Z.one) n (Cons (pid, acc))

let gen_pids n = gen_pids' Z.zero n Nil
    
module PC = struct

  let n : Z.t = Z.of_string "5"
  let t : Z.t = Z.of_string "2"
              
  type pid_t = t
  let pid_set = gen_pids n
  
end

module Shamir = Shamir (PC)
module BGWAdd = BGWAdditionGate (PC)
module BGWMul = BGWMultiplicationGate (PC)
module BGWSMul = BGWSMultiplicationGate (PC)
module BGWRefresh = BGWRefreshGate (PC)
module BGWGate = BGWGateData (PC)
module BGW = BGWData (PC)

module ListShamir = ListSecretSharing (Shamir)

let rec dpolynomial' (i : Z.t) (d : Z.t) (p : monomial list) : monomial list =
  if Z.gt i d then p
  else
    let coef = dt () in
    if Z.equal coef Z.zero then dpolynomial' i d p
    else dpolynomial' (Z.add i Z.one) d (Cons ({ coef = coef ; expo = i}, p))
    
let dpolynomial : Z.t -> monomial list =
  fun n -> dpolynomial' Z.zero n Nil

let rec dpolynomial_list' d (ns : Z.t) acc : (monomial list) list =
  if Z.equal Z.zero ns then acc
  else dpolynomial_list' d (Z.sub ns Z.one) (Cons (dpolynomial d, acc))

let rec dpolynomial_list d (ns : Z.t) : (monomial list) list = dpolynomial_list' d ns Nil
    
let example_topology = (Z.of_string "1", Z.of_string "2", Z.of_string "1", Z.of_string "6")
                     
let example_gates = Addition (Z.of_string "8",
                                
                        (Addition (Z.of_string "6",
                           (Multiplication (Z.of_string "4",
                              (SInput (Z.of_string "1")),
                              (SInput (Z.of_string "1")))),
                           (Multiplication (Z.of_string "5",
                              (SInput (Z.of_string "2")),
                              (SInput (Z.of_string "2")))))),
                        
                        (SMultiplication (Z.of_string "7",
                           (PInput (Z.of_string "0")),
                           (Constant ((Z.of_string "3"), (Z.of_string "100"))))))
                  
let example_circuit = (example_topology, example_gates)
                    
let inst = Cons (Z.of_string "25", Nil)
let w = Cons (witness, Cons (Z.of_string "3", Cons (Z.of_string "4", Nil)))

module ShamirBGWSha256InTheHead' = ShamirBGWSha256InTheHead (PC) (struct let relc = example_circuit end)
module ShamirBGWSha256InTheHead = ZKSigmaProtocol (ShamirBGWSha256InTheHead')

let rec bgw_gate_party_rand_gen acc = function
  | PInput w -> acc
  | SInput w -> acc
  | Constant (gid, c) -> acc
  | Addition (gid, wl, wr) ->
     let rl = bgw_gate_party_rand_gen acc wl in
     let rr = bgw_gate_party_rand_gen rl wr in
     Cons ((gid, BGWGate.AdditionRand ()), rr)
     
  | Multiplication (gid, wl, wr) ->
     let rl = bgw_gate_party_rand_gen acc wl in
     let rr = bgw_gate_party_rand_gen rl wr in
     Cons ((gid, BGWGate.MultiplicationRand (dpolynomial PC.t)), rr)

  | SMultiplication (gid, wl, wr) ->
     let rl = bgw_gate_party_rand_gen acc wl in
     let rr = bgw_gate_party_rand_gen rl wr in
     Cons ((gid, BGWGate.SMultiplicationRand ()), rr)

let bgw_gate_rand_gen gg = map (fun pid -> (pid, bgw_gate_party_rand_gen Nil gg)) PC.pid_set

let bgw_rand_gen gg = map (fun pid -> (pid, (bgw_gate_party_rand_gen Nil gg, dpolynomial PC.t))) PC.pid_set

let verifier_randomness_generator =
  let r1 = ref Z.zero in
  let r2 = ref Z.zero in
  let quit_loop = ref false in
  Random.self_init () ;
  
  while not !quit_loop do
    let r1' = Random.int (Z.to_int PC.n) in
    let r2' = Random.int (Z.to_int PC.n) in
    if r1' <> r2' then
      begin r1 := nth witness PC.pid_set (Z.of_int r1') ;
            r2 := nth witness PC.pid_set (Z.of_int r2') ;
            quit_loop := true ;
      end
  done ;
  (!r1, !r2) ;;
     
let benchmark100_1 benchmark =
  let rec median tp = function
    | Nil -> tp /. 100.0
    | Cons(x, s) -> median (tp +. x) s
  in
  let b100 = ECList.init (Z.of_string "100") (fun _ -> benchmark ()) in
  median 0.0 b100
   
let benchmark100_2 benchmark =
  let rec median2 tp tpp = function
    | Nil -> (tp /. 100.0, tpp /. 100.0)
    | Cons((x,y), s) -> median2 (tp +. x) (tpp +. y) s
  in
  let b100 = ECList.init (Z.of_string "100") (fun _ -> benchmark ()) in
  median2 0.0 0.0 b100
  
let benchmark100_3 benchmark =
  let rec median3 tg ts tr = function
    | Nil -> (tg /. 100.0, ts /. 100.0, tr /. 100.0)
    | Cons((x,y,z), s) -> median3 (tg +. x) (ts +. y) (tr +. z) s
  in
  let b100 = ECList.init (Z.of_string "100") (fun _ -> benchmark ()) in
  median3 0.0 0.0 0.0 b100

let benchmark_shamir () =
  let s = Z.of_string "123456789" in
  
  let t0 = Sys.time () in
  let r = dpolynomial PC.t in
  let t1 = Sys.time () in
  let tgen = (t1 -. t0) *. 1000.0 in

  let t0 = Sys.time () in
  let ss = Shamir.share r s in
  let t1 = Sys.time () in
  let tshare = (t1 -. t0) *. 1000.0 in

  let t0 = Sys.time () in
  let sr = Shamir.reconstruct ss in
  let t1 = Sys.time () in
  let treconstruct = (t1 -. t0) *. 1000.0 in

  (*Printf.printf "Reconstructed secret = %s\n" (Z.to_string sr) ;*)
  
  (tgen, tshare, treconstruct)
  
let benchmark_bgw_add () =
  let s1 = Z.of_string "123456789" in
  let s2 = Z.of_string "1" in

  let r1 = dpolynomial PC.t in
  let r2 = dpolynomial PC.t in
  
  let ss1 = Shamir.share r1 s1 in
  let ss2 = Shamir.share r2 s2 in

  let rs = map (fun pid -> (pid, ())) PC.pid_set in
  let xs = map (fun pid -> (pid, ((), (oget (assoc ss1 pid), oget (assoc ss2 pid))))) PC.pid_set in
  
  let t0 = Sys.time () in
  let ss = BGWAdd.gate rs xs in
  let t1 = Sys.time () in

  let sr = Shamir.reconstruct (snd ss) in

  (*Printf.printf "Reconstructed secret = %s\n" (Z.to_string sr) ;*)
  (t1 -. t0) *. 1000.0

let benchmark_bgw_mul () =
  let s1 = Z.of_string "123456789" in
  let s2 = Z.of_string "2" in
  
  let r1 = dpolynomial PC.t in
  let r2 = dpolynomial PC.t in

  let ss1 = Shamir.share r1 s1 in
  let ss2 = Shamir.share r2 s2 in

  let t0 = Sys.time () in
  let rs = map (fun pid -> (pid, dpolynomial PC.t)) PC.pid_set in
  let t1 = Sys.time () in
  let tgen = (t1 -. t0) *. 1000.0 in
  
  let xs = map (fun pid -> (pid, ((), (oget (assoc ss1 pid), oget (assoc ss2 pid))))) PC.pid_set in
  
  let t0 = Sys.time () in
  let ss = BGWMul.gate rs xs in
  let t1 = Sys.time () in
  let tprot = (t1 -. t0) *. 1000.0 in
  
  let sr = Shamir.reconstruct (snd ss) in
  (*Printf.printf "Reconstructed secret = %s\n" (Z.to_string sr) ;*)

  (tgen, tprot)

let benchmark_bgw_smul () =
  let s1 = Z.of_string "123456789" in
  let s2 = Z.of_string "2" in

  (*let r1 = dpolynomial PC.t in*)
  let r2 = dpolynomial PC.t in
  
  let ss1 = Shamir.public_encoding s1 in
  let ss2 = Shamir.share r2 s2 in

  let rs = map (fun pid -> (pid, ())) PC.pid_set in
  let xs = map (fun pid -> (pid, ((oget (assoc ss1 pid)), (oget (assoc ss2 pid), witness)))) PC.pid_set in
  
  let t0 = Sys.time () in
  let ss = BGWSMul.gate rs xs in
  let t1 = Sys.time () in

  let sr = Shamir.reconstruct (snd ss) in

  (*Printf.printf "Reconstructed secret = %s\n" (Z.to_string sr) ;*)
  (t1 -. t0) *. 1000.0

let benchmark_bgw_refresh () =
  let s = Z.of_string "123456789" in

  (*let r1 = dpolynomial PC.t in*)
  let r = dpolynomial PC.t in
  
  let ss = Shamir.share r s in

  let t0 = Sys.time () in
  let rs = map (fun pid -> (pid, dpolynomial PC.t)) PC.pid_set in
  let t1 = Sys.time () in
  let tgen = (t1 -. t0) *. 1000.0 in

  let xs = map (fun pid -> (pid, ((), (oget (assoc ss pid), witness)))) PC.pid_set in
  
  let t0 = Sys.time () in
  let ss = BGWRefresh.gate rs xs in
  let t1 = Sys.time () in
  let tprot = (t1 -. t0) *. 1000.0 in

  let sr = Shamir.reconstruct (snd ss) in

  (*Printf.printf "Reconstructed secret = %s\n" (Z.to_string sr) ;*)
  (tgen, tprot)

let benchmark_bgw_gate () =

  let r = Cons (dpolynomial PC.t, Cons (dpolynomial PC.t, Nil)) in
  
  let ss = ListShamir.share r w in

  let t0 = Sys.time () in
  let rs = bgw_gate_rand_gen example_gates in
  let t1 = Sys.time () in
  let tgen = (t1 -. t0) *. 1000.0 in

  let rec dummy np acc =
    if Z.equal Z.zero np then acc
    else dummy (Z.sub np Z.one) (Cons (witness,acc))
  in
  let dummy_np = dummy (size inst) Nil in
  
  
  let x_mpc = map (fun pid -> (pid, (inst, concat dummy_np (oget (assoc ss pid))))) PC.pid_set in
    
  let t0 = Sys.time () in
  let ss = BGWGate.protocol example_circuit rs x_mpc in
  let t1 = Sys.time () in
  let tprot = (t1 -. t0) *. 1000.0 in

  let sr = Shamir.reconstruct (snd ss) in

  (*Printf.printf "Reconstructed secret = %s\n" (Z.to_string sr) ;*)
  (tgen, tprot)

let benchmark_bgw () =

  let r = Cons (dpolynomial PC.t, Cons (dpolynomial PC.t, Nil)) in
  
  let ss = ListShamir.share r w in

  let t0 = Sys.time () in
  let rs = bgw_rand_gen example_gates in
  let t1 = Sys.time () in
  let tgen = (t1 -. t0) *. 1000.0 in

  let rec dummy np acc =
    if Z.equal Z.zero np then acc
    else dummy (Z.sub np Z.one) (Cons (witness,acc))
  in
  let dummy_np = dummy (size inst) Nil in
  
  
  let x_mpc = map (fun pid -> (pid, (inst, concat dummy_np (oget (assoc ss pid))))) PC.pid_set in
    
  let t0 = Sys.time () in
  let ss = BGW.protocol example_circuit rs x_mpc in
  let t1 = Sys.time () in
  let tprot = (t1 -. t0) *. 1000.0 in

  let sr = Shamir.reconstruct (snd ss) in

  (*Printf.printf "Reconstructed secret = %s\n" (Z.to_string sr) ;*)
  (tgen, tprot)

let benchmark_mith () =

  let t0 = Sys.time () in
  let rss = dpolynomial_list PC.t PC.n in
  let rmpc = bgw_rand_gen example_gates in
  let rcs = map (fun pid -> (pid, ())) PC.pid_set in
  let t1 = Sys.time () in
  let tgen = (t1 -. t0) *. 1000.0 in

  let (i,j) = verifier_randomness_generator in
  
  let t0 = Sys.time () in
  let (_,b) = ShamirBGWSha256InTheHead.protocol ((rss, rmpc, rcs), (i,j)) ((w,inst), inst) in
  let t1 = Sys.time () in
  let tprot = (t1 -. t0) *. 1000.0 in

  (*Printf.printf "MITH output = %s\n" (if snd b then "TRUE" else "FALSE") ;*)
  (tgen, tprot)
  
let _ =

  Format.printf "Running benchmarks for N = %s parties and T = %s\n\n@." (Z.to_string PC.n) (Z.to_string PC.t) ;
  
  let (tg,ts,tr) = benchmark100_3 benchmark_shamir in
  Format.printf "Shamir benchmark result:\n\t- random generation: %f\n\t- share: %f\n\t- reconstruct: %f\n\n@." tg ts tr ;

  let tr = benchmark100_1 benchmark_bgw_add in
  Format.printf "Addition benchmark result:\n\t- random generation: NA\n\t- gate: %f\n\n@." tr ;

  let (tg, tr) = benchmark100_2 benchmark_bgw_mul in
  Format.printf "Multiplication benchmark result:\n\t- random generation: %f\n\t- gate: %f\n\n@." tg tr ;

  let tr = benchmark100_1 benchmark_bgw_smul in
  Format.printf "SMultiplication benchmark result:\n\t- random generation: NA\n\t- gate: %f\n\n@." tr ;
  
  let (tg, tr) = benchmark100_2 benchmark_bgw_refresh in
  Format.printf "Refresh benchmark result:\n\t- random generation: %f\n\t- gate: %f\n\n@." tg tr ;

  let (tg, tr) = benchmark100_2 benchmark_bgw_gate in
  Format.printf "BGW gate benchmark result:\n\t- random generation: %f\n\t- protocol: %f\n\n@." tg tr ;

  let (tg, tr) = benchmark100_2 benchmark_bgw in
  Format.printf "BGW benchmark result:\n\t- random generation: %f\n\t- protocol: %f\n\n@." tg tr ;

  let (tg, tr) = benchmark100_2 benchmark_mith in
  Format.printf "MTIH benchmark result:\n\t- random generation: %f\n\t- protocol: %f\n\n@." tg tr 
