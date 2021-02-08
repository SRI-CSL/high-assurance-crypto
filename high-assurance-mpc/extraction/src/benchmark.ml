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
open Shamir
open CRPRFCommitment

module Sha256 = struct 

  type input_t = string
  type output_t = string
  type key_t = unit

  let f (k : key_t) (x : input_t) : output_t = 
    let sha256 = Cryptokit.Hash.sha256 () in
    sha256#add_string x;
    String.sub (sha256#result) 0 16

   end
                 
module Com = CRPRFCommitment (Sha256)
open Com
           
open ArithmeticProtocol

module BGWData = ArithmeticProtocolData(ShamirData)(BGWAdditionData)(BGWMultiplicationData)(BGWSMultiplicationData)
open BGW

open ShamirBGWSha256InTheHead

let rec dpolynomial' (i : Z.t) (d : Z.t) (p : monomial list) : monomial list =
  if Z.gt i d then p
  else
    let coef = dt () in
    if Z.equal coef Z.zero then dpolynomial' i d p
    else dpolynomial' (Z.add i Z.one) d (Cons ({ coef = coef ; expo = i}, p))
    
let dpolynomial : Z.t -> monomial list =
  fun n -> dpolynomial' Z.zero n Nil

let rec random_generator_gates (g : ArithmeticGates.gates_t) =
  match g with
  | PInput _ -> Nil
  | SInput _ -> Nil
  | Constant _ -> Nil
  | Addition (gid, wl, wr) -> 
    concat (concat (random_generator_gates wl) (Cons ((gid, BGWData.AdditionRands ((),(),(),(),())), Nil))) (random_generator_gates wr)
  | Multiplication (gid, wl, wr) -> 
    concat (concat (random_generator_gates wl) (Cons ((gid, BGWData.MultiplicationRands (dpolynomial (Z.of_string "2"), dpolynomial (Z.of_string "2"), dpolynomial (Z.of_string "2"), dpolynomial (Z.of_string "2"), dpolynomial (Z.of_string "2"))), Nil))) (random_generator_gates wr)
  | SMultiplication (gid, wl, wr) -> 
    concat (concat (random_generator_gates wl) (Cons ((gid, BGWData.SMultiplicationRands ((),(),(),(),())), Nil))) (random_generator_gates wr)

let rec random_generator = function
  | Nil -> Nil
  | Cons (g,gs) -> concat (random_generator_gates g) (random_generator gs)
                  
let rec commitment_random_generator i n =
  if Z.equal i n then Nil
  else Cons ((), commitment_random_generator (Z.add i Z.one) n)

let rec share_random_generator i n =
  if Z.equal i n then Nil
  else
    let r = dpolynomial (Z.of_string "2") in
    Cons (r, share_random_generator (Z.add i Z.one) n)

let int_to_pid x =
  if x = 1 then P1
  else if x = 2 then P2
  else if x = 3 then P3
  else if x = 4 then P4
  else P5

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
  (!r1, !r2) ;;

let benchmark100 benchmark =
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
  let r = dpolynomial (Z.of_string "2") in
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
  (tgen, tshare, treconstruct)

let benchmark_addition () =
  let s1 = dt () in
  let s2 = dt () in

  let r1 = dpolynomial (Z.of_string "2") in
  let r2 = dpolynomial (Z.of_string "2") in

  let (s1_1, s1_2, s1_3, s1_4, s1_5) = Shamir.share r1 s1 in
  let (s2_1, s2_2, s2_3, s2_4, s2_5) = Shamir.share r2 s2 in
  
  let t0 = Sys.time () in
  let ss = BGWAdditionGate.eval_gate ((),(),(),(),()) ((s1_1, s1_2, s1_3, s1_4, s1_5), (s2_1, s2_2, s2_3, s2_4, s2_5)) in
  let t1 = Sys.time () in

  let sr = Shamir.reconstruct (snd ss) in
  (t1 -. t0) *. 1000.0
  
let benchmark_multiplication () =
  let s1 = dt () in
  let s2 = dt () in

  let r1 = dpolynomial (Z.of_string "2") in
  let r2 = dpolynomial (Z.of_string "2") in

  let (s1_1, s1_2, s1_3, s1_4, s1_5) = Shamir.share r1 s1 in
  let (s2_1, s2_2, s2_3, s2_4, s2_5) = Shamir.share r2 s2 in

  let t0 = Sys.time () in
  let r1 = dpolynomial (Z.of_string "2") in
  let r2 = dpolynomial (Z.of_string "2") in
  let r3 = dpolynomial (Z.of_string "2") in
  let r4 = dpolynomial (Z.of_string "2") in
  let r5 = dpolynomial (Z.of_string "2") in
  let t1 = Sys.time () in
  let tgen = (t1 -. t0) *. 1000.0 in
  
  let t0 = Sys.time () in
  let ss = BGWMultiplicationGate.eval_gate (r1,r2,r3,r4,r5) ((s1_1, s1_2, s1_3, s1_4, s1_5), (s2_1, s2_2, s2_3, s2_4, s2_5)) in
  let t1 = Sys.time () in
  let tprot = (t1 -. t0) *. 1000.0 in
  
  let sr = Shamir.reconstruct (snd ss) in

  (tgen, tprot)

let benchmark_scalar_multiplication () =
  let s1 = dt () in
  let s2 = dt () in

  let r = dpolynomial (Z.of_string "2") in

  let (s2_1, s2_2, s2_3, s2_4, s2_5) = Shamir.share r s2 in
  
  let t0 = Sys.time () in
  let ss = BGWSMultiplicationGate.eval_gate ((),(),(),(),()) ((s1,s1,s1,s1,s1),(s2_1, s2_2, s2_3, s2_4, s2_5)) in
  let t1 = Sys.time () in

  let sr = Shamir.reconstruct (snd ss) in
  (t1 -. t0) *. 1000.0

let benchmark_hash_commitment () =

  let s1 = dt () in
  
  let t0 = Sys.time () in
  let (c,ok) = Com.commit () (Z.to_string s1) in
  let t1 = Sys.time () in
  let tcom = (t1 -. t0) *. 1000.0 in

  let t0 = Sys.time () in
  let b = Com.verify (Z.to_string s1) (c,ok) in
  let t1 = Sys.time () in
  let tver = (t1 -. t0) *. 1000.0 in
  
  (tcom, tver)

(*let benchmark_pedersen () =
  let s = dt () in

  let t0 = Sys.time () in
  let r = dt () in
  let t1 = Sys.time () in
  let tgen = (t1 -. t0) *. 1000.0 in
  
  let t0 = Sys.time () in
  let (c,ok) = Pedersen.cs_commit r s in
  let t1 = Sys.time () in
  let tcom = (t1 -. t0) *. 1000.0 in

  let t0 = Sys.time () in
  let b = Pedersen.cs_verify s (c,ok) in
  let t1 = Sys.time () in
  let tver = (t1 -. t0) *. 1000.0 in
  
  (tgen, tcom, tver)*)

let _ =

  let (tg,ts,tr) = benchmark100_3 benchmark_shamir in
  Printf.printf "Shamir benchmark result:\n\t- random generation: %f\n\t- share: %f\n\t- reconstruct: %f\n\n" tg ts tr ;

  let tr = benchmark100 benchmark_addition in
  Printf.printf "Addition benchmark result:\n\t- protocol execution: %f\n\n" tr ;

  let (tg, tr) = benchmark100_2 benchmark_multiplication in
  Printf.printf "Multiplication benchmark result:\n\t- random generation: %f\n\t- protocol execution: %f\n\n" tg tr ;

  let tr = benchmark100 benchmark_scalar_multiplication in
  Printf.printf "Scalar multiplication benchmark result:\n\t- protocol execution: %f\n\n" tr ;

  let (tc, tv) = benchmark100_2 benchmark_hash_commitment in
  Printf.printf "Hash-based commitment benchmark result:\n\t- commit execution: %f\n\t- verify execution: %f\n" tc tv
