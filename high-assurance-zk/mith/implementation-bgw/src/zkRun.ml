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

CyclicGroup.p := (Z.of_string "0xFFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E462E36CE3BE39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA051015728E5A8AACAA68FFFFFFFFFFFFFFFF");;
CyclicGroup.g := (Z.of_string "2");;

Utils.p1 := (Z.of_string "1");;
Utils.p2 := (Z.of_string "2");;
Utils.p3 := (Z.of_string "3");;
Utils.p4 := (Z.of_string "4");;
Utils.p5 := (Z.of_string "5");;

let options = []
let description = ""
let args = ref []

let () =
  Arg.parse options (fun a->args := a::!args) description;

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
  let gg = Cons (gg, Nil) in
  let circuit = (topo,gg) in

  Format.printf "Circuit topology: #public inputs = %s | #secret inputs = %s | #output wires = %s | #gates = %s\n@." (Z.to_string np) (Z.to_string ns) (Z.to_string m) (Z.to_string q) ;

  
  Format.printf "Generating randomness...@." ;

  let t0 = Sys.time() in
  
  let rss = share_random_generator (Z.zero) ns in
  (*let r1 = random_generator gg in
  let r2 = random_generator gg in
  let r3 = random_generator gg in
  let r4 = random_generator gg in
  let r5 = random_generator gg in*)
  let r_mpc = random_generator gg in (*(r1,r2,r3,r4,r5) in*)
  (*let r_cs1 = commitment_random_generator (Z.zero) (Z.add n (Z.add m q)) in
  let r_cs2 = commitment_random_generator (Z.zero) (Z.add n (Z.add m q)) in
  let r_cs3 = commitment_random_generator (Z.zero) (Z.add n (Z.add m q)) in
  let r_cs4 = commitment_random_generator (Z.zero) (Z.add n (Z.add m q)) in
  let r_cs5 = commitment_random_generator (Z.zero) (Z.add n (Z.add m q)) in*)
  let r_cs1 = () in
  let r_cs2 = () in
  let r_cs3 = () in
  let r_cs4 = () in
  let r_cs5 = () in
  let r_cs = (r_cs1, r_cs2, r_cs3, r_cs4, r_cs5) in

  let t1 = Sys.time () in
  let trand = (t1 -. t0) *. 1000. in

  Format.printf "Randomness generated in %f milliseconds\n@." trand ;
  
  let (i,j) = verifier_randomness_generator in
  let pi = int_to_pid i in
  let pj = int_to_pid j in
  let r_v = (pi,pj) in

  Format.printf "Running MPC-in-the-Head protocol...@." ;

  let t0 = Sys.time() in
  
  let statement = (circuit, instance) in  

  let (_, y) = ShamirBGWSha256InTheHead.eval_protocol ((rss,r_mpc,r_cs), r_v) ((witness, statement), statement) in
  let (_,b) = y in

  let t1 = Sys.time () in
  let thead = (t1 -. t0) *. 1000. in

  Format.printf "MPC-in-the-Head protocol executed in %f milliseconds with output %s@." thead (if b then "TRUE" else "FALSE") ;
  Format.printf "Verifier choosed to see party %d and party %d\n\n@." i j ;

  Format.printf "Total time elapsed: %f milliseconds@." (trand +. thead)
