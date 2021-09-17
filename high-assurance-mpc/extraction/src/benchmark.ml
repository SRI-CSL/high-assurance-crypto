open Option
open ECList
open FieldPolynomial
open PrimeField
open Utils

open BGWAddition
open BGWMultiplication
open BGWSMultiplication
open BGWRefresh
   
open Shamir

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

let benchmark_1 benchmark n =
  let nf = Z.to_float (Z.of_string n) in
  let rec median1 t1 = function
    | Nil -> t1 /. nf
    | Cons(a, s) -> median1 (t1 +. a) s
  in
  let b_n = ECList.init (Z.of_string n) (fun _ -> benchmark ()) in
  median1 0.0 b_n

let benchmark_2 benchmark n =
  let nf = Z.to_float (Z.of_string n) in
  let rec median2 t1 t2 = function
    | Nil -> (t1 /. nf, t2 /. nf)
    | Cons((a, b), s) -> median2 (t1 +. a) (t2 +. b) s
  in
  let b_n = ECList.init (Z.of_string n) (fun _ -> benchmark ()) in
  median2 0.0 0.0 b_n

let benchmark_3 benchmark n =
  let nf = Z.to_float (Z.of_string n) in
  let rec median3 t1 t2 t3 = function
    | Nil -> (t1 /. nf, t2 /. nf, t3 /. nf)
    | Cons((a, b, c), s) -> median3 (t1 +. a) (t2 +. b) (t3 +. c) s
  in
  let b_n = ECList.init (Z.of_string n) (fun _ -> benchmark ()) in
  median3 0.0 0.0 0.0 b_n

let n_ref = ref ""
let t_ref = ref ""
let r_ref = ref ""
let field_ref = ref ""
              
let options = [
    ("-field", Arg.Set_string field_ref, "Field size");
    ("-n", Arg.Set_string n_ref, "Number of parties");
    ("-t", Arg.Set_string t_ref, "Number of tolerated corrupt parties");
    ("-r", Arg.Set_string r_ref, "Number of benchmark repetitions")]
let usage_message = "./benchmark.native -field F -n N -t T -r R"
let args = ref []
         
let () =
  Arg.parse options (fun a->args := a::!args) usage_message;

  PrimeField.q := Z.of_string !field_ref ;

  let module PC = struct
      let n = Z.of_string !n_ref
      let t = Z.of_string !t_ref
      type pid_t = Z.t
      let pid_set = iota_ Z.one (Z.of_string !n_ref)
    end
  in

  let module Shamir = Shamir (PC) in
  let module BGWAdd = BGWAdditionGate (PC) in
  let module BGWMul = BGWMultiplicationGate (PC) in
  let module BGWSMul = BGWSMultiplicationGate (PC) in
  let module BGWRefresh = BGWRefreshGate (PC) in

  let benchmark_shamir () =
    let s = dt () in

    let t0 = Sys.time () in
    let r = dpolynomial (Z.of_string !t_ref) in
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
  in

  let benchmark_addition () =
    let s1 = dt () in
    let s2 = dt () in
    
    let r1 = dpolynomial (Z.of_string !t_ref) in
    let r2 = dpolynomial (Z.of_string !t_ref) in
    
    let ss1 = Shamir.share r1 s1 in
    let ss2 = Shamir.share r2 s2 in

    let rr = map (fun pid -> (pid, ())) PC.pid_set in
    let xx = map (fun pid -> (pid, ((), (oget (assoc ss1 pid), oget (assoc ss2 pid))))) PC.pid_set in
    
    let t0 = Sys.time () in
    let _ = BGWAdd.gate rr xx in
    let t1 = Sys.time () in
    
    (t1 -. t0) *. 1000.0
  in
  
  let benchmark_multiplication () =
    let s1 = dt () in
    let s2 = dt () in
    
    let r1 = dpolynomial (Z.of_string !t_ref) in
    let r2 = dpolynomial (Z.of_string !t_ref) in

    let ss1 = Shamir.share r1 s1 in
    let ss2 = Shamir.share r2 s2 in

    let t0 = Sys.time () in
    let rr = map (fun pid -> (pid, dpolynomial (Z.of_string !t_ref))) PC.pid_set in
    let t1 = Sys.time () in
    let tgen = (t1 -. t0) *. 1000.0 in

    let xx = map (fun pid -> (pid, ((), (oget (assoc ss1 pid), oget (assoc ss2 pid))))) PC.pid_set in

    let t0 = Sys.time () in
    let _ = BGWMul.gate rr xx in
    let t1 = Sys.time () in
    let tprot = (t1 -. t0) *. 1000.0 in
    
    (tgen, tprot)
  in
  
  let benchmark_smultiplication () =
    let s1 = dt () in
    let s2 = dt () in
    
    let r2 = dpolynomial (Z.of_string !t_ref) in
    
    let ss2 = Shamir.share r2 s2 in

    let rr = map (fun pid -> (pid, ())) PC.pid_set in
    let xx = map (fun pid -> (pid, (s1, (oget (assoc ss2 pid), witness)))) PC.pid_set in
    
    let t0 = Sys.time () in
    let _ = BGWSMul.gate rr xx in
    let t1 = Sys.time () in
    
    (t1 -. t0) *. 1000.0
  in

  let benchmark_refresh () =
    let s = dt () in
    
    let r = dpolynomial (Z.of_string !t_ref) in

    let ss = Shamir.share r s in

    let t0 = Sys.time () in
    let rr = map (fun pid -> (pid, dpolynomial (Z.of_string !t_ref))) PC.pid_set in
    let t1 = Sys.time () in
    let tgen = (t1 -. t0) *. 1000.0 in

    let xx = map (fun pid -> (pid, ((), (oget (assoc ss pid), witness)))) PC.pid_set in

    let t0 = Sys.time () in
    let _ = BGWRefresh.gate rr xx in
    let t1 = Sys.time () in
    let tprot = (t1 -. t0) *. 1000.0 in
    
    (tgen, tprot)
  in

  let (tg,ts,tr) = benchmark_3 benchmark_shamir !r_ref in
  Format.printf "Shamir benchmark result:\n\t- random generation: %f ms\n\t- share: %f ms\n\t- reconstruct: %f ms\n@." tg ts tr ;

  let tr = benchmark_1 benchmark_addition !r_ref in
  Format.printf "Addition benchmark result:\n\t- protocol execution: %f ms\n@." tr ;

  let (tg, tr) = benchmark_2 benchmark_multiplication !r_ref in
  Format.printf "Multiplication benchmark result:\n\t- random generation: %f ms\n\t- protocol execution: %f ms\n@." tg tr ;

  let tr = benchmark_1 benchmark_smultiplication !r_ref in
  Format.printf "Scalar multiplication benchmark result:\n\t- protocol execution: %f ms\n@." tr ;

  let (tg, tr) = benchmark_2 benchmark_refresh !r_ref in
  Format.printf "Refresh benchmark result:\n\t- random generation: %f ms\n\t- protocol execution: %f ms\n@." tg tr ;
