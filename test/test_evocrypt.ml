open Format

open EVOCrypt
open EcLib
open EcList

let error_occurred = ref false

let test test_name answer correct_answer =
  flush stdout;
  flush stderr;
  if answer <> correct_answer then begin
    eprintf "*** Bad result (%s)@." test_name;
    flush stderr;
    error_occurred := true
  end else begin
    printf " %s...@." test_name
  end

let rec pad_witness' l i ws =
  if Z.equal i l then ws
  else pad_witness' l (Z.add i Z.one) (concat (Cons (EcOption.witness, Nil)) ws)
  
let pad_witness l ws = pad_witness' l Z.zero ws

(* =========================================================================== *)
(** Arithmetic circuit tests *)

open EVOCrypt.Circuit.ArithmeticCircuit 
open ArithmeticGates

let default_gates = Multiplication (Z.of_string "8", 
                                    Addition (Z.of_string "7",
                                      Addition (Z.of_string "6", PInput (Z.of_string "0"), SInput (Z.of_string "2")),
                                      Multiplication (Z.of_string "5", 
                                        Constant (Z.of_string "4", Z.of_string "2"),
                                        SInput (Z.of_string "3"))),
                                    PInput (Z.of_string "1"))
let default_topology = (Z.of_string "2", Z.of_string "2", Z.of_string "1", Z.of_string "5")
let default_circuit = (default_topology, default_gates)

let _ = 
  let xp = Cons(Z.of_string "1", Cons(Z.of_string "2", Nil)) in
  let xs = Cons(Z.of_string "3", Cons(Z.of_string "4", Nil)) in
  let answer = ArithmeticCircuit.eval_circuit default_circuit xp (pad_witness (Z.of_string "2") xs) in
  test "Circuit evaluation test" answer (Z.of_string "16")
(* =========================================================================== *)

(* =========================================================================== *)
(** Commitment test *)
open EVOCrypt.Commitment.SHA3Commitment

let _ = 
  let msg = "The quick brown fox jumps over the lazy dog" in
  let answer = SHA3Commitment.verify msg (SHA3Commitment.commit () msg) in
  test "SHA3 commitment test (TRUE)" answer true ;
  let answer = SHA3Commitment.verify msg (SHA3Commitment.commit () "") in
  test "SHA3 commitment test (FALSE)" answer false
(* =========================================================================== *)

(* =========================================================================== *)
(** Secret sharing test *)
open EVOCrypt.SecretSharing.Shamir
open Zarith.FieldPolynomial

let p1 = Z.of_string "1"
let p2 = Z.of_string "2"
let p3 = Z.of_string "3"
let p4 = Z.of_string "4"
let p5 = Z.of_string "5"

let pid_mpc_set : Z.t list = Cons (p1, Cons (p2, Cons (p3, Cons (p4, Cons (p5, Nil)))))

module PC5 = struct
  let n = Z.of_string "5"
  let t = Z.of_string "2"
  type pid_t = Z.t
  let pid_set : pid_t list = pid_mpc_set
end 

let rec shares_to_string = function
  | Nil -> ""
  | Cons(x, Nil) -> let (pid, s) = x in Z.to_string pid ^ " -> " ^ Z.to_string s
  | Cons(x, xs) -> let (pid, s) = x in Z.to_string pid ^ " -> " ^ Z.to_string s ^ "\n" ^ shares_to_string xs

let _ = 
  let module Shamir5 = Shamir (PC5) in
  EcPrimeField.q := Z.of_string "11" ;
  let p = Cons({ coef = Z.of_string "5" ; expo = Z.of_string "1"}, Cons({ coef = Z.of_string "7"; expo = Z.zero}, Nil)) in
  let s = Z.of_string "4" in
  let answer = Shamir5.share p s in
  test "Shamir test share" answer (Cons((p1, Z.of_string "9"), Cons((p2, Z.of_string "3"), Cons((p3, Z.of_string "8"), Cons((p4, Z.of_string "2"), Cons((p5, Z.of_string "7"), Nil)))))) ;
  let answer = Shamir5.reconstruct answer in
  test "Shamir test reconstruct (all shares)" answer s ;
  let answer = Shamir5.reconstruct (Cons((p1, Z.of_string "9"), Cons((p2, Z.of_string "3"), Cons((p3, Z.of_string "8"), Nil)))) in
  test "Shamir test reconstruct (subset of shares)" answer s
(* =========================================================================== *)

(** End of tests *)
let _ =
  print_newline();
  if !error_occurred then begin
    printf "********* TEST FAILED ***********\n";
    exit 2 
  end else begin
    printf "All tests successful.\n";
    exit 0
  end