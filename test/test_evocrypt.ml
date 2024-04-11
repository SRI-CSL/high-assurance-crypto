open Format

open EVOCrypt
open EcLib
open EcList

let error_occurred = ref false

let test test_name answer correct_answer =
  flush stdout;
  flush stderr;
  if answer <> correct_answer then begin
    eprintf "*** Bad result (%s)\n" test_name;
    flush stderr;
    error_occurred := true
  end else begin
    printf " %s..." test_name
  end

let rec pad_witness' l i ws =
  if Z.equal i l then ws
  else pad_witness' l (Z.add i Z.one) (concat (Cons (EcOption.witness, Nil)) ws)
  
let pad_witness l ws = pad_witness' l Z.zero ws

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