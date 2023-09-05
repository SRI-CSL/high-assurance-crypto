module JSON = Yojson.Basic

exception BadJSON of string

let bad json s = raise (BadJSON(JSON.to_string json^" should be a "^s))

let json_to_string : JSON.t -> String.t = function
  | `String s -> s
  | json -> bad json "string"

let json_to_int : JSON.t -> int = function
  | `Int s -> s
  | json -> bad json "int"

let json_to_dico : JSON.t -> (String.t * JSON.t) List.t = function
  | `Assoc s -> s
  | json -> bad json "dictionary"

let json_to_list : JSON.t -> JSON.t List.t = function
  | `List s -> s
  | json -> bad json "list"

let z256 = Z.of_int 256

let utype_to_Z : JSON.t -> Z.t = function
  | `List l ->
     let aux sofar = function
       | `Int byte -> Z.((z256 * sofar) + Z.of_int byte)
       | `String byte -> Z.((z256 * sofar) + Z.of_string byte)
       | json -> bad json "int (utype)"
     in
     l |> List.rev |> List.fold_left aux Z.zero
  | json -> bad json "list (utype)"

let read_file file =

  let ic = open_in file in

  let s = ref "" in
  let c = ref (input_char ic) in
  try
    while true do
      c := (input_char ic) ;
      if (!c = '\n') then s := !s ^ Char.escaped ' '
      else s := !s ^ Char.escaped !c
    done ;
    close_in ic ; !s
  with End_of_file -> close_in ic ; !s

let rec index' x i = function
  | [] -> -1
  | x' :: xs -> if x = x' then i else index' x (i+1) xs

let myindex x xs = index' x 0 xs
                 
let options = []
let usage_message = "./benchmark.native <json input> N"
let args = ref []

let () =
  Arg.parse options (fun a->args := a::!args) usage_message;

  if List.length !args < 2 then
    begin Format.eprintf "Wrong number of arguments!\n\n%s@." usage_message; exit 1 end
  else
    let open JSON.Util in

    let file = List.hd (List.rev !args) in
    let n = List.hd !args in
    
    let json = JSON.from_file file in

    let relations = json |> member "relations" |> json_to_list in
    let header = List.nth relations 0 in
    let field_z = header |> member "header" |> member "field_characteristic" |> utype_to_Z in
    
    if Z.equal field_z (Z.of_int 2) then
      begin
        Format.printf "Running benchmarks for Maurer boolean backend...@." ;
        let prover_exec = Sys.command ("./benchmark_boolean.native " ^ file ^ " " ^ n) in
        exit prover_exec
      end
    else
      if Z.equal field_z (Z.sub (Z.pow (Z.of_int 2) 255) (Z.of_int 19)) then
        begin
          Format.printf "Running benchmarks for Maurer 25519 backend...@." ;
          let prover_exec = Sys.command ("./benchmark_25519.native " ^ file ^ " " ^ n) in
          exit prover_exec
        end
      else
        if Z.lt field_z (Z.of_int64 Int64.max_int) then
          begin
            Format.printf "Running benchmarks for Maurer small modulus backend...@." ;
            let prover_exec = Sys.command ("./benchmark_small_modulus.native " ^ file ^ " " ^ n) in
            exit prover_exec
          end
        else
          begin
            Format.printf "Field size not supported. Use BGW MitH based implementation instead@." 
          end
