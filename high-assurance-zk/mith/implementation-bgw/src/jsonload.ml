open Containers

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
       | `String s -> Z.((z256 * sofar) + Z.of_string s)
       | json -> bad json "int (utype)"
     in
     l |> List.rev |> List.fold_left aux Z.zero
  | json -> bad json "list (utype)"

module Header = struct

  type z = Z.t [@@deriving eq]
  let pp_z = Z.pp_print

  type t = {
      version : string;
      profile : string;
      field_characteristic : z;
      field_degree : int
    } [@@deriving eq, show]
end
              
module SH = CCHashtbl.Make(String)

let list_to_hash l =
  let result = SH.create 15 in
  List.iter (fun (s,json) -> SH.replace result s json) l;
  result

let json_to_header json =
  let dico = json |> json_to_dico |> list_to_hash in
  let version = SH.find dico "version" |> json_to_string in
  let profile = SH.find dico "profile" |> json_to_string in
  let field_characteristic = SH.find dico "field_characteristic" |> utype_to_Z in
  let field_degree = SH.find dico "field_degree" |> json_to_int in
  Header.{ version; profile; field_characteristic; field_degree }

module IH = CCHashtbl.Make(Int)

let json_to_gates wire_index json =
  let gates = json |> json_to_list in

  let read id =
    (* print_endline("Getting node "^string_of_int id); *)
    try IH.find wire_index id with Not_found -> ArithmeticCircuit.ArithmeticGates.SInput (Z.of_int id) (*Format.printf "not_found: id = %d@." id; exit 1*)
  in

  let rec aux = function
    | [] -> raise (BadJSON("I haven't seen the AssertZero gate in "^JSON.to_string json))
    | gate::next_gates ->

       let write id c = (* print_endline("Registering node "^string_of_int id); *)
         IH.replace wire_index id c;
         aux next_gates
       in
       let open ArithmeticCircuit in
       match json_to_dico gate with

       | ["Constant",`List[`Int w; u]]
         -> write w ArithmeticGates.(Constant(Z.of_int w, utype_to_Z u))

       | ["Mul",`List[`Int output; `Int input1; `Int input2]]
         ->
          write output
            ArithmeticGates.(Multiplication(Z.of_int output, read input1, read input2))

       | ["SMul", `List[`Int output; `Int input1; `Int input2]]
         -> write output
              ArithmeticGates.(SMultiplication(Z.of_int output, read input1, read input2))

       | ["Add",`List[`Int output; `Int input1; `Int input2]]
         ->
          write output
            ArithmeticGates.(Addition(Z.of_int output, read input1, read input2))

       | ["AssertZero",`Int output]
(* -> let out = Z.of_int output in accu(ArithmeticCircuit.Output(Z.(out + one), out)) *)
         -> output
       | _ 
         -> raise (BadJSON "Gate not supported")
  in
  aux gates |> read

let json_to_relations previous_header json =
  match json |> json_to_list with
  | [dico] ->
     begin
       match json_to_dico dico with
       | ["header", header; "gates", gates]
         | ["gates", gates; "header", header]
         ->
          begin
            let header = json_to_header header in
            match previous_header with
            | Some previous_header when not(Header.equal header previous_header)
              ->  raise (BadJSON("The header doesn't match the previous one"))
            | _ -> header, gates
          end
       | _ -> raise (BadJSON("This should be a dictionary for header and gates: "^JSON.to_string json))
     end

  | _ -> raise (BadJSON("This should be a singleton list for a relation: "^JSON.to_string json))


let record_inputs wire_index inputs f i =
  let rec aux accu i = function
    | [] -> accu []
    | gate::next_gates ->
       match json_to_dico gate with
       | ["id",`Int w; "value", u]
         | ["value", u; "id",`Int w] when w = i
         ->
          (* print_endline("Registering node "^string_of_int w); *)
          IH.replace wire_index w (f(Z.of_int w));
          aux (fun x -> accu((utype_to_Z u)::x)) (i+1) next_gates
       | _ -> raise (BadJSON("Not a good input: "^JSON.to_string gate))
            
  in
  inputs |> json_to_list |> aux (fun x -> x) i
  
let json_to_inputs previous_header header =
  let header = json_to_header header in
  match previous_header with
  | Some previous_header when not(Header.equal header previous_header)
    ->  raise (BadJSON("The header doesn't match the previous one"))
  | _ -> header

let json_to_instance previous_header json =
  match json |> json_to_list with
  | [dico] ->
     begin
       match json_to_dico dico with
       | ["header", header; "common_inputs", inputs]
         | ["common_inputs", inputs; "header", header]
         -> json_to_inputs previous_header header, inputs
       | _ -> raise (BadJSON("This should be a dictionary for header and common_inputs: "^JSON.to_string json))
     end
  | _ -> raise (BadJSON("This should be a singleton list for a relation: "^JSON.to_string json))

let json_to_witness previous_header json =
  match json |> json_to_list with
  | [dico] ->
     begin
       match json_to_dico dico with
       | ["header", header; "short_witness", inputs]
         | ["short_witness", inputs; "header", header]
         -> json_to_inputs previous_header header, inputs
       | _ -> raise (BadJSON("This should be a dictionary for header and short_witness: "^JSON.to_string json))
     end
  | _ -> raise (BadJSON("This should be a singleton list for a relation: "^JSON.to_string json))

type statement = {
    header : Header.t;
    relation : (Z.t * Z.t * Z.t * Z.t) * ArithmeticCircuit.ArithmeticGates.gates_t;
    instance : Z.t list }

type witness = Z.t list

let rec number_of_gates =
  let open ArithmeticCircuit.ArithmeticGates in
  function
  | PInput _ -> 1
  | SInput _ -> 1
  | Constant _ -> 1
  | Addition(_,l,r) -> number_of_gates l + number_of_gates r
  | Multiplication(_,l,r) -> number_of_gates l + number_of_gates r
  | SMultiplication(_,l,r) -> number_of_gates l + number_of_gates r

let rec number_of_multiplications =
  let open ArithmeticCircuit.ArithmeticGates in
  function
  | PInput _ -> 0
  | SInput _ -> 0
  | Constant _ -> 0
  | Addition(_,l,r) -> number_of_multiplications l + number_of_multiplications r
  | Multiplication(_,l,r) -> 1 + number_of_multiplications l + number_of_multiplications r
  | SMultiplication(_,l,r) -> number_of_multiplications l + number_of_multiplications r

let rec print_of_gates =
  let open ArithmeticCircuit.ArithmeticGates in
  function
  | PInput output -> Format.printf "PInput gate with gid = %s@." (Z.to_string output) ; 
  | SInput output -> Format.printf "Addition gate with gid = %s@." (Z.to_string output) ; 
  | Constant (output,c) -> Format.printf "Addition gate with gid = %s@." (Z.to_string output) ; 
  | Addition(output,l,r) -> Format.printf "Addition gate with gid = %s@." (Z.to_string output) ; print_of_gates l ; print_of_gates r
  | Multiplication(output,l,r) -> Format.printf "Multiplication gate with gid = %s@." (Z.to_string output) ; print_of_gates l ; print_of_gates r
  | SMultiplication(output,l,r) -> Format.printf "Scalar multiplication gate with gid = %s@." (Z.to_string output) ; print_of_gates l ; print_of_gates r

let parse_files l =
  
  let jsons = List.rev_map JSON.from_file l in  
  let wire_index = IH.create 1000 in

  let aux (header, relation, instance, witness) = function
    | "relations", json ->
       if Option.is_some relation
       then raise (BadJSON("The relation is already defined: "^JSON.to_string json));
       let header, relation = json_to_relations header json in
       Some header, Some relation, instance, witness
    | "instances", json ->
       if Option.is_some instance
       then raise (BadJSON("The instance is already defined: "^JSON.to_string json));
       let header, instance = json_to_instance header json in
       Some header, relation, Some instance, witness
    | "witnesses", json ->
       if Option.is_some witness
       then raise (BadJSON("The witness is already defined: "^JSON.to_string json));
       let header, witness = json_to_witness header json in
       Some header, relation, instance, Some witness
    | s,_ -> raise(BadJSON("The key should be relations, instances, or witnesses, but it's "^s))
  in
  let aux sofar json =
    let dico = json_to_dico json in
    List.fold_left aux sofar dico
  in
  match List.fold_left aux (None, None, None, None) jsons with
  | Some header, Some relation, Some instance, Some witness
    ->
     
     let f id = ArithmeticCircuit.ArithmeticGates.PInput id in
     let instance = record_inputs wire_index instance f 0 in
     let instance_card = List.length instance in
     let f id = ArithmeticCircuit.ArithmeticGates.SInput id in
     let witness = record_inputs wire_index witness f instance_card in
     let circuit = json_to_gates wire_index relation in
     (* let muls = number_of_multiplications circuit in *)

     let topology =
       instance_card |> Z.of_int,
       List.length witness |> Z.of_int,
       Z.one,
       number_of_gates circuit |> Z.of_int
     in
     
     let relation = topology, circuit in
     { header; relation; instance }, witness
  | Some header, Some relation, Some instance, None
    ->     
     let f id = ArithmeticCircuit.ArithmeticGates.PInput id in
     let instance = record_inputs wire_index instance f 0 in
     let instance_card = List.length instance in
     let circuit = json_to_gates wire_index relation in
     (* let muls = number_of_multiplications circuit in *)

     let topology =
       instance_card |> Z.of_int,
       Z.zero,
       Z.one,
       number_of_gates circuit |> Z.of_int
     in
     
     let relation = topology, circuit in
     { header; relation; instance }, []
  | _ -> raise(BadJSON "relation, instance, or witness is missing")
           
