open Containers

open NextMsgMaurerProtocol

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

let json_to_maurer_gates json =
  let gates = json |> json_to_list in

  let rec aux = function
    | [] -> raise (BadJSON("I haven't seen the AssertZero gate in "^JSON.to_string json))
    | gate::next_gates ->

       let open NextMsgMaurerProtocol in
       let open ECList in
       match json_to_dico gate with

       | ["Constant",`List[`Int w; u]]
         -> Cons(MaurerGate.Const ( Z.of_int w ,  (Z.to_int (utype_to_Z u), 0, 0, 0)),
            aux next_gates)

       | ["Mul",`List[`Int output; `Int input1; `Int input2]]
         -> Cons(MaurerGate.Mul ( Z.of_int output ,  ( Z.of_int input1,  Z.of_int input2 ) ),
            aux next_gates)

       | ["SMul", `List[`Int output; `Int input1; `Int input2]]
         -> Cons(MaurerGate.SMul (  Z.of_int output ,  ( Z.of_int input1, Z.of_int input2 ) ),
            aux next_gates)

       | ["Add",`List[`Int output; `Int input1; `Int input2]]
         ->  Cons(MaurerGate.Add (  Z.of_int output , ( Z.of_int input1, Z.of_int input2 ) ),
            aux next_gates)

       | ["AssertZero",`Int output]
         -> Nil
       | _ 
         -> raise (BadJSON "Gate not supported")
  in
  aux gates

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


let record_inputs inputs i =
  let rec aux accu i = function
    | [] -> accu []
    | gate::next_gates ->
       match json_to_dico gate with
       | ["id",`Int w; "value", u]
         | ["value", u; "id",`Int w] when w = i
         ->
          (* print_endline("Registering node "^string_of_int w); *)
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

type maurer_statement = {
    header : Header.t;
    relation : (Z.t * Z.t * Z.t * Z.t) * MaurerCircuit.circuit;
    instance : Z.t list }

type witness = Z.t list

let number_of_maurer_gates = let open ECList in fun x -> Z.to_int (size x)

let parse_maurer_files l =
  let jsons = List.rev_map JSON.from_file l in
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
     let instance = record_inputs instance 0 in
     let instance_card = List.length instance in
     let witness = record_inputs witness instance_card in
     let circuit = json_to_maurer_gates relation in
     Format.printf "Maurer GATES %d\n@." (number_of_maurer_gates circuit);
     let topology =
       instance_card |> Z.of_int,
       List.length witness |> Z.of_int,
       Z.one,
       number_of_maurer_gates circuit |> Z.of_int
     in
     let relation = topology, circuit in
     { header; relation; instance }, witness
     | _ -> raise(BadJSON "relation, instance, or witness is missing")
    
