open Containers

open LPZK

module JSON = Yojson.Safe

exception BadJSON of string

let bad json s = raise (BadJSON(JSON.to_string json^" should be a "^s))

let json_to_string : JSON.t -> String.t = function
  | `String s -> s
  | json -> bad json "string"

let json_to_int : JSON.t -> int = function
  | `Int s -> s
  | json -> bad json "int"

let json_to_Z : JSON.t -> Z.t = function
  | `Int s -> Z.of_int s
  | `Intlit s -> Z.of_string s
  | json -> bad json "int"

let json_to_dico : JSON.t -> (String.t * JSON.t) List.t = function
  | `Assoc s -> s
  | json -> bad json "dictionary"

let json_to_list : JSON.t -> JSON.t List.t = function
  | `List s -> s
  | json -> bad json "list"

let json_to_array : JSON.t -> JSON.t Array.t = function
  | `List s -> Array.of_list s
  | json -> bad json "list"

let rec list_to_eclist : 'a List.t -> 'a LPZK.list = function
  | [] -> Nil
  | x :: xs -> Cons(x, list_to_eclist xs)

let z256 = Z.of_int 256

let utype_to_Z : JSON.t -> Z.t = function
  | `List l ->
     let aux sofar = function
       | `Int byte -> Z.((z256 * sofar) + Z.of_int byte)
       | `Intlit s -> Z.((z256 * sofar) + Z.of_string s)
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

let bad_header =
  let version = "" in
  let profile = "" in
  let field_characteristic = Z.zero in
  let field_degree = -1 in
  Header.{ version; profile; field_characteristic; field_degree }
  
module SH = CCHashtbl.Make(String)

let list_to_hash l =
  let result = SH.create 15 in
  List.iter (fun (s,json) -> SH.replace result s json) l;
  result

let json_to_header json =
  let dico = json |> json_to_dico |> list_to_hash in
  let version = SH.find dico "version" |> json_to_string in
  let profile = "" (*SH.find dico "profile" |> json_to_string*) in
  let field_characteristic = SH.find dico "field_characteristic" |> utype_to_Z in
  let field_degree = SH.find dico "field_degree" |> json_to_int in
  Header.{ version; profile; field_characteristic; field_degree }

module IH = CCHashtbl.Make(Z)

let ninputs = ref Z.zero

module WH = CCHashtbl.Make(Z)

let rec get_real_wire wire_index w curr =
  try
    let curr' = WH.find wire_index w in
    get_real_wire wire_index curr' curr'
  with Not_found -> curr

let output_wire = ref Z.zero

let count_nsinputs json =
  let gates = json |> json_to_list in

  let rec aux = function
    | [] -> 0 (*raise (BadJSON("I haven't seen the AssertZero gate in "^JSON.to_string json))*)
    | gate::next_gates ->

       match json_to_dico gate with

       | ["Witness", _w] -> 1 + aux next_gates
          
       | ["Instance", _w] -> aux next_gates
          
       | ["Copy", `List [_w_dest; _w_source]] -> aux next_gates
          
       | ["Constant", `List[_w; _u]] -> aux next_gates
                                    
       | ["Mul",`List[_output; _input1; _input2]] -> aux next_gates

       | ["MulConstant", `List[_output; _input1; _input2]] -> aux next_gates

       | ["Add",`List[_output; _input1; _input2]] -> aux next_gates

       | ["Free", _l] -> aux next_gates
                      
       | ["AssertZero", _output] -> aux next_gates
            
       | g
         -> raise (BadJSON ("Gate not supported "^ (fst (List.hd g))))
  in
  aux gates

let max_wire = ref Z.zero
  
let json_to_gates wire_index wire_gate_index inst_start wit_start gate_start json =
  let gates = json |> json_to_list in
  let output_wires = ref [] in

  let read id =
    (* print_endline("Getting node "^string_of_int id); *)
    try IH.find wire_gate_index id with Not_found -> SInput id (*Format.printf "not_found: id = %d@." id; exit 1*)
  in

  let witness_count  = ref wit_start in
  let instance_count = ref inst_start in
  let gate_count     = ref gate_start in
  let mul_count      = ref 0 in

  let rec aux = function
    | [] -> !output_wires
    (*raise (BadJSON("I haven't seen the AssertZero gate in "^JSON.to_string json))*)
    | gate::next_gates ->

       let write id c = (* print_endline("Registering node "^string_of_int id); *)
         IH.replace wire_gate_index id c;
         aux next_gates
       in
       match json_to_dico gate with

       | ["Witness", w] ->
          let c = !witness_count in
          let w = json_to_Z w in
          witness_count := Z.succ c;
          (*let w = Z.add (json_to_Z w) !ninputs in*)
          write w (read c)

       (*witness_count := !witness_count + 1 ;
          WH.replace wire_index (Z.of_int (!witness_count - 1)) (*(Z.add (json_to_Z w) !ninputs)*) (Z.of_int (!witness_count - 1)) ;
          aux next_gates *)
          
       | ["Instance", w] ->
          let c = !instance_count in
          let w = json_to_Z w in
          instance_count := Z.succ c;
          (*let w = Z.add (json_to_Z w) !ninputs in*)
          write w (PInput c)
          
       (*instance_count := !instance_count + 1 ;
          WH.replace wire_index (Z.of_int (!instance_count - 1)) (Z.add (json_to_Z w) !ninputs) ;
          aux next_gates*)
          
       | ["Copy", `List [w_dest; w_source]] ->
          let w_dest = json_to_Z w_dest in
          let w_source = json_to_Z w_source in
          write w_dest (read w_source)
       (*WH.replace wire_index (Z.add (json_to_Z w_dest) !ninputs) (Z.add (json_to_Z w_source) !ninputs) ;
          aux next_gates*)
          
       | ["Constant", `List[w; u]] ->
          let c = !gate_count in
          gate_count := Z.succ c;
          write (json_to_Z w) (Constant(c, utype_to_Z u))
          
       | ["Mul",`List[output; input1; input2]] ->
          (*let wl = get_real_wire wire_index (Z.add (json_to_Z input1) !ninputs) (Z.add (json_to_Z input1) !ninputs) in
          let wr = get_real_wire wire_index (Z.add (json_to_Z input2) !ninputs) (Z.add (json_to_Z input2) !ninputs) in*)
          let wl = json_to_Z input1 in
          let wr = json_to_Z input2 in
          let w  = json_to_Z output in
          let c  = !gate_count in
          gate_count := Z.succ c;
          mul_count  := !mul_count + 1;
          write w (Multiplication(c, read wl, read wr))

       | ["MulConstant", `List[output; input1; input2]]
         ->
          (*let wl = get_real_wire wire_index (Z.add (json_to_Z input1) !ninputs) (Z.add (json_to_Z input1) !ninputs) in
          let wr = get_real_wire wire_index (Z.add (json_to_Z input2) !ninputs) (Z.add (json_to_Z input2) !ninputs) in*)
          let wl = json_to_Z input1 in
          let wr = json_to_Z input2 in
          let w  = json_to_Z output in
          let c  = !gate_count in
          gate_count := Z.succ c;
          write w (Multiplication(c, read wl, read wr))
          
       (*write (Z.add (json_to_Z output) !ninputs) ArithmeticGates.(SMultiplication(Z.add (json_to_Z output) !ninputs, read (Z.add (json_to_Z input1) !ninputs), read (Z.add (json_to_Z input2) !ninputs)))*)

       | ["Add",`List[output; input1; input2]]
         ->
          (*let wl = get_real_wire wire_index (Z.add (json_to_Z input1) !ninputs) (Z.add (json_to_Z input1) !ninputs) in
          let wr = get_real_wire wire_index (Z.add (json_to_Z input2) !ninputs) (Z.add (json_to_Z input2) !ninputs) in*)
          let wl = json_to_Z input1 in
          let wr = json_to_Z input2 in
          let w  = json_to_Z output in
          let c  = !gate_count in
          gate_count := Z.succ c;
          write w (Addition(c, read wl, read wr))
       (*write (Z.add (json_to_Z output) !ninputs) ArithmeticGates.(Addition(Z.add (json_to_Z output) !ninputs, read (Z.add (json_to_Z input1) !ninputs), read (Z.add (json_to_Z input2) !ninputs)))*)

       | ["Free", _l] -> aux next_gates
                      
       | ["AssertZero", output]
(* -> let out = Z.of_int output in accu(ArithmeticCircuit.Output(Z.(out + one), out)) *)
         ->
          let w = json_to_Z output in
          output_wire  := !gate_count;
          output_wires := w :: !output_wires;
          gate_count   := Z.succ !gate_count;
          aux next_gates
          
       | g
         -> raise (BadJSON ("Gate not supported "^ (fst (List.hd g))))
  in

  let out_wires = aux gates in

  (*let rec wrap_up max_wire = function
    | [] -> assert (false)
    | ow :: [] -> read ow
    | ow0 :: ow1 :: [] -> (Addition(max_wire, read ow0, read ow1))
    | ow :: tl -> (Addition(max_wire, wrap_up (Z.sub max_wire Z.one) tl, read ow))
  in*)

  Z.sub !instance_count inst_start,
  Z.sub !witness_count wit_start,
  Z.add (Z.sub !gate_count gate_start) (Z.of_int (List.length out_wires)),
  !mul_count,
  (*wrap_up (Z.add !gate_count (Z.of_int (List.length out_wires))) out_wires*)
  List.map read out_wires
  
(*aux gates |> read*)

let json_to_relations previous_header json =
  match json |> json_to_list with
  | [dico] ->
     begin
       match json_to_dico dico with
       | ["header", header; "gate_mask", _mask ; "feat_mask", _fmask ; "functions", _fs ; "gates", gates]
         | ["gates", gates; "functions", _fs ; "feat_mask", _fmask ; "gate_mask", _mask ; "header", header]
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
  | [] -> bad_header, `List []
  | _ -> raise (BadJSON("This should be a singleton list for a relation1: "^JSON.to_string json))


(* let record_inputs wire_index inputs f i = *)
(*   let rec aux accu i = function *)
(*     | [] -> accu (Array.make 0 witness) *)
(*     | gate::next_gates -> *)
(*        IH.replace wire_index i (f i); *)
(*        aux (fun x -> accu (Array.append (Array.make 1 (utype_to_Z gate)) x)) (Z.succ i) next_gates *)
       
(*   (\*match json_to_list gate with *)
(*        | [(\*"id",`Int w;*\) (\*"value",*\) u] *)
(*          | [(\*"value",*\) u (\*; "id",`Int w*\)] (\*when w = i*\) *)
(*          -> *)
(*           (\* print_endline("Registering node "^string_of_int w); *\) *)
(*           IH.replace wire_index i (f (Z.of_int i)); *)
(*           aux (fun x -> accu((utype_to_Z u)::x)) (i+1) next_gates *)
(*        | u -> *)
(*           IH.replace wire_index i (f (Z.of_int i)); *)
(*           aux (fun x -> accu((utype_to_Z u)::x)) (i+1) next_gates *)
(*        | _ -> raise (BadJSON("Not a good input: "^JSON.to_string gate))*\) *)
       
(*   in *)
(*   inputs |> json_to_list |> aux (fun x -> x) i *)
  
let record_inputs wire_index inputs f i =
  inputs
  |> json_to_list
  |> List.fold_map (fun i gate -> IH.replace wire_index i (f i); Z.succ i, utype_to_Z gate) i
  |> snd
  |> list_to_eclist
  
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
  | [] -> (bad_header, `List [`Int (-1)])
  | _ -> raise (BadJSON("This should be a singleton list for a relation2: "^JSON.to_string json))

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
  | [] -> (bad_header, `List [`Int (-1)])
  | _ -> raise (BadJSON("This should be a singleton list for a relation3: "^JSON.to_string json))

  type statement = {
    header : Header.t;
    relation : topology_t * gates_t List.t;
    instance : Z.t LPZK.list }

type witness = Z.t LPZK.list

(* let rec number_of_gates = *)
(*   function *)
(*   | PInput _ -> 1 *)
(*   | SInput _ -> 1 *)
(*   | Constant _ -> 1 *)
(*   | Addition(_gid,l,r) -> 1 + number_of_gates l + number_of_gates r *)
(*   | Multiplication(_gid,l,r) -> 1 + number_of_gates l + number_of_gates r *)

(* let rec number_of_multiplications = *)
(*   function *)
(*   | PInput _ -> 0 *)
(*   | SInput _ -> 0 *)
(*   | Constant _ -> 0 *)
(*   | Addition(_,l,r) -> number_of_multiplications l + number_of_multiplications r *)
(*   | Multiplication(_,l,r) -> 1 + number_of_multiplications l + number_of_multiplications r *)

let get_wire =
  function
  | PInput output -> Z.to_string output
  | SInput output -> Z.to_string output
  | Constant (output,_c) -> Z.to_string output
  | Addition(output,_l,_r) -> Z.to_string output
  | Multiplication(output,_l,_r) -> Z.to_string output
                                 
let rec print_of_gates =
  function
  | PInput output -> Format.printf "PInput %s@." (Z.to_string output) ; 
  | SInput output -> Format.printf "SInput %s@." (Z.to_string output) ; 
  | Constant (output,_c) -> Format.printf "Constant %s@." (Z.to_string output) ; 
  | Addition(output,l,r) -> Format.printf "Addition [%s, %s, %s]@." (Z.to_string output) (get_wire l) (get_wire r) ; print_of_gates l ; print_of_gates r
  | Multiplication(output,l,r) -> Format.printf "Multiplication [%s, %s, %s]@." (Z.to_string output) (get_wire l) (get_wire r) ; print_of_gates l ; print_of_gates r

let is_empty_header header = Header.equal header bad_header

let timer_parsing = Timer.create "parsing"

let parse_files l =

  Timer.start timer_parsing;
  let jsons = List.rev_map JSON.from_file l in  
  Timer.stop timer_parsing;
  Format.printf "Time for core parsing is %f\n" (Timer.read timer_parsing *. 1000.);
  let wire_gate_index = IH.create 1000 in
  let wire_index = WH.create 1000 in

  let aux (header, relation, instance, witness) = function
    | "relations", json ->
       (*if Option.is_some relation
       then raise (BadJSON("The relation is already defined: "^JSON.to_string json));
       let header, relation = json_to_relations header json in
       Some header, Some relation, instance, witness*)
       let prev_relation = relation in
       let prev_header = header in
       let header, relation = json_to_relations header json in
       if is_empty_header header then prev_header, prev_relation, instance, witness
       else Some header, Some relation, instance, witness
       
    | "instances", json ->
       (*if Option.is_some instance && not (is_empty_instance (get instance))
       then raise (BadJSON("The instance is already defined: "^JSON.to_string json));
       let header, instance = json_to_instance header json in
       Format.printf "is_empty_instance = %s@." (if is_empty_instance instance then "TRUE" else "FALSE") ;
       if is_empty_instance instance then Some header, relation, None, witness
       else Some header, relation, Some instance, witness*)
       let prev_instance = instance in
       let prev_header = header in
       let header, instance = json_to_instance header json in
       if is_empty_header header then prev_header, relation, prev_instance, witness
       else Some header, relation, Some instance, witness
       
    | "witnesses", json ->
       (*if Option.is_some witness
       then raise (BadJSON("The witness is already defined: "^JSON.to_string json));
       let header, witness = json_to_witness header json in
       Format.printf "is_empty_witness = %s@." (if is_empty_witness witness then "TRUE" else "FALSE") ;
       if is_empty_witness witness then Some header, relation, instance, None
       else Some header, relation, instance, Some witness*)
       let prev_witness = witness in
       let prev_header = header in
       let header, witness = json_to_witness header json in
       if is_empty_header header then prev_header, relation, instance, prev_witness
       else Some header, relation, instance, Some witness
       
    | s,_ -> raise(BadJSON("The key should be relations, instances, or witnesses, but it's "^s))
  in
  let aux sofar json =
    let dico = json_to_dico json in
    List.fold_left aux sofar dico
  in
  match List.fold_left aux (None, None, None, None) jsons with
  | Some header, Some relation, Some instance, Some witness
    ->
     
     let f id = PInput id in
     let instance = record_inputs wire_gate_index instance f Z.zero in
     let instance_card = size instance in
     let f id = SInput id in
     let witness = record_inputs wire_gate_index witness f instance_card in
     let npinputs, nsinputs, ngates, nmul, circuit =
       json_to_gates
         wire_index
         wire_gate_index
         Z.zero
         instance_card
         (Z.add instance_card (size witness))
         relation
     in

     (* let muls = number_of_multiplications circuit in *)
     
     let topology = {
       npinputs = npinputs ;
       nsinputs = nsinputs ;
       noutputs = Z.one ;
       ngates = ngates }
     in
     
     let relation = topology, circuit in
     { header; relation; instance }, witness, nmul

  | Some header, Some relation, Some instance, None
    -> 
     let f id = PInput id in
     let instance = record_inputs wire_gate_index instance f Z.zero in
     let instance_card = size instance in
     let nsinputs = Z.of_int (count_nsinputs relation) in
     let npinputs, nsinputs, ngates, nmul, circuit =
       json_to_gates
         wire_index
         wire_gate_index
         Z.zero
         instance_card
         (Z.add instance_card nsinputs)
         relation
     in
     (* let muls = number_of_multiplications circuit in *)

     let topology = {
       npinputs = npinputs ;
       nsinputs = nsinputs ;
       noutputs = Z.one ;
       ngates = ngates }
     in
     
     let relation = topology, circuit in
     { header; relation; instance }, witness, nmul
  | _ -> raise(BadJSON "relation, instance, or witness is missing")
           

