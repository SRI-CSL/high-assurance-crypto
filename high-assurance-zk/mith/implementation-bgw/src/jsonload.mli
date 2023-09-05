module JSON = Yojson.Basic

exception BadJSON of string

val json_to_string : JSON.t -> String.t

val json_to_int : JSON.t -> int

val json_to_dico : JSON.t -> (String.t * JSON.t) List.t

val json_to_list : JSON.t -> JSON.t List.t

module Header : sig
  type t = {
      version : string;
      profile : string;
      field_characteristic : Z.t;
      field_degree : int;
    } [@@deriving eq, show]
end

type statement = {
    header : Header.t;
    relation : (Z.t * Z.t * Z.t * Z.t) * ArithmeticCircuit.ArithmeticGates.gates_t;
    instance : Z.t list }

type witness = Z.t list

val parse_files     : string list -> statement * witness
