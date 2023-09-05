open ECList
open Core
open Option

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
