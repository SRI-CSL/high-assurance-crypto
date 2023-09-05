module JSON = Yojson.Basic

exception BadJSON of string

module Header : sig
  type t = {
      version : string;
      profile : string;
      field_characteristic : Z.t;
      field_degree : int;
    } [@@deriving eq, show]
end

type maurer_statement = {
    header : Header.t;
    relation : (Z.t * Z.t * Z.t * Z.t) * NextMsgMaurerProtocol.MaurerCircuit.circuit;
    instance : Z.t list }

type witness = Z.t list

val parse_maurer_files     : string list -> maurer_statement * witness
