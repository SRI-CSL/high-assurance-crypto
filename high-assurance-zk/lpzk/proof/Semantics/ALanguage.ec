(**
  Abstract syntax definition for a *language*.

  A language is comprised by a set of instructions - **L** -, and tolerates both public and secret
  data types - **public_t** and **secret_t**, respectively. In addition to the instructions of
  **L**, it is also possible to define a set of secret operations **sop_t**, with the goal of
  defining secure mechanisms to compute that subset of operations. Intuitively, one may use the
  **L** data type to define language statements and *public* operations, while the operations
  over confidential data are fixed by *sop_t*. Finally, we also include the input out output 
  types that are consumed and produced by an evaluation of a program written in the language.

  The **Language** theory is modular enough to support multiple language formats, including high
  level programming languages with complex instructions, or low level representations such as
  boolean or arithmetic circuits.
*)
theory Language.

  (** Language instructions type. This type needs to be made concrete when the language is 
      instantiated *)
  type L.

  (** Public data types. This type needs to be made concrete when the language is instantiated *)
  type public_t.
  (** Confidential data types. This type needs to be made concrete when the language is 
      instantiated *)
  type secret_t.

  (** Set of operations to be carried out in a secure (confidential) way *)
  type sop_t.

  (** Program inputs *)
  type input_t.

  (** Program outputs *)
  type output_t.

end Language.
