module type CRPRF = sig 

  type input_t
  type output_t
  type key_t

  val f : key_t -> input_t -> output_t

end