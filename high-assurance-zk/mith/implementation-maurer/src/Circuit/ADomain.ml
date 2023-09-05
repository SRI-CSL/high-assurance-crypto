module type Domain = sig

  type wire_t

  val wire_to_bool : wire_t -> bool

end
