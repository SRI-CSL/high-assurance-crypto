module type RFData = sig

  type input_t
  type output_t

end

module RF (RFD : RFData) = struct

  type input_t = RFD.input_t
  type output_t = RFD.output_t

end
