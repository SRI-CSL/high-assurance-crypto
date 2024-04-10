open CRPRFCommitment

module SHA3 = struct

  type input_t = string
  type output_t = string
  type key_t = unit

  let f (k : key_t) (x : input_t) : output_t = 
    let sha3 = Cryptokit.Hash.sha3 256 in
    sha3#add_string x;
    String.sub (sha3#result) 0 16
end

module SHA3Commitment = CRPRFCommitment (SHA3)