module type CommitmentSchemeData = sig

  type msg_t

  type rand_t

  type commitment_t
  type opening_string_t

  val commit : rand_t -> msg_t -> commitment_t * opening_string_t

  val verify : msg_t -> commitment_t * opening_string_t -> bool

end

module CommitmentScheme (CSD : CommitmentSchemeData) = struct

  type msg_t = CSD.msg_t

  type rand_t = CSD.rand_t

  type commitment_t = CSD.commitment_t
  type opening_string_t = CSD.opening_string_t
  type commit_info_t = commitment_t * opening_string_t

  let commit = CSD.commit

  let verify = CSD.verify

end
