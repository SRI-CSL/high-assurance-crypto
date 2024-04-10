open ACommitment
open CRPRF

module CRPRFCommitmentData (CRPRF : CRPRF) = struct

  type msg_t = CRPRF.input_t

  type rand_t = CRPRF.key_t

  type commitment_t = CRPRF.output_t
  type opening_string_t = CRPRF.key_t

  let commit (r : rand_t) (x : msg_t) : commitment_t * opening_string_t = (CRPRF.f r x, r)

  let verify (x : msg_t) (ci : commitment_t * opening_string_t) : bool = fst ci = CRPRF.f (snd ci) x

end

module CRPRFCommitment (CRPRF : CRPRF) = CommitmentScheme (CRPRFCommitmentData(CRPRF))