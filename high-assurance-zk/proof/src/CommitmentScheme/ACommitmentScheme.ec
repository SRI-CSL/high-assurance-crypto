theory CommitmentScheme.  

  type msg_t.

  type rand_t.
  op valid_rand : rand_t -> bool.

  type commitment_t.
  type opening_string_t.
  type commit_info_t = commitment_t * opening_string_t.

  op commit : rand_t -> msg_t -> commit_info_t.

  op verify : msg_t -> commit_info_t -> bool.

  axiom correct (r : rand_t) (x : msg_t) : 
    valid_rand r =>
    verify x (commit r x).

end CommitmentScheme.
