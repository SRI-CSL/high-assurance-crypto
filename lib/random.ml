open Domainslib

module LPZK = struct

  open LPZK

  let dt' () = Z.rem (Z.of_bits (Cryptokit.Random.string (Cryptokit.Random.pseudo_rng "0000000000000000") 128)) !LPZK.q
  let dt () =
    let coef = ref Z.zero in
    let quit = ref false in
    while not !quit do
      coef := dt' () ;
      if not (Z.equal !coef Z.zero) then quit := true
    done ;
    !coef

  let generate_lpzk_prover_randomness (ngates : int) : LPZK.prover_rand_t =
    let total_rand = ngates + 2 + 1 in
    let rp = Array.make total_rand LPZK.def_ui in
    let generate_random_ui () = { a = dt () ; b = dt () ; a' = dt () ; b' = dt () } in

    for i = 0 to total_rand - 1 do
      Array.set rp i (generate_random_ui ())
    done;
    rp

  let generate_lpzk_verifier_randomness (ngates : int) : LPZK.verifier_rand_t =
    let total_rand = ngates + 2 + 1 in
    let y = Array.make total_rand def_yi in
    let alpha = Z.rem (Z.of_bits (Cryptokit.Random.string Cryptokit.Random.secure_rng 128)) !LPZK.q in

    for i = 0 to total_rand - 1 do
      let a = dt () in
      let b = dt () in
      let a' = dt () in
      let b' = dt () in
      Array.set y i { v = Z.erem (Z.add (Z.mul a alpha) b) !LPZK.q ; v' = Z.erem (Z.add (Z.mul a' alpha) b') !LPZK.q }
    done;
    { alpha = alpha ; y = y }

  let parallel_generate_lpzk_prover_randomness pool (ngates : int) : LPZK.prover_rand_t =
    let total_rand = ngates + 2 + 1 in
    let rp = Array.make total_rand LPZK.def_ui in
    let generate_random_ui () = { a = dt () ; b = dt () ; a' = dt () ; b' = dt () } in

    Task.parallel_for pool ~start:0 ~finish:(total_rand - 1) ~body:(fun i ->
      Array.set rp i (generate_random_ui ())
    );
    rp

  let parallel_generate_lpzk_verifier_randomness pool (ngates : int) : LPZK.verifier_rand_t =
    let total_rand = ngates + 2 + 1 in
    let y = Array.make total_rand def_yi in
    let alpha = Z.rem (Z.of_bits (Cryptokit.Random.string Cryptokit.Random.secure_rng 128)) !LPZK.q in

    Task.parallel_for pool ~start:0 ~finish:(total_rand - 1) ~body:(fun i ->
      let a = dt () in
      let b = dt () in
      let a' = dt () in
      let b' = dt () in
      Array.set y i { v = Z.erem (Z.add (Z.mul a alpha) b) !LPZK.q ; v' = Z.erem (Z.add (Z.mul a' alpha) b') !LPZK.q }
    );
    { alpha = alpha ; y = y }

end