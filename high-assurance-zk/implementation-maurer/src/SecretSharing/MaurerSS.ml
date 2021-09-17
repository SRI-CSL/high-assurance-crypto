open Utils
open ECList
open ECOption

open ASecretSharingScheme

(* val -> shr *)
external maurer_pshare_c :  int Array.t -> int Array.t = "maurer_pshare_c" 
external maurer_punshare : int -> int Array.t = "maurer_punshare_c"
external maurer_share : int ->  int Array.t -> (int * int) Array.t = "maurer_share_c"

(* THIS IS NOT USED *)   
external maurer_reconstruct : (int * int) Array.t -> int Array.t = "maurer_reconstruct_c"
(**********************)

module MaurerData = struct

  let n : Z.t = Z.of_int 5
  let t : Z.t = Z.of_int 2
    
  type pid_t = Z.t
  let pid_set : pid_t list = Cons (Z.of_int 0, Cons (Z.of_int 1, Cons (Z.of_int 2, Cons (Z.of_int 3, Cons (Z.of_int 4, Nil)))))

  type share_t = int
  type shares_t = (pid_t * share_t) list

  type rand_t = int
  type aux_t = unit

  type secret_t = int * int * int * int
  let valid_secret(s : secret_t) = true

  let public_encoding (aux : aux_t) (x : secret_t) : (pid_t * share_t) list =
    let (x1,x2,x3,x4) = x in 
    (*Format.printf "Starting public encoding x1 = %d\n@." x1 ; *)
    let ss = maurer_pshare_c (eclist_to_array (Cons (x1,Cons (x2, Cons (x3, Cons (x4,Nil))))))  in
    map (fun pid -> (pid, ss.(Z.to_int pid))) pid_set

  let pub_reconstruct (pid : pid_t) (sh : share_t) : secret_t =
      (* Format.printf "Starting public reconstruct x1 = %d\n@." (Z.to_int pid) ; *)
    let v = maurer_punshare sh in (v.(0),v.(1),v.(2),v.(3))

  let share (r : rand_t) (x : secret_t) : (pid_t * share_t) list =
      (* Format.printf "Starting share \n@."  ; *)
    let (x1,x2,x3,x4) = x in 
    let ss = maurer_share r (eclist_to_array (Cons (x1,Cons (x2, Cons (x3, Cons (x4,Nil))))))  in
    map (fun pid -> (Z.of_int (fst ss.(Z.to_int pid)), snd ss.(Z.to_int pid))) pid_set

  let reconstruct (xx : (pid_t * share_t) list) : secret_t =
    (* Format.printf "Starting reconstruct\n@."  ; *)
    let ss = eclist_to_array (map (fun pid -> (Z.to_int pid, oget (assoc xx pid))) pid_set) in 
    let v = maurer_reconstruct ss in (v.(0),v.(1),v.(2),v.(3))

  let get_party_share (pid : pid_t) (xs : shares_t) : share_t = oget (assoc xs pid)

end

module MaurerSS = SecretSharingScheme (MaurerData)
