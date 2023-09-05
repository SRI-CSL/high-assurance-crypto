open NextMsgECPervasive
open NextMsgECLogic
open NextMsgECCore
open NextMsgECList
open NextMsgMaurerP

(*ADDED*)
open MaurerSS

(* BEGIN ADDED *)
let rawShareSize : int = 4
let nRawShares : int = 10
let nRawSharesPP : int = 6
let nParties : int = 5
let randSharingSize : int = (nRawShares-1)*rawShareSize
let shareSize : int = nRawSharesPP*rawShareSize
let sharingSize : int = shareSize*nParties
let viewRowSize : int = randSharingSize+sharingSize
let stateRowSize : int = shareSize

let commitKeySize : int = 16

let viewSize n_total_wires = (n_total_wires+1) * viewRowSize + 1 
let stateSize n_total_wires = (n_total_wires) * stateRowSize

(* ADDED *) type ptr_t = int
(* ADDED *) type limbs_t = int * int * int * int
(* ADDED *) type size_t = int

(* wid1, wid2, st -> st*)
external maurer_add : int -> int -> (int * ptr_t) -> (int * ptr_t) = "maurer_add_c"
(* wid1, wid2, st -> st*)
external maurer_smul : int -> int -> (int * ptr_t) -> (int * ptr_t) = "maurer_smul_c"
(* val, st, pid -> st *)
external maurer_const : limbs_t -> (int * ptr_t) -> int -> (int * ptr_t) = "maurer_const_c" 
(* wid1, wid2, st, rnd-> msgs *)
external maurer_mul_start : int -> int  -> (int * ptr_t)  -> ptr_t -> ptr_t = "maurer_mul_start_c"
(* msgs, st, st *)
external maurer_mul_end : ptr_t -> (int * ptr_t) -> (int * ptr_t) = "maurer_mul_end_c"
(* wid, st -> msgs *)
external maurer_output_start : int -> (int * ptr_t) -> ptr_t = "maurer_output_start_c"
(* msgs -> val *)
external maurer_output_end : ptr_t -> limbs_t = "maurer_output_end_c"  
(* npins, nsins, nwires -> rnd for sharing, rnd for all parties, rnd for commitments *)                                                                                                                                                                                           
external prover_rand_gen : int -> int -> int -> (ptr_t Array.t * (ptr_t Array.t Array.t) * (ptr_t Array.t)) = "prover_rand_gen_c"                                                     
(* pid -> [number of wires] -> [wires already secret shared] -> [size of the circuit in wires] *)                  
external initial_status : int -> int -> (ptr_t Array.t) -> int * ptr_t = "initial_status_c"
(* five msgs *)
external maurer_dispatch : ptr_t -> ptr_t -> ptr_t -> ptr_t -> ptr_t -> unit = "maurer_dispatch_c"
(* shr, k -> v *)
external maurer_rawshare : int -> int -> int Array.t = "maurer_rawshare_c"
external compare_msg_c : int -> int -> bool = "compare_msg_c"
(* END ADDED *)

(* ADDED *) let nullp : ptr_t = 0
(* ADDED *) let isv0 (v : limbs_t) : bool = 
    let (v1,v2,v3,v4) = v in 
        v1 = 0 && v2 = 0 && v3 = 0 && v4 = 0

module MaurerAPI = struct
    type shr = (*ADDED*) ptr_t
    type shrs = (* ADDED *) ptr_t Array.t
    type _val = (* ADDED *) limbs_t
    type rshr = _val
    type msg = shr
    type msgs = (*ADDED*) ptr_t
    type wid = Pervasive.int
    type wire_st = (* ADDED *) size_t * ptr_t
    type pid = Pervasive.int
    type rand = (*ADDED*) ptr_t
    let mkwire_st : Pervasive.int -> Pervasive.int -> shr NextMsgIMap.IMap.imap -> wire_st = (* ADDED *)
        fun pid ninputs ws ->
            let arr = Array.init (Z.to_int ninputs) (fun wi -> Logic.oget (NextMsgIMap.IMap.get ws (Z.of_int wi))) in
            let wst = initial_status (Z.to_int pid) (Z.to_int ninputs) arr in
            Format.printf "initial wire_st %d %d \n@." (fst wst) (snd wst); wst
    let val_to_bool : (_val -> Pervasive.bool) = isv0
    let get_wire_st_next : (wire_st -> wid) = (* ADDED *) fun st -> Z.of_int (fst st)
    let get_wire_st_shr : (wire_st -> (wid -> shr)) = (* ADDED *)
        fun st w -> 
        (snd st) + 8*shareSize*(Z.to_int w)  
    let get_wire_st_fdom : (wire_st -> NextMsgISet.ISet.iset) = (* ADDED *)
        fun st ->
         NextMsgISet.ISet.oflist (List.Iota.iota_ (Z.of_int 0) (Z.of_int (fst st)))
    let get_rshr : (shr -> (Pervasive.int -> rshr)) = (*ADDED*)
        fun s i ->
        let v = maurer_rawshare s (Z.to_int i) in (v.(0),v.(1),v.(2),v.(3))
    let party_pshare : (pid -> (_val -> shr)) = (* ADDED *)
        fun p v ->
          ECOption.oget (ECList.assoc (MaurerSS.public_encoding () v) (p))
    let party_unpshare : (shr -> _val) = (* ADDED *)
        fun s ->
         MaurerSS.pub_reconstruct (Z.of_int 0) s
    let check_pshare : (pid -> (shr -> Pervasive.bool)) = (*ADDED*) fun (i) (ss) -> 
             compare_msg_c ss (party_pshare i (party_unpshare ss))
    let mk_shares : ((shr) MaurerP.arrayN -> shrs) = (*ADDED*)
        fun ss ->   
            Array.init 5 (fun i -> MaurerP.get ss (Z.of_int i))
    let mk_msgs (ss:msg MaurerP.arrayN) : msgs = (*ADDED*)
        MaurerP.get ss (Z.of_int 0)
    let shr_idx : (pid -> (Pervasive.int) Aux.array6) = (*ADDED*) fun p ->
        if p = (Z.of_int 0) then  (Z.of_int 5,( (Z.of_int 9,( (Z.of_int 8,( (Z.of_int 7,( (Z.of_int 4,( (Z.of_int 6))))))))))) else 
        if p = (Z.of_int 1) then  (Z.of_int 1,( (Z.of_int 2,( (Z.of_int 9,( (Z.of_int 3,( (Z.of_int 8,( (Z.of_int 7))))))))))) else
        if p = (Z.of_int 2) then  (Z.of_int 6,( (Z.of_int 0,( (Z.of_int 2,( (Z.of_int 5,( (Z.of_int 9,( (Z.of_int 3))))))))))) else
        if p = (Z.of_int 3) then  (Z.of_int 3,( (Z.of_int 8,( (Z.of_int 4,( (Z.of_int 6,( (Z.of_int 0,( (Z.of_int 1))))))))))) else
        if p = (Z.of_int 4) then  (Z.of_int 7,( (Z.of_int 4,( (Z.of_int 0,( (Z.of_int 1,( (Z.of_int 2,( (Z.of_int 5))))))))))) else
                      failwith "shr_idx"
    let get_shr : (shrs -> (Pervasive.int -> shr)) = (* ADDED *)
        fun ss p ->
        ss.(Z.to_int p)
    let get_msg (ms:msgs) (i:Pervasive.int) : msg = (*ADDED*)
        (ms + 8*shareSize*(Z.to_int i))
    let share : (_val -> (rand -> shrs)) = (*ADDED*) fun v r -> failwith "share"
    let add : (wid -> (wid -> (wire_st -> wire_st))) = (* ADDED *)
        fun wi wj wst ->
          (* Format.printf "Entering add\n@."; *)
          maurer_add (Z.to_int wi) (Z.to_int wj) wst
    let smul : (wid -> (wid -> (wire_st -> wire_st))) = (* ADDED *)
        fun wi wc wst ->
          (* Format.printf "Entering smul\n@."; *)
          maurer_smul (Z.to_int wi) (Z.to_int wc) wst
    let cnst : (pid -> (_val -> (wire_st -> wire_st))) = (* ADDED *)
        fun p v wst ->
          (* Format.printf "Entering const\n@."; *)
          maurer_const v wst (Z.to_int p)
    let mul_start : (wid -> (wid -> (wire_st -> (rand -> msgs)))) = (* ADDED *)
        fun wi wj wst r ->
          (* Format.printf "Entering mul start\n@."; *)
          (maurer_mul_start (Z.to_int wi) (Z.to_int wj) wst r)
    let mul_end : (msgs -> (wire_st -> wire_st)) = (* ADDED *)
        fun ms wst ->
          (* Format.printf "Entering mul end\n@."; *)
          maurer_mul_end (ms) wst
    let output_start : (wid -> (wire_st -> msgs)) = (* ADDED *)
        fun wi st ->
          (* Format.printf "Entering output start %d\n@." ((fst st) - 1); *)
          let r = maurer_output_start ((fst st) - 1) st in
          r
    let output_end : (msgs -> _val) = (* ADDED *)
        fun ms ->
          (* Format.printf "Entering output end\n@."; *)
          maurer_output_end (ms)
    let send_messages : ((msgs) MaurerP.arrayN -> (msgs) MaurerP.arrayN) = (* ADDED *)
        fun ms ->
              let m1 = (MaurerP.get ms (Z.of_int 0)) in
              let m2 = (MaurerP.get ms (Z.of_int 1)) in
              let m3 = (MaurerP.get ms (Z.of_int 2)) in
              let m4 = (MaurerP.get ms (Z.of_int 3)) in
              let m5 = (MaurerP.get ms (Z.of_int 4)) in
         maurer_dispatch m1 m2 m3 m4 m5; ms
    let eq_msg : (msg -> (msg -> Pervasive.bool)) = (*ADDED*) fun m1 m2 ->
         compare_msg_c m1 m2
    let eq_msgs (m1 : msgs) (m2 : msgs) : Pervasive.bool =
                                                             (List.all (fun (i : Pervasive.int) -> (eq_msg (get_msg m1 i) (get_msg m2 i))) (AuxList.iseq (Pervasive.mk_int 5)))
    let shrs_to_msgs : shrs -> msgs = fun ss ->
        mk_msgs (MaurerP.init (fun i -> get_shr ss i))
    let msgs_to_shrs : msgs -> shrs = fun ms ->
        mk_shares (MaurerP.init (fun i -> get_msg ms i))
    type pub_st = NextMsgISet.ISet.iset
    type g_sec = (wid * (_val) NextMsgIMap.IMap.imap)
    let unshare : (shrs -> _val) = (*ADDED*)
        fun ss ->
            let ms = shrs_to_msgs ss in
            maurer_output_end ms
    let g_unshare (xs : ((wire_st * pub_st)) MaurerP.arrayN) : (wid * (_val) NextMsgIMap.IMap.imap) =
                                                                                                       (let (pivot) = (fst (MaurerP.get xs (Pervasive.mk_int 0))) in
                                                                                                        (let (unshr) = (fun (wid : wid) -> (let (shares) = (MaurerP.map (fun (x : (wire_st * pub_st)) -> (get_wire_st_shr (fst x) wid)) xs) in
                                                                                                                                            (unshare (mk_shares shares)))) in
                                                                                                         ((get_wire_st_next pivot) , (NextMsgIMap.IMap.ofset unshr (get_wire_st_fdom pivot)))))
    let add_val : (_val -> (_val -> _val)) = (*ADDED*) fun v1 v2 -> failwith "add_val"
    let mul_val : (_val -> (_val -> _val)) = (*ADDED*) fun v1 v2 -> failwith "mul_val"
    let zero_val : _val = (0,0,0,0)
    let g_valid_share (s : (wire_st * pub_st)) : Pervasive.bool =
                                                                    (Pervasive._and (NextMsgISet.ISet.equal (get_wire_st_fdom (fst s)) (NextMsgISet.ISet.iset (get_wire_st_next (fst s)))) (NextMsgISet.ISet.subset (snd s) (get_wire_st_fdom (fst s))))
    let add_valid_share (wij : (wid * (wid * wid))) (s : (wire_st * pub_st)) : Pervasive.bool =
                                                                                                  (Pervasive._and (g_valid_share s) (Pervasive._and (Pervasive.eq (Aux.nth0_3 wij) (get_wire_st_next (fst s))) (Pervasive._and (NextMsgISet.ISet.mem (Aux.nth1_3 wij) (get_wire_st_fdom (fst s))) (NextMsgISet.ISet.mem (Aux.nth2_3 wij) (get_wire_st_fdom (fst s))))))
    let smul_valid_share (wij : (wid * (wid * wid))) (s : (wire_st * pub_st)) : Pervasive.bool =
                                                                                                   (Pervasive._and (add_valid_share wij s) (NextMsgISet.ISet.mem (Aux.nth2_3 wij) (snd s)))
    let const_valid_share (wij : (wid * _val)) (s : (wire_st * pub_st)) : Pervasive.bool =
                                                                                             (Pervasive._and (g_valid_share s) (Pervasive.eq (fst wij) (get_wire_st_next (fst s))))
    let consistent_pub_shares (i : pid) (j : pid) (p1 : shr) (p2 : shr) : Pervasive.bool =
                                                                                             (Pervasive._and (check_pshare i p1) (Pervasive._and (check_pshare j p2) (Pervasive.eq (party_unpshare p1) (party_unpshare p2))))
    let raw_shares (i : pid) (s : shr) : (rshr) NextMsgIMap.IMap.imap =
                                                                         (AuxList.foldl_iseq (fun (m : (rshr) NextMsgIMap.IMap.imap) (k : Pervasive.int) -> (let (j) = (Aux.nth_array6 (shr_idx i) k) in
                                                                                                                                                            (NextMsgIMap.IMap.set m j (get_rshr s k)))) (NextMsgIMap.IMap.empty) (Pervasive.mk_int 6))
    let consistent_raw_shares (i : pid) (j : pid) (s1 : shr) (s2 : shr) : Pervasive.bool =
                                                                                             (NextMsgIMap.IMap.all (fun (_ : Pervasive.int) (xy : (rshr * rshr)) -> (Pervasive.eq (fst xy) (snd xy))) (NextMsgIMap.IMap.zip (raw_shares i s1) (raw_shares j s2)))
    let valid_raw_shares (ss : shrs) : Pervasive.bool =
                                                          (Pervasive.witness)
    let consistent_shares (i : pid) (j : pid) (s1 : (wire_st * pub_st)) (s2 : (wire_st * pub_st)) : Pervasive.bool =
                                                                                                                       (Pervasive._and (Pervasive.eq (get_wire_st_next (fst s1)) (get_wire_st_next (fst s2))) (Pervasive._and (Pervasive.eq (get_wire_st_fdom (fst s1)) (get_wire_st_fdom (fst s2))) (Pervasive._and (Pervasive.eq (snd s1) (snd s2)) (Pervasive._and (NextMsgISet.ISet.all (fun (wid : wid) -> (consistent_pub_shares i j (get_wire_st_shr (fst s1) wid) (get_wire_st_shr (fst s2) wid))) (snd s1)) (AuxList.all_iseq (fun (wid : wid) -> (consistent_raw_shares i j (get_wire_st_shr (fst s1) wid) (get_wire_st_shr (fst s2) wid))) (get_wire_st_next (fst s1)))))))
    let consistent_vals (v1 : _val) (v2 : _val) : Pervasive.bool =
                                                                     (val_to_bool v1) && (val_to_bool v2)
end
