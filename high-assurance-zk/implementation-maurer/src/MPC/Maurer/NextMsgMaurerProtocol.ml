open NextMsgECList
open NextMsgECPervasive
open NextMsgECCore
open NextMsgECInt
open NextMsgECLogic
open NextMsgMaurerP
open NextMsgArray
open NextMsgMaurerAPI
module MaurerAdd = struct
    type _Gate = (NextMsgMaurerAPI.MaurerAPI.wid * (NextMsgMaurerAPI.MaurerAPI.wid * NextMsgMaurerAPI.MaurerAPI.wid))
    type share = (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)
    type local_msgs = Pervasive.unit
    type local_in_msgs = local_msgs
    type local_out_msgs = local_msgs
    module GT = struct
        type public_input = _Gate
        module P = struct
            let rec size : Pervasive.int =
                                             (NextMsgMaurerP.MaurerP.size)
            type ('a) arrayN = ('a) NextMsgMaurerP.MaurerP.arrayN
            let rec get : (('a) Aux.array5 -> (Pervasive.int -> 'a)) =
                                                                         (NextMsgMaurerP.MaurerP.get)
            let rec set : (('a) Aux.array5 -> (Pervasive.int -> ('a -> ('a * ('a * ('a * ('a) Aux.array2)))))) =
                                                                                                                   (NextMsgMaurerP.MaurerP.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a * ('a * ('a * ('a * 'a))))) =
                                                                                         (NextMsgMaurerP.MaurerP.init)
            let rec of_list : (('a) List.list -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                         (NextMsgMaurerP.MaurerP.of_list)
            let rec to_list : (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) List.list) =
                                                                                         (NextMsgMaurerP.MaurerP.to_list)
            let rec to_assoc : (('a) NextMsgMaurerP.MaurerP.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                                            (NextMsgMaurerP.MaurerP.to_assoc)
            let rec create : ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                            (NextMsgMaurerP.MaurerP.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                              (NextMsgMaurerP.MaurerP.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('b) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                             (NextMsgMaurerP.MaurerP.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> (('b) NextMsgMaurerP.MaurerP.arrayN -> ('c) NextMsgMaurerP.MaurerP.arrayN))) =
                                                                                                                                                                           (NextMsgMaurerP.MaurerP.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                                           (NextMsgMaurerP.MaurerP.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool)) =
                                                                                                                                    (NextMsgMaurerP.MaurerP.all)
            let rec allsame : (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool) =
                                                                                         (NextMsgMaurerP.MaurerP.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) NextMsgMaurerP.MaurerP.arrayN) List.list -> (('b) List.list) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                                                                    (NextMsgMaurerP.MaurerP.concat)
        end
        let parties : Pervasive.int =
                                        (P.size)
        type party = Pervasive.int
        let partyset : NextMsgISet.ISet.iset =
                                                 (NextMsgISet.ISet.iset (parties))
        type round = Pervasive.int
        let rounds (_ : public_input) : Pervasive.int =
                                                          (Pervasive.mk_int 1)
        let roundset (p : public_input) : NextMsgISet.ISet.iset =
                                                                    (NextMsgISet.ISet.iset (rounds p))
        type ('a) pmap = ('a) P.arrayN
        type ('a) rmap = ('a) NextMsgArray.Array.array
        type ('a) prmap = (('a) rmap) pmap
        type ('a) ppmap = (('a) pmap) pmap
        type ('a) pprmap = (('a) rmap) ppmap
        type local_input = share
        type local_output = share
        type local_rand = Pervasive.unit
        type msg = Pervasive.unit
        type pmsgs = (msg) pmap
        type rmsgs = (msg) rmap
        type prmsgs = (rmsgs) pmap
        type ppmsgs = (pmsgs) pmap
        type pprmsgs = (prmsgs) pmap
        type in_msgs = prmsgs
        type out_msgs = prmsgs
        type view = (local_input * (in_msgs * local_rand))
        type trace = (view) pmap
        let eq_msg (_ : msg) (_ : msg) : Pervasive.bool =
                                                            (Pervasive._true)
        let eq_pmsgs (m1 : pmsgs) (m2 : pmsgs) : Pervasive.bool =
                                                                    (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (P.get m1 i) (P.get m2 i))) (P.size))
        let eq_rmsgs (m1 : rmsgs) (m2 : rmsgs) : Pervasive.bool =
                                                                    (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size m1) (NextMsgArray.Array.size m2)) (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (NextMsgArray.Array.get m1 i) (NextMsgArray.Array.get m2 i))) (NextMsgArray.Array.size m1)))
        let pinit (f : (party -> 'a)) : ('a) P.arrayN =
                                                          (P.init f)
        let ppinit (f : (party -> (party -> 'a))) : (('a) P.arrayN) P.arrayN =
                                                                                 (pinit (fun (i : party) -> (pinit (f i))))
        let prempty (sz : Pervasive.int) (v : 'a) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                 (pinit (fun (_ : party) -> (NextMsgArray.Array.create sz v)))
        let pprempty (sz : Pervasive.int) (v : 'a) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                             (ppinit (fun (_ : party) (_ : party) -> (NextMsgArray.Array.create sz v)))
        let ppswap (m : ('a) ppmap) : (('a) P.arrayN) P.arrayN =
                                                                   (ppinit (fun (j : Pervasive.int) (i : Pervasive.int) -> (P.get (P.get m i) j)))
        let prget (xs : ('a) prmap) (r : round) : ('a) P.arrayN =
                                                                    (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.get (P.get xs i) r)))
        let pprget (xs : ('a) pprmap) (r : round) : (('a) P.arrayN) P.arrayN =
                                                                                 (ppinit (fun (i : Pervasive.int) (j : Pervasive.int) -> (NextMsgArray.Array.get (P.get (P.get xs i) j) r)))
        let prset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.merge (fun (x0 : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set x0 n y)) xs x)
        let prext (sz : Pervasive.int) (xs : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.init sz (fun (j : Pervasive.int) -> if (Pervasive._and (Int.le (Pervasive.mk_int 0) j) (Int.lt j (NextMsgArray.Array.size (P.get xs i)))) then (NextMsgArray.Array.get (P.get xs i) j) else (Pervasive.witness)))))
        let prextset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                          (prset (prext (Int.plus n (Pervasive.mk_int 1)) xs) n x)
        let pprset (xs : ('a) pprmap) (n : round) (x : ('a) ppmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                             (P.merge (P.merge (fun (ys : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set ys n y))) xs x)
        let prfilter (p : (round -> Pervasive.bool)) (ins : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) ins)
        let pprfilter (p : (round -> Pervasive.bool)) (ins : ('a) pprmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                                    (P.map (fun (xs : (('a) NextMsgArray.Array.array) P.arrayN) -> (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) xs)) ins)
        let rdom (sz : Pervasive.int) (round : round) (xs : ('a) rmap) : Pervasive.bool =
                                                                                            (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size xs) sz) (Pervasive.witness))
        let prdom (sz : Pervasive.int) (round : round) (xs : ('a) prmap) : Pervasive.bool =
                                                                                              (P.all (fun (_ : Pervasive.int) -> (rdom sz round)) xs)
        let pprdom (sz : Pervasive.int) (round : round) (xs : ('a) pprmap) : Pervasive.bool =
                                                                                                (P.all (fun (_ : Pervasive.int) -> (prdom sz round)) xs)
        let rlist (sz : Pervasive.int) (xs : ('a) List.list) : ('a) NextMsgArray.Array.array =
                                                                                                 (List.foldl (fun (rs : ('a) NextMsgArray.Array.array) (i : Pervasive.int) -> (NextMsgArray.Array.set rs i (List.nth (Pervasive.witness) xs i))) (NextMsgArray.Array.create sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let prlist (sz : Pervasive.int) (xs : (pmsgs) List.list) : (msg) prmap =
                                                                                   (List.foldl (fun (rs : (msg) prmap) (i : Pervasive.int) -> (prset rs i (List.nth (Pervasive.witness) xs i))) (prempty sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let pcons (x : ('a) pmap) (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                               (P.merge (fun (x0 : 'a) (xs0 : ('a) List.list) -> (AuxList.cons x0 xs0)) x xs)
        let phead (xs : (('a) List.list) pmap) : ('a) P.arrayN =
                                                                   (P.map (List.head (Pervasive.witness)) xs)
        let pbehead (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                 (P.map (List.behead) xs)
        let prcons (xs : (('a) List.list) pmap) (x : ('a) pmap) : (('a) List.list) P.arrayN =
                                                                                                (P.merge (List.rcons) xs x)
        let pcat (xs : (('a) List.list) pmap) (ys : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                                           (P.merge (fun (x : ('a) List.list) (y : ('a) List.list) -> (AuxList.cat x y)) xs ys)
        let ppcons (x : ('a) ppmap) (xs : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                             (P.merge (pcons) x xs)
        let pprcons (xs : (('a) List.list) ppmap) (x : ('a) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                              (P.merge (prcons) xs x)
        let ppcat (xs : (('a) List.list) ppmap) (ys : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                                         (P.merge (pcat) xs ys)
        let prmsgs_up_to (round : round) (ins : prmsgs) : ((msg) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (prfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let pprmsgs_up_to (round : round) (ins : pprmsgs) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                     (pprfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let get_trace_inputs (tr : trace) : (local_input) P.arrayN =
                                                                       (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.fst3 x)) tr)
        let get_trace_in_msgs (tr : trace) : (in_msgs) P.arrayN =
                                                                    (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.snd3 x)) tr)
        let get_trace_rands (tr : trace) : (local_rand) P.arrayN =
                                                                     (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.thr3 x)) tr)
        let get_view (i : party) (tr : trace) : view =
                                                         (P.get tr i)
        let get_trace_in_msgs_round (round : round) (tr : trace) : ((msg) P.arrayN) P.arrayN =
                                                                                                 (pprget (get_trace_in_msgs tr) round)
        let get_view_in_msgs_round (round : round) (v : view) : (msg) P.arrayN =
                                                                                   (prget (Aux.snd3 v) round)
        let add_view_in_msgs (r : round) (ins : pmsgs) (v : view) : (local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand)) =
                                                                                                                                                 ((Aux.fst3 v) , ((prset (Aux.snd3 v) r ins) , (Aux.thr3 v)))
        let get_trace_in_msgs_up_to (round : round) (tr : trace) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                            (pprmsgs_up_to round (get_trace_in_msgs tr))
        let add_trace_in_msgs (r : round) (ins : ppmsgs) (tr : trace) : ((local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand))) P.arrayN =
                                                                                                                                                                (P.map (fun (ins_v : (pmsgs * view)) -> (add_view_in_msgs r (Aux.fst3 ins_v) (snd ins_v))) (P.zip ins tr))
        let valid_trace (x : public_input) (tr : trace) : Pervasive.bool =
                                                                             (pprdom (rounds x) (rounds x) (get_trace_in_msgs tr))
        let valid_view (x : public_input) (v : view) : Pervasive.bool =
                                                                          (prdom (rounds x) (rounds x) (Aux.snd3 v))
    end
    let local_gate_start (_ : GT.party) (_ : _Gate) (_ : share) (_ : GT.local_rand) : Pervasive.unit =
                                                                                                         (Pervasive.tt)
    let local_gate_end (_ : GT.party) (wij : _Gate) (st : share) (_ : local_in_msgs) : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) =
                                                                                                                                                                    ((NextMsgMaurerAPI.MaurerAPI.add (Aux.nth1_3 wij) (Aux.nth2_3 wij) (fst st)) , (snd st))
    let gate_valid_rand (_ : _Gate) (_ : GT.local_rand) : Pervasive.bool =
                                                                             (Pervasive._true)
    let gate_valid_rands (x : _Gate) (cs : (GT.local_rand) GT.P.arrayN) : Pervasive.bool =
                                                                                             (GT.P.all (fun (_ : Pervasive.int) (c : GT.local_rand) -> (gate_valid_rand x c)) cs)
    module ST = struct
        type public_input = GT.public_input
        module P = struct
            let rec size : Pervasive.int =
                                             (GT.P.size)
            type ('a) arrayN = ('a) GT.P.arrayN
            let rec get : (('a) GT.P.arrayN -> (Pervasive.int -> 'a)) =
                                                                          (GT.P.get)
            let rec set : (('a) GT.P.arrayN -> (Pervasive.int -> ('a -> ('a) GT.P.arrayN))) =
                                                                                                (GT.P.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a) GT.P.arrayN) =
                                                                           (GT.P.init)
            let rec of_list : (('a) List.list -> ('a) GT.P.arrayN) =
                                                                       (GT.P.of_list)
            let rec to_list : (('a) GT.P.arrayN -> ('a) List.list) =
                                                                       (GT.P.to_list)
            let rec to_assoc : (('a) GT.P.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                          (GT.P.to_assoc)
            let rec create : ('a -> ('a) GT.P.arrayN) =
                                                          (GT.P.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) GT.P.arrayN)) =
                                                                            (GT.P.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) GT.P.arrayN -> ('b) GT.P.arrayN)) =
                                                                                                         (GT.P.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) GT.P.arrayN -> (('b) GT.P.arrayN -> ('c) GT.P.arrayN))) =
                                                                                                                     (GT.P.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) GT.P.arrayN -> ('a) GT.P.arrayN)) =
                                                                                                                       (GT.P.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) GT.P.arrayN -> Pervasive.bool)) =
                                                                                                                  (GT.P.all)
            let rec allsame : (('a) GT.P.arrayN -> Pervasive.bool) =
                                                                       (GT.P.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) GT.P.arrayN) List.list -> (('b) List.list) GT.P.arrayN) =
                                                                                                (GT.P.concat)
        end
        let rec parties : Pervasive.int =
                                            (GT.parties)
        type party = GT.party
        let rec partyset : NextMsgISet.ISet.iset =
                                                     (GT.partyset)
        type round = GT.round
        let rec rounds : (GT.public_input -> Pervasive.int) =
                                                                (GT.rounds)
        let rec roundset : (GT.public_input -> NextMsgISet.ISet.iset) =
                                                                          (GT.roundset)
        type ('a) pmap = ('a) GT.pmap
        type ('a) rmap = ('a) GT.rmap
        type ('a) prmap = ('a) GT.prmap
        type ('a) ppmap = ('a) GT.ppmap
        type ('a) pprmap = ('a) GT.pprmap
        type local_input = GT.local_input
        type local_output = GT.local_output
        type local_rand = GT.local_rand
        type msg = GT.msg
        type pmsgs = GT.pmsgs
        type rmsgs = GT.rmsgs
        type prmsgs = GT.prmsgs
        type ppmsgs = GT.ppmsgs
        type pprmsgs = GT.pprmsgs
        type in_msgs = GT.in_msgs
        type out_msgs = GT.out_msgs
        type view = GT.view
        type trace = GT.trace
        let rec eq_msg : (GT.msg -> (GT.msg -> Pervasive.bool)) =
                                                                    (GT.eq_msg)
        let rec eq_pmsgs : (GT.pmsgs -> (GT.pmsgs -> Pervasive.bool)) =
                                                                          (GT.eq_pmsgs)
        let rec eq_rmsgs : (GT.rmsgs -> (GT.rmsgs -> Pervasive.bool)) =
                                                                          (GT.eq_rmsgs)
        let rec pinit : ((GT.party -> 'a) -> ('a) GT.P.arrayN) =
                                                                   (GT.pinit)
        let rec ppinit : ((GT.party -> (GT.party -> 'a)) -> (('a) GT.P.arrayN) GT.P.arrayN) =
                                                                                                (GT.ppinit)
        let rec prempty : (Pervasive.int -> ('a -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                     (GT.prempty)
        let rec pprempty : (Pervasive.int -> ('a -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                    (GT.pprempty)
        let rec ppswap : (('a) GT.ppmap -> (('a) GT.P.arrayN) GT.P.arrayN) =
                                                                               (GT.ppswap)
        let rec prget : (('a) GT.prmap -> (GT.round -> ('a) GT.P.arrayN)) =
                                                                              (GT.prget)
        let rec pprget : (('a) GT.pprmap -> (GT.round -> (('a) GT.P.arrayN) GT.P.arrayN)) =
                                                                                              (GT.pprget)
        let rec prset : (('a) GT.prmap -> (Pervasive.int -> (('a) GT.pmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN))) =
                                                                                                                                (GT.prset)
        let rec prext : (Pervasive.int -> (('a) GT.prmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                              (GT.prext)
        let rec prextset : (('a) GT.prmap -> (Pervasive.int -> (('a) GT.pmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN))) =
                                                                                                                                   (GT.prextset)
        let rec pprset : (('a) GT.pprmap -> (GT.round -> (('a) GT.ppmap -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN))) =
                                                                                                                                            (GT.pprset)
        let rec prfilter : ((GT.round -> Pervasive.bool) -> (('a) GT.prmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                                                (GT.prfilter)
        let rec pprfilter : ((GT.round -> Pervasive.bool) -> (('a) GT.pprmap -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                                (GT.pprfilter)
        let rec rdom : (Pervasive.int -> (GT.round -> (('a) GT.rmap -> Pervasive.bool))) =
                                                                                             (GT.rdom)
        let rec prdom : (Pervasive.int -> (GT.round -> (('a) GT.prmap -> Pervasive.bool))) =
                                                                                               (GT.prdom)
        let rec pprdom : (Pervasive.int -> (GT.round -> (('a) GT.pprmap -> Pervasive.bool))) =
                                                                                                 (GT.pprdom)
        let rec rlist : (Pervasive.int -> (('a) List.list -> ('a) NextMsgArray.Array.array)) =
                                                                                                 (GT.rlist)
        let rec prlist : (Pervasive.int -> ((GT.pmsgs) List.list -> (GT.msg) GT.prmap)) =
                                                                                            (GT.prlist)
        let rec pcons : (('a) GT.pmap -> ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                         (GT.pcons)
        let rec phead : ((('a) List.list) GT.pmap -> ('a) GT.P.arrayN) =
                                                                           (GT.phead)
        let rec pbehead : ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN) =
                                                                                         (GT.pbehead)
        let rec prcons : ((('a) List.list) GT.pmap -> (('a) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                          (GT.prcons)
        let rec pcat : ((('a) List.list) GT.pmap -> ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                                    (GT.pcat)
        let rec ppcons : (('a) GT.ppmap -> ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                          (GT.ppcons)
        let rec pprcons : ((('a) List.list) GT.ppmap -> (('a) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                           (GT.pprcons)
        let rec ppcat : ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                     (GT.ppcat)
        let rec prmsgs_up_to : (GT.round -> (GT.prmsgs -> ((GT.msg) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                                (GT.prmsgs_up_to)
        let rec pprmsgs_up_to : (GT.round -> (GT.pprmsgs -> (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                (GT.pprmsgs_up_to)
        let rec get_trace_inputs : (GT.trace -> (GT.local_input) GT.P.arrayN) =
                                                                                  (GT.get_trace_inputs)
        let rec get_trace_in_msgs : (GT.trace -> (GT.in_msgs) GT.P.arrayN) =
                                                                               (GT.get_trace_in_msgs)
        let rec get_trace_rands : (GT.trace -> (GT.local_rand) GT.P.arrayN) =
                                                                                (GT.get_trace_rands)
        let rec get_view : (GT.party -> (GT.trace -> GT.view)) =
                                                                   (GT.get_view)
        let rec get_trace_in_msgs_round : (GT.round -> (GT.trace -> ((GT.msg) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                             (GT.get_trace_in_msgs_round)
        let rec get_view_in_msgs_round : (GT.round -> (GT.view -> (GT.msg) GT.P.arrayN)) =
                                                                                             (GT.get_view_in_msgs_round)
        let rec add_view_in_msgs : (GT.round -> (GT.pmsgs -> (GT.view -> (GT.local_input * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))))) =
                                                                                                                                                                     (GT.add_view_in_msgs)
        let rec get_trace_in_msgs_up_to : (GT.round -> (GT.trace -> (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                        (GT.get_trace_in_msgs_up_to)
        let rec add_trace_in_msgs : (GT.round -> (GT.ppmsgs -> (GT.trace -> ((GT.local_input * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))) GT.P.arrayN))) =
                                                                                                                                                                                      (GT.add_trace_in_msgs)
        let rec valid_trace : (GT.public_input -> (GT.trace -> Pervasive.bool)) =
                                                                                    (GT.valid_trace)
        let rec valid_view : (GT.public_input -> (GT.view -> Pervasive.bool)) =
                                                                                  (GT.valid_view)
    end
    type local_messages = local_msgs
    type messages = (local_messages) ST.pmap
    type local_out_messages = local_messages
    type local_in_messages = local_messages
    type out_messages = messages
    type in_messages = messages
    let from_local_messages (_ : local_messages) : (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * Pervasive.unit)))) =
                                                                                                                                                  (NextMsgMaurerP.MaurerP.init (fun (_ : Pervasive.int) -> (Pervasive.tt)))
    let to_local_messages (_ : ST.pmsgs) : Pervasive.unit =
                                                              (Pervasive.tt)
    let send_messages (_ : out_messages) : (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * Pervasive.unit)))) =
                                                                                                                                          (NextMsgMaurerP.MaurerP.init (fun (_ : Pervasive.int) -> (Pervasive.tt)))
    let from_messages (xs : (local_messages) ST.P.arrayN) : (ST.pmsgs) ST.P.arrayN =
                                                                                       (ST.P.map (from_local_messages) xs)
    let to_messages (xs : (ST.pmsgs) ST.P.arrayN) : (local_messages) ST.P.arrayN =
                                                                                     (ST.P.map (to_local_messages) xs)
    let valid_local_messages (_ : ST.public_input) (_ : ST.round) (_ : local_messages) : Pervasive.bool =
                                                                                                            (Pervasive._true)
    let valid_messages (p : ST.public_input) (r : ST.round) (ms : messages) : Pervasive.bool =
                                                                                                 (ST.P.all (fun (_ : Pervasive.int) -> (valid_local_messages p r)) ms)
    let valid_msg (_ : ST.public_input) (_ : ST.round) (_ : ST.msg) : Pervasive.bool =
                                                                                         (Pervasive._true)
    let valid_pmsgs (p : ST.public_input) (r : ST.round) (ms : ST.pmsgs) : Pervasive.bool =
                                                                                              (ST.P.all (fun (_ : Pervasive.int) -> (valid_msg p r)) ms)
    let valid_ppmsgs (p : ST.public_input) (r : ST.round) (ms : ST.ppmsgs) : Pervasive.bool =
                                                                                                (ST.P.all (fun (_ : Pervasive.int) -> (valid_pmsgs p r)) ms)
    type local_state = (share * (GT.local_rand, local_in_msgs) Aux.either)
    let init_local_state (_ : ST.party) (_ : ST.public_input) (wis : share) (ris : ST.local_rand) : (share * (ST.local_rand, local_in_msgs) Aux.either) =
                                                                                                                                                            (wis , (Aux.L ris))
    let update_local_state (_ : ST.party) (_ : ST.round) (_ : ST.public_input) (_ : ST.local_input) (ins : local_in_messages) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : (share * (GT.local_rand, local_in_messages) Aux.either) =
                                                                                                                                                                                                                                                       ((fst st) , (Aux.R ins))
    let get_local_state (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : local_state =
                                                                                                                                                             (let (go) = (fun (st : local_state) (r0 : ST.round) -> (let (insr) = (ST.prget insi r0) in
                                                                                                                                                                                                                     (update_local_state i r0 x wi (to_local_messages insr) st))) in
                                                                                                                                                              (List.foldl go (init_local_state i x wi ri) (AuxList.iseq r)))
    type state = (local_state) ST.pmap
    let init_state (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                        (ST.P.imap (fun (i : ST.party) (wi_ri : (ST.local_input * ST.local_rand)) -> (init_local_state i x (fst wi_ri) (snd wi_ri))) (ST.P.zip ws rs))
    let update_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (local_in_messages) ST.pmap) (st : state) : (local_state) ST.P.arrayN =
                                                                                                                                                                               (ST.P.imap (fun (i : ST.party) (wsi_insi_sti : (ST.local_input * (local_in_messages * local_state))) -> (update_local_state i round x (Aux.fst3 wsi_insi_sti) (Aux.snd3 wsi_insi_sti) (Aux.thr3 wsi_insi_sti))) (ST.P.zip3 ws ins st))
    let get_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                                                                       (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (get_local_state i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) (ST.P.zip3 ws rs ins))
    let stateful_local_protocol_round (i : GT.party) (_ : ST.round) (g : _Gate) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : local_out_msgs =
                                                                                                                                                                (local_gate_start i g (fst st) (Aux.unL (snd st)))
    let stateful_local_protocol_end (i : GT.party) (g : _Gate) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : share =
                                                                                                                                      (local_gate_end i g (fst st) (Aux.unR (snd st)))
    let stateful_local_protocol''' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : (ST.round) List.list) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                                            (List.foldl (fun (acc : (local_state * ST.out_msgs)) (round : ST.round) -> (let (outs') = (ST.prset (snd acc) round (from_local_messages (stateful_local_protocol_round i round x (Aux.fst3 acc)))) in
                                                                                                                                                                                                                                                                                                        (let (st') = (update_local_state i round x inp (to_local_messages (ST.prget ins round)) (Aux.fst3 acc)) in
                                                                                                                                                                                                                                                                                                         (st' , outs')))) (st , (ST.prempty sz (Pervasive.witness))) rounds)
    let stateful_local_protocol'' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                               (stateful_local_protocol''' i x inp st ins sz (AuxList.iseq rounds))
    let stateful_local_protocol' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) : (local_state * ST.out_msgs) =
                                                                                                                                                                     (stateful_local_protocol'' i x inp st ins (ST.rounds x) (ST.rounds x))
    let stateful_local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                          (let (outs) = (stateful_local_protocol' i x (Aux.fst3 vi) (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) (Aux.snd3 vi)) in
                                                                                                                           (let (out) = (stateful_local_protocol_end i x (Aux.fst3 outs)) in
                                                                                                                            ((snd outs) , out)))
    let stateful_protocol_round (round : ST.round) (x : ST.public_input) (st : state) : (local_out_messages) ST.P.arrayN =
                                                                                                                             (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_round i round x sti)) st)
    let stateful_protocol_end (x : ST.public_input) (st : state) : (ST.local_output) ST.P.arrayN =
                                                                                                     (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_end i x sti)) st)
    let stateful_protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : (ST.round) List.list) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                                  (List.foldl (fun (ins_st : ((ST.in_msgs) ST.pmap * state)) (round : ST.round) -> (let (ins0) = (Aux.fst3 ins_st) in
                                                                                                                                                                                                                                                                                    (let (st0) = (snd ins_st) in
                                                                                                                                                                                                                                                                                     (let (outs) = (send_messages (stateful_protocol_round round x st0)) in
                                                                                                                                                                                                                                                                                      ((ST.pprset ins0 round (from_messages outs)) , (update_state round x ws outs st0)))))) (ins , st) rounds)
    let stateful_protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : ST.round) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                     (stateful_protocol''' x ws ins st (AuxList.iseq rounds))
    let stateful_protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                     (stateful_protocol'' x ws (ST.pprempty (ST.rounds x) (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                     (let (ins_st') = (stateful_protocol' x ws rs) in
                                                                                                                                                                                                                      (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                       (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                        (tr , outs))))
    let stateful_protocol_sz' (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                             (stateful_protocol'' x ws (ST.pprempty sz (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol_sz (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                                             (let (ins_st') = (stateful_protocol_sz' sz x ws rs) in
                                                                                                                                                                                                                                              (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                                               (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                                                (tr , outs))))
    let local_protocol_round (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.pmsgs =
                                                                                                                                                               (from_local_messages (stateful_local_protocol_round i r x (get_local_state i r x wi ri insi)))
    let local_protocol_end (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.local_output =
                                                                                                                                                     (stateful_local_protocol_end i x (get_local_state i (ST.rounds x) x wi ri insi))
    let local_protocol'' (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : ST.out_msgs =
                                                                                                                                                                                       (List.foldl (fun (outs : ST.out_msgs) (round : Pervasive.int) -> (ST.prset outs round (local_protocol_round i round x wi ri ins))) (ST.prempty sz (Pervasive.witness)) (AuxList.iseq rounds))
    let local_protocol' (i : ST.party) (x : ST.public_input) (vi : ST.view) : ST.out_msgs =
                                                                                              (local_protocol'' i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi) (ST.rounds x) (ST.rounds x))
    let local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                 (let (outs) = (local_protocol' i x vi) in
                                                                                                                  (let (out) = (local_protocol_end i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi)) in
                                                                                                                   (outs , out)))
    let protocol_round (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.pmsgs) ST.P.arrayN =
                                                                                                                                                                                         (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                                          (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_round i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol_end (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                                                                                           (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                            (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_end i x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (round1 : ST.round) (d : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (List.Iota.iota_ round1 d))
    let protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (rounds : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (AuxList.iseq rounds))
    let protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (ST.in_msgs) ST.pmap =
                                                                                                                                  (protocol'' x ws rs (ST.pprempty (ST.rounds x) (Pervasive.witness)) (ST.rounds x))
    let protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                            (let (ins) = (protocol' x ws rs) in
                                                                                                                                                                                                             (let (outs) = (protocol_end x ws rs ins) in
                                                                                                                                                                                                              (let (tr) = (ST.P.zip3 ws ins rs) in
                                                                                                                                                                                                               (tr , outs))))
    let get_view_in_msgs (j : ST.party) (vi : ST.view) : ST.rmsgs =
                                                                      (ST.P.get (Aux.snd3 vi) j)
    let get_view_out_msgs (i : ST.party) (j : ST.party) (x : ST.public_input) (vi : ST.view) : ST.rmsgs =
                                                                                                            (ST.P.get (local_protocol' i x vi) j)
    let consistent_inputs (wij : _Gate) (i : NextMsgMaurerAPI.MaurerAPI.pid) (j : NextMsgMaurerAPI.MaurerAPI.pid) (si : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) (sj : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) : Pervasive.bool =
                                                                                                                                                                                                                                                                                                       (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.add_valid_share wij si) (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.add_valid_share wij sj) (NextMsgMaurerAPI.MaurerAPI.consistent_shares i j si sj)))
    let consistent_rands (x : _Gate) (_ : ST.party) (_ : ST.party) (ri : GT.local_rand) (rj : GT.local_rand) : Pervasive.bool =
                                                                                                                                  (Pervasive._and (gate_valid_rand x ri) (gate_valid_rand x rj))
    let valid_inputs (x : ST.public_input) (ws : (ST.local_input) ST.pmap) : Pervasive.bool =
                                                                                                (Pervasive.witness)
    let valid_rands (x : ST.public_input) (ws : (ST.local_rand) ST.pmap) : Pervasive.bool =
                                                                                              (Pervasive.witness)
    let consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                (Pervasive._and (ST.eq_rmsgs (get_view_in_msgs j vi) (get_view_out_msgs j i x vj)) (Pervasive._and (Pervasive.eq (get_view_in_msgs i vj) (get_view_out_msgs i j x vi)) (Pervasive._and (consistent_inputs x i j (Aux.fst3 vi) (Aux.fst3 vj)) (consistent_rands x i j (Aux.thr3 vi) (Aux.thr3 vj)))))
    let consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                    (Pervasive.witness)
    let pairwise_consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                         (Pervasive._and (ST.valid_view x vi) (Pervasive._and (ST.valid_view x vj) (consistent_views x i j vi vj)))
    let pairwise_consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                             (Pervasive.witness)
    let view_output (i : ST.party) (x : ST.public_input) (v : ST.view) : ST.local_output =
                                                                                             (local_protocol_end i x (Aux.fst3 v) (Aux.thr3 v) (Aux.snd3 v))
    let view_outputs (x : ST.public_input) (vs : (ST.view) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                        (ST.P.imap (fun (i : ST.party) (v : ST.view) -> (view_output i x v)) vs)
    let stateful_consistent_outputs : (ST.public_input -> (ST.party -> (ST.party -> (ST.local_output -> (ST.local_output -> Pervasive.bool))))) = Pervasive.witness
    type local_state2 = (local_state * local_state)
    let stateful_consistent_views_outputs_round (r : ST.round) (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : ((local_state * local_state) * Pervasive.bool) =
                                                                                                                                                                                                                                                                                     (let (outs1) = (from_local_messages (stateful_local_protocol_round i r x (Aux.fst3 sts))) in
                                                                                                                                                                                                                                                                                      (let (outs2) = (from_local_messages (stateful_local_protocol_round j r x (snd sts))) in
                                                                                                                                                                                                                                                                                       (let (in1) = (ST.prget ins1 r) in
                                                                                                                                                                                                                                                                                        (let (in2) = (ST.prget ins2 r) in
                                                                                                                                                                                                                                                                                         (let (sts1') = (update_local_state i r x inp1 (to_local_messages in1) (Aux.fst3 sts)) in
                                                                                                                                                                                                                                                                                          (let (sts2') = (update_local_state j r x inp2 (to_local_messages in2) (snd sts)) in
                                                                                                                                                                                                                                                                                           (let (b) = (Pervasive._and (ST.eq_msg (ST.P.get outs1 j) (ST.P.get in2 i)) (ST.eq_msg (ST.P.get outs2 i) (ST.P.get in1 j))) in
                                                                                                                                                                                                                                                                                            ((sts1' , sts2') , b))))))))
    let stateful_consistent_views_outputs''' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) (rounds : (ST.round) List.list) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                                                    (let (go) = (fun (stb : (local_state2 * Pervasive.bool)) (r : ST.round) -> (let (stb') = (stateful_consistent_views_outputs_round r x i j inp1 inp2 ins1 ins2 (fst stb)) in
                                                                                                                                                                                                                                                                                                                                                                ((fst stb') , (Pervasive._and (snd stb) (snd stb'))))) in
                                                                                                                                                                                                                                                                                     (List.foldl go (sts , (Pervasive._true)) rounds))
    let stateful_consistent_views_outputs'' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                   (stateful_consistent_views_outputs''' x i j inp1 inp2 ins1 ins2 sts (AuxList.iseq (ST.rounds x)))
    let stateful_consistent_views_outputs' (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                   (let (st1) = (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) in
                                                                                                                                                                    (let (st2) = (init_local_state j x (Aux.fst3 vj) (Aux.thr3 vj)) in
                                                                                                                                                                     (let (outsb) = (stateful_consistent_views_outputs'' x i j (Aux.fst3 vi) (Aux.fst3 vj) (Aux.snd3 vi) (Aux.snd3 vj) (st1 , st2)) in
                                                                                                                                                                      outsb)))
    let stateful_consistent_views_outputs (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                                 (let (outsb) = (stateful_consistent_views_outputs' x i j vi vj) in
                                                                                                                                                  (let (outs1) = (Aux.fst3 (fst outsb)) in
                                                                                                                                                   (let (outs2) = (snd (fst outsb)) in
                                                                                                                                                    (let (b) = (snd outsb) in
                                                                                                                                                     (let (out1) = (stateful_local_protocol_end i x outs1) in
                                                                                                                                                      (let (out2) = (stateful_local_protocol_end j x outs2) in
                                                                                                                                                       (Pervasive._and b (stateful_consistent_outputs x i j out1 out2))))))))
    let g_protocol (x : _Gate) (ws : (share) GT.pmap) (cs : (GT.local_rand) GT.pmap) : (((share * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))) GT.P.arrayN * (share) GT.P.arrayN) =
                                                                                                                                                                                                             (let (outs) = (GT.P.imap (fun (i : GT.party) (wc : (share * GT.local_rand)) -> (local_gate_start i x (fst wc) (snd wc))) (GT.P.zip ws cs)) in
                                                                                                                                                                                                              (let (ins) = (send_messages outs) in
                                                                                                                                                                                                               (let (o) = (GT.P.imap (fun (i : GT.party) (wi : (share * local_in_msgs)) -> (local_gate_end i x (fst wi) (snd wi))) (GT.P.zip ws ins)) in
                                                                                                                                                                                                                (let (rins) = (GT.P.map (fun (bin : local_messages) -> (GT.P.map (fun (msg : GT.msg) -> (NextMsgArray.Array.init (Pervasive.mk_int 1) (fun (j : Pervasive.int) -> if (Pervasive.eq j (Pervasive.mk_int 0)) then msg else (Pervasive.witness)))) (from_local_messages bin))) ins) in
                                                                                                                                                                                                                 (let (tr) = (GT.P.zip3 ws rins cs) in
                                                                                                                                                                                                                  (tr , o))))))
end
module MaurerSMul = struct
    type _Gate = (NextMsgMaurerAPI.MaurerAPI.wid * (NextMsgMaurerAPI.MaurerAPI.wid * NextMsgMaurerAPI.MaurerAPI.wid))
    type share = (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)
    type local_msgs = Pervasive.unit
    type local_in_msgs = local_msgs
    type local_out_msgs = local_msgs
    module GT = struct
        type public_input = _Gate
        module P = struct
            let rec size : Pervasive.int =
                                             (NextMsgMaurerP.MaurerP.size)
            type ('a) arrayN = ('a) NextMsgMaurerP.MaurerP.arrayN
            let rec get : (('a) Aux.array5 -> (Pervasive.int -> 'a)) =
                                                                         (NextMsgMaurerP.MaurerP.get)
            let rec set : (('a) Aux.array5 -> (Pervasive.int -> ('a -> ('a * ('a * ('a * ('a) Aux.array2)))))) =
                                                                                                                   (NextMsgMaurerP.MaurerP.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a * ('a * ('a * ('a * 'a))))) =
                                                                                         (NextMsgMaurerP.MaurerP.init)
            let rec of_list : (('a) List.list -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                         (NextMsgMaurerP.MaurerP.of_list)
            let rec to_list : (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) List.list) =
                                                                                         (NextMsgMaurerP.MaurerP.to_list)
            let rec to_assoc : (('a) NextMsgMaurerP.MaurerP.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                                            (NextMsgMaurerP.MaurerP.to_assoc)
            let rec create : ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                            (NextMsgMaurerP.MaurerP.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                              (NextMsgMaurerP.MaurerP.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('b) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                             (NextMsgMaurerP.MaurerP.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> (('b) NextMsgMaurerP.MaurerP.arrayN -> ('c) NextMsgMaurerP.MaurerP.arrayN))) =
                                                                                                                                                                           (NextMsgMaurerP.MaurerP.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                                           (NextMsgMaurerP.MaurerP.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool)) =
                                                                                                                                    (NextMsgMaurerP.MaurerP.all)
            let rec allsame : (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool) =
                                                                                         (NextMsgMaurerP.MaurerP.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) NextMsgMaurerP.MaurerP.arrayN) List.list -> (('b) List.list) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                                                                    (NextMsgMaurerP.MaurerP.concat)
        end
        let parties : Pervasive.int =
                                        (P.size)
        type party = Pervasive.int
        let partyset : NextMsgISet.ISet.iset =
                                                 (NextMsgISet.ISet.iset (parties))
        type round = Pervasive.int
        let rounds (_ : public_input) : Pervasive.int =
                                                          (Pervasive.mk_int 1)
        let roundset (p : public_input) : NextMsgISet.ISet.iset =
                                                                    (NextMsgISet.ISet.iset (rounds p))
        type ('a) pmap = ('a) P.arrayN
        type ('a) rmap = ('a) NextMsgArray.Array.array
        type ('a) prmap = (('a) rmap) pmap
        type ('a) ppmap = (('a) pmap) pmap
        type ('a) pprmap = (('a) rmap) ppmap
        type local_input = share
        type local_output = share
        type local_rand = Pervasive.unit
        type msg = Pervasive.unit
        type pmsgs = (msg) pmap
        type rmsgs = (msg) rmap
        type prmsgs = (rmsgs) pmap
        type ppmsgs = (pmsgs) pmap
        type pprmsgs = (prmsgs) pmap
        type in_msgs = prmsgs
        type out_msgs = prmsgs
        type view = (local_input * (in_msgs * local_rand))
        type trace = (view) pmap
        let eq_msg (_ : msg) (_ : msg) : Pervasive.bool =
                                                            (Pervasive._true)
        let eq_pmsgs (m1 : pmsgs) (m2 : pmsgs) : Pervasive.bool =
                                                                    (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (P.get m1 i) (P.get m2 i))) (P.size))
        let eq_rmsgs (m1 : rmsgs) (m2 : rmsgs) : Pervasive.bool =
                                                                    (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size m1) (NextMsgArray.Array.size m2)) (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (NextMsgArray.Array.get m1 i) (NextMsgArray.Array.get m2 i))) (NextMsgArray.Array.size m1)))
        let pinit (f : (party -> 'a)) : ('a) P.arrayN =
                                                          (P.init f)
        let ppinit (f : (party -> (party -> 'a))) : (('a) P.arrayN) P.arrayN =
                                                                                 (pinit (fun (i : party) -> (pinit (f i))))
        let prempty (sz : Pervasive.int) (v : 'a) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                 (pinit (fun (_ : party) -> (NextMsgArray.Array.create sz v)))
        let pprempty (sz : Pervasive.int) (v : 'a) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                             (ppinit (fun (_ : party) (_ : party) -> (NextMsgArray.Array.create sz v)))
        let ppswap (m : ('a) ppmap) : (('a) P.arrayN) P.arrayN =
                                                                   (ppinit (fun (j : Pervasive.int) (i : Pervasive.int) -> (P.get (P.get m i) j)))
        let prget (xs : ('a) prmap) (r : round) : ('a) P.arrayN =
                                                                    (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.get (P.get xs i) r)))
        let pprget (xs : ('a) pprmap) (r : round) : (('a) P.arrayN) P.arrayN =
                                                                                 (ppinit (fun (i : Pervasive.int) (j : Pervasive.int) -> (NextMsgArray.Array.get (P.get (P.get xs i) j) r)))
        let prset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.merge (fun (x0 : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set x0 n y)) xs x)
        let prext (sz : Pervasive.int) (xs : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.init sz (fun (j : Pervasive.int) -> if (Pervasive._and (Int.le (Pervasive.mk_int 0) j) (Int.lt j (NextMsgArray.Array.size (P.get xs i)))) then (NextMsgArray.Array.get (P.get xs i) j) else (Pervasive.witness)))))
        let prextset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                          (prset (prext (Int.plus n (Pervasive.mk_int 1)) xs) n x)
        let pprset (xs : ('a) pprmap) (n : round) (x : ('a) ppmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                             (P.merge (P.merge (fun (ys : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set ys n y))) xs x)
        let prfilter (p : (round -> Pervasive.bool)) (ins : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) ins)
        let pprfilter (p : (round -> Pervasive.bool)) (ins : ('a) pprmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                                    (P.map (fun (xs : (('a) NextMsgArray.Array.array) P.arrayN) -> (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) xs)) ins)
        let rdom (sz : Pervasive.int) (round : round) (xs : ('a) rmap) : Pervasive.bool =
                                                                                            (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size xs) sz) (Pervasive.witness))
        let prdom (sz : Pervasive.int) (round : round) (xs : ('a) prmap) : Pervasive.bool =
                                                                                              (P.all (fun (_ : Pervasive.int) -> (rdom sz round)) xs)
        let pprdom (sz : Pervasive.int) (round : round) (xs : ('a) pprmap) : Pervasive.bool =
                                                                                                (P.all (fun (_ : Pervasive.int) -> (prdom sz round)) xs)
        let rlist (sz : Pervasive.int) (xs : ('a) List.list) : ('a) NextMsgArray.Array.array =
                                                                                                 (List.foldl (fun (rs : ('a) NextMsgArray.Array.array) (i : Pervasive.int) -> (NextMsgArray.Array.set rs i (List.nth (Pervasive.witness) xs i))) (NextMsgArray.Array.create sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let prlist (sz : Pervasive.int) (xs : (pmsgs) List.list) : (msg) prmap =
                                                                                   (List.foldl (fun (rs : (msg) prmap) (i : Pervasive.int) -> (prset rs i (List.nth (Pervasive.witness) xs i))) (prempty sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let pcons (x : ('a) pmap) (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                               (P.merge (fun (x0 : 'a) (xs0 : ('a) List.list) -> (AuxList.cons x0 xs0)) x xs)
        let phead (xs : (('a) List.list) pmap) : ('a) P.arrayN =
                                                                   (P.map (List.head (Pervasive.witness)) xs)
        let pbehead (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                 (P.map (List.behead) xs)
        let prcons (xs : (('a) List.list) pmap) (x : ('a) pmap) : (('a) List.list) P.arrayN =
                                                                                                (P.merge (List.rcons) xs x)
        let pcat (xs : (('a) List.list) pmap) (ys : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                                           (P.merge (fun (x : ('a) List.list) (y : ('a) List.list) -> (AuxList.cat x y)) xs ys)
        let ppcons (x : ('a) ppmap) (xs : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                             (P.merge (pcons) x xs)
        let pprcons (xs : (('a) List.list) ppmap) (x : ('a) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                              (P.merge (prcons) xs x)
        let ppcat (xs : (('a) List.list) ppmap) (ys : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                                         (P.merge (pcat) xs ys)
        let prmsgs_up_to (round : round) (ins : prmsgs) : ((msg) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (prfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let pprmsgs_up_to (round : round) (ins : pprmsgs) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                     (pprfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let get_trace_inputs (tr : trace) : (local_input) P.arrayN =
                                                                       (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.fst3 x)) tr)
        let get_trace_in_msgs (tr : trace) : (in_msgs) P.arrayN =
                                                                    (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.snd3 x)) tr)
        let get_trace_rands (tr : trace) : (local_rand) P.arrayN =
                                                                     (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.thr3 x)) tr)
        let get_view (i : party) (tr : trace) : view =
                                                         (P.get tr i)
        let get_trace_in_msgs_round (round : round) (tr : trace) : ((msg) P.arrayN) P.arrayN =
                                                                                                 (pprget (get_trace_in_msgs tr) round)
        let get_view_in_msgs_round (round : round) (v : view) : (msg) P.arrayN =
                                                                                   (prget (Aux.snd3 v) round)
        let add_view_in_msgs (r : round) (ins : pmsgs) (v : view) : (local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand)) =
                                                                                                                                                 ((Aux.fst3 v) , ((prset (Aux.snd3 v) r ins) , (Aux.thr3 v)))
        let get_trace_in_msgs_up_to (round : round) (tr : trace) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                            (pprmsgs_up_to round (get_trace_in_msgs tr))
        let add_trace_in_msgs (r : round) (ins : ppmsgs) (tr : trace) : ((local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand))) P.arrayN =
                                                                                                                                                                (P.map (fun (ins_v : (pmsgs * view)) -> (add_view_in_msgs r (Aux.fst3 ins_v) (snd ins_v))) (P.zip ins tr))
        let valid_trace (x : public_input) (tr : trace) : Pervasive.bool =
                                                                             (pprdom (rounds x) (rounds x) (get_trace_in_msgs tr))
        let valid_view (x : public_input) (v : view) : Pervasive.bool =
                                                                          (prdom (rounds x) (rounds x) (Aux.snd3 v))
    end
    let local_gate_start (_ : GT.party) (_ : _Gate) (_ : share) (_ : GT.local_rand) : Pervasive.unit =
                                                                                                         (Pervasive.tt)
    let local_gate_end (_ : GT.party) (wij : _Gate) (st : share) (_ : local_in_msgs) : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) =
                                                                                                                                                                    ((NextMsgMaurerAPI.MaurerAPI.smul (Aux.nth1_3 wij) (Aux.nth2_3 wij) (fst st)) , (snd st))
    let gate_valid_rand (_ : _Gate) (_ : GT.local_rand) : Pervasive.bool =
                                                                             (Pervasive._true)
    let gate_valid_rands (x : _Gate) (cs : (GT.local_rand) GT.P.arrayN) : Pervasive.bool =
                                                                                             (GT.P.all (fun (_ : Pervasive.int) (c : GT.local_rand) -> (gate_valid_rand x c)) cs)
    module ST = struct
        type public_input = GT.public_input
        module P = struct
            let rec size : Pervasive.int =
                                             (GT.P.size)
            type ('a) arrayN = ('a) GT.P.arrayN
            let rec get : (('a) GT.P.arrayN -> (Pervasive.int -> 'a)) =
                                                                          (GT.P.get)
            let rec set : (('a) GT.P.arrayN -> (Pervasive.int -> ('a -> ('a) GT.P.arrayN))) =
                                                                                                (GT.P.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a) GT.P.arrayN) =
                                                                           (GT.P.init)
            let rec of_list : (('a) List.list -> ('a) GT.P.arrayN) =
                                                                       (GT.P.of_list)
            let rec to_list : (('a) GT.P.arrayN -> ('a) List.list) =
                                                                       (GT.P.to_list)
            let rec to_assoc : (('a) GT.P.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                          (GT.P.to_assoc)
            let rec create : ('a -> ('a) GT.P.arrayN) =
                                                          (GT.P.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) GT.P.arrayN)) =
                                                                            (GT.P.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) GT.P.arrayN -> ('b) GT.P.arrayN)) =
                                                                                                         (GT.P.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) GT.P.arrayN -> (('b) GT.P.arrayN -> ('c) GT.P.arrayN))) =
                                                                                                                     (GT.P.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) GT.P.arrayN -> ('a) GT.P.arrayN)) =
                                                                                                                       (GT.P.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) GT.P.arrayN -> Pervasive.bool)) =
                                                                                                                  (GT.P.all)
            let rec allsame : (('a) GT.P.arrayN -> Pervasive.bool) =
                                                                       (GT.P.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) GT.P.arrayN) List.list -> (('b) List.list) GT.P.arrayN) =
                                                                                                (GT.P.concat)
        end
        let rec parties : Pervasive.int =
                                            (GT.parties)
        type party = GT.party
        let rec partyset : NextMsgISet.ISet.iset =
                                                     (GT.partyset)
        type round = GT.round
        let rec rounds : (GT.public_input -> Pervasive.int) =
                                                                (GT.rounds)
        let rec roundset : (GT.public_input -> NextMsgISet.ISet.iset) =
                                                                          (GT.roundset)
        type ('a) pmap = ('a) GT.pmap
        type ('a) rmap = ('a) GT.rmap
        type ('a) prmap = ('a) GT.prmap
        type ('a) ppmap = ('a) GT.ppmap
        type ('a) pprmap = ('a) GT.pprmap
        type local_input = GT.local_input
        type local_output = GT.local_output
        type local_rand = GT.local_rand
        type msg = GT.msg
        type pmsgs = GT.pmsgs
        type rmsgs = GT.rmsgs
        type prmsgs = GT.prmsgs
        type ppmsgs = GT.ppmsgs
        type pprmsgs = GT.pprmsgs
        type in_msgs = GT.in_msgs
        type out_msgs = GT.out_msgs
        type view = GT.view
        type trace = GT.trace
        let rec eq_msg : (GT.msg -> (GT.msg -> Pervasive.bool)) =
                                                                    (GT.eq_msg)
        let rec eq_pmsgs : (GT.pmsgs -> (GT.pmsgs -> Pervasive.bool)) =
                                                                          (GT.eq_pmsgs)
        let rec eq_rmsgs : (GT.rmsgs -> (GT.rmsgs -> Pervasive.bool)) =
                                                                          (GT.eq_rmsgs)
        let rec pinit : ((GT.party -> 'a) -> ('a) GT.P.arrayN) =
                                                                   (GT.pinit)
        let rec ppinit : ((GT.party -> (GT.party -> 'a)) -> (('a) GT.P.arrayN) GT.P.arrayN) =
                                                                                                (GT.ppinit)
        let rec prempty : (Pervasive.int -> ('a -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                     (GT.prempty)
        let rec pprempty : (Pervasive.int -> ('a -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                    (GT.pprempty)
        let rec ppswap : (('a) GT.ppmap -> (('a) GT.P.arrayN) GT.P.arrayN) =
                                                                               (GT.ppswap)
        let rec prget : (('a) GT.prmap -> (GT.round -> ('a) GT.P.arrayN)) =
                                                                              (GT.prget)
        let rec pprget : (('a) GT.pprmap -> (GT.round -> (('a) GT.P.arrayN) GT.P.arrayN)) =
                                                                                              (GT.pprget)
        let rec prset : (('a) GT.prmap -> (Pervasive.int -> (('a) GT.pmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN))) =
                                                                                                                                (GT.prset)
        let rec prext : (Pervasive.int -> (('a) GT.prmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                              (GT.prext)
        let rec prextset : (('a) GT.prmap -> (Pervasive.int -> (('a) GT.pmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN))) =
                                                                                                                                   (GT.prextset)
        let rec pprset : (('a) GT.pprmap -> (GT.round -> (('a) GT.ppmap -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN))) =
                                                                                                                                            (GT.pprset)
        let rec prfilter : ((GT.round -> Pervasive.bool) -> (('a) GT.prmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                                                (GT.prfilter)
        let rec pprfilter : ((GT.round -> Pervasive.bool) -> (('a) GT.pprmap -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                                (GT.pprfilter)
        let rec rdom : (Pervasive.int -> (GT.round -> (('a) GT.rmap -> Pervasive.bool))) =
                                                                                             (GT.rdom)
        let rec prdom : (Pervasive.int -> (GT.round -> (('a) GT.prmap -> Pervasive.bool))) =
                                                                                               (GT.prdom)
        let rec pprdom : (Pervasive.int -> (GT.round -> (('a) GT.pprmap -> Pervasive.bool))) =
                                                                                                 (GT.pprdom)
        let rec rlist : (Pervasive.int -> (('a) List.list -> ('a) NextMsgArray.Array.array)) =
                                                                                                 (GT.rlist)
        let rec prlist : (Pervasive.int -> ((GT.pmsgs) List.list -> (GT.msg) GT.prmap)) =
                                                                                            (GT.prlist)
        let rec pcons : (('a) GT.pmap -> ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                         (GT.pcons)
        let rec phead : ((('a) List.list) GT.pmap -> ('a) GT.P.arrayN) =
                                                                           (GT.phead)
        let rec pbehead : ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN) =
                                                                                         (GT.pbehead)
        let rec prcons : ((('a) List.list) GT.pmap -> (('a) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                          (GT.prcons)
        let rec pcat : ((('a) List.list) GT.pmap -> ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                                    (GT.pcat)
        let rec ppcons : (('a) GT.ppmap -> ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                          (GT.ppcons)
        let rec pprcons : ((('a) List.list) GT.ppmap -> (('a) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                           (GT.pprcons)
        let rec ppcat : ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                     (GT.ppcat)
        let rec prmsgs_up_to : (GT.round -> (GT.prmsgs -> ((GT.msg) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                                (GT.prmsgs_up_to)
        let rec pprmsgs_up_to : (GT.round -> (GT.pprmsgs -> (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                (GT.pprmsgs_up_to)
        let rec get_trace_inputs : (GT.trace -> (GT.local_input) GT.P.arrayN) =
                                                                                  (GT.get_trace_inputs)
        let rec get_trace_in_msgs : (GT.trace -> (GT.in_msgs) GT.P.arrayN) =
                                                                               (GT.get_trace_in_msgs)
        let rec get_trace_rands : (GT.trace -> (GT.local_rand) GT.P.arrayN) =
                                                                                (GT.get_trace_rands)
        let rec get_view : (GT.party -> (GT.trace -> GT.view)) =
                                                                   (GT.get_view)
        let rec get_trace_in_msgs_round : (GT.round -> (GT.trace -> ((GT.msg) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                             (GT.get_trace_in_msgs_round)
        let rec get_view_in_msgs_round : (GT.round -> (GT.view -> (GT.msg) GT.P.arrayN)) =
                                                                                             (GT.get_view_in_msgs_round)
        let rec add_view_in_msgs : (GT.round -> (GT.pmsgs -> (GT.view -> (GT.local_input * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))))) =
                                                                                                                                                                     (GT.add_view_in_msgs)
        let rec get_trace_in_msgs_up_to : (GT.round -> (GT.trace -> (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                        (GT.get_trace_in_msgs_up_to)
        let rec add_trace_in_msgs : (GT.round -> (GT.ppmsgs -> (GT.trace -> ((GT.local_input * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))) GT.P.arrayN))) =
                                                                                                                                                                                      (GT.add_trace_in_msgs)
        let rec valid_trace : (GT.public_input -> (GT.trace -> Pervasive.bool)) =
                                                                                    (GT.valid_trace)
        let rec valid_view : (GT.public_input -> (GT.view -> Pervasive.bool)) =
                                                                                  (GT.valid_view)
    end
    type local_messages = local_msgs
    type messages = (local_messages) ST.pmap
    type local_out_messages = local_messages
    type local_in_messages = local_messages
    type out_messages = messages
    type in_messages = messages
    let rec from_local_messages : (MaurerAdd.local_messages -> (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * Pervasive.unit))))) =
                                                                                                                                                               (MaurerAdd.from_local_messages)
    let rec to_local_messages : (MaurerAdd.ST.pmsgs -> Pervasive.unit) =
                                                                           (MaurerAdd.to_local_messages)
    let rec send_messages : (MaurerAdd.out_messages -> (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * Pervasive.unit))))) =
                                                                                                                                                       (MaurerAdd.send_messages)
    let from_messages (xs : (local_messages) ST.P.arrayN) : (ST.pmsgs) ST.P.arrayN =
                                                                                       (ST.P.map (from_local_messages) xs)
    let to_messages (xs : (ST.pmsgs) ST.P.arrayN) : (local_messages) ST.P.arrayN =
                                                                                     (ST.P.map (to_local_messages) xs)
    let valid_local_messages (_ : ST.public_input) (_ : ST.round) (_ : local_messages) : Pervasive.bool =
                                                                                                            (Pervasive._true)
    let valid_messages (p : ST.public_input) (r : ST.round) (ms : messages) : Pervasive.bool =
                                                                                                 (ST.P.all (fun (_ : Pervasive.int) -> (valid_local_messages p r)) ms)
    let valid_msg (_ : ST.public_input) (_ : ST.round) (_ : ST.msg) : Pervasive.bool =
                                                                                         (Pervasive._true)
    let valid_pmsgs (p : ST.public_input) (r : ST.round) (ms : ST.pmsgs) : Pervasive.bool =
                                                                                              (ST.P.all (fun (_ : Pervasive.int) -> (valid_msg p r)) ms)
    let valid_ppmsgs (p : ST.public_input) (r : ST.round) (ms : ST.ppmsgs) : Pervasive.bool =
                                                                                                (ST.P.all (fun (_ : Pervasive.int) -> (valid_pmsgs p r)) ms)
    type local_state = (share * (GT.local_rand, local_in_msgs) Aux.either)
    let init_local_state (_ : ST.party) (_ : ST.public_input) (wis : share) (ris : ST.local_rand) : (share * (ST.local_rand, local_in_msgs) Aux.either) =
                                                                                                                                                            (wis , (Aux.L ris))
    let update_local_state (_ : ST.party) (_ : ST.round) (_ : ST.public_input) (_ : ST.local_input) (ins : local_in_messages) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : (share * (GT.local_rand, local_in_messages) Aux.either) =
                                                                                                                                                                                                                                                       ((fst st) , (Aux.R ins))
    let get_local_state (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : local_state =
                                                                                                                                                             (let (go) = (fun (st : local_state) (r0 : ST.round) -> (let (insr) = (ST.prget insi r0) in
                                                                                                                                                                                                                     (update_local_state i r0 x wi (to_local_messages insr) st))) in
                                                                                                                                                              (List.foldl go (init_local_state i x wi ri) (AuxList.iseq r)))
    type state = (local_state) ST.pmap
    let init_state (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                        (ST.P.imap (fun (i : ST.party) (wi_ri : (ST.local_input * ST.local_rand)) -> (init_local_state i x (fst wi_ri) (snd wi_ri))) (ST.P.zip ws rs))
    let update_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (local_in_messages) ST.pmap) (st : state) : (local_state) ST.P.arrayN =
                                                                                                                                                                               (ST.P.imap (fun (i : ST.party) (wsi_insi_sti : (ST.local_input * (local_in_messages * local_state))) -> (update_local_state i round x (Aux.fst3 wsi_insi_sti) (Aux.snd3 wsi_insi_sti) (Aux.thr3 wsi_insi_sti))) (ST.P.zip3 ws ins st))
    let get_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                                                                       (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (get_local_state i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) (ST.P.zip3 ws rs ins))
    let stateful_local_protocol_round (i : GT.party) (_ : ST.round) (g : _Gate) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : local_out_msgs =
                                                                                                                                                                (local_gate_start i g (fst st) (Aux.unL (snd st)))
    let stateful_local_protocol_end (i : GT.party) (g : _Gate) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : share =
                                                                                                                                      (local_gate_end i g (fst st) (Aux.unR (snd st)))
    let stateful_local_protocol''' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : (ST.round) List.list) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                                            (List.foldl (fun (acc : (local_state * ST.out_msgs)) (round : ST.round) -> (let (outs') = (ST.prset (snd acc) round (from_local_messages (stateful_local_protocol_round i round x (Aux.fst3 acc)))) in
                                                                                                                                                                                                                                                                                                        (let (st') = (update_local_state i round x inp (to_local_messages (ST.prget ins round)) (Aux.fst3 acc)) in
                                                                                                                                                                                                                                                                                                         (st' , outs')))) (st , (ST.prempty sz (Pervasive.witness))) rounds)
    let stateful_local_protocol'' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                               (stateful_local_protocol''' i x inp st ins sz (AuxList.iseq rounds))
    let stateful_local_protocol' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) : (local_state * ST.out_msgs) =
                                                                                                                                                                     (stateful_local_protocol'' i x inp st ins (ST.rounds x) (ST.rounds x))
    let stateful_local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                          (let (outs) = (stateful_local_protocol' i x (Aux.fst3 vi) (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) (Aux.snd3 vi)) in
                                                                                                                           (let (out) = (stateful_local_protocol_end i x (Aux.fst3 outs)) in
                                                                                                                            ((snd outs) , out)))
    let stateful_protocol_round (round : ST.round) (x : ST.public_input) (st : state) : (local_out_messages) ST.P.arrayN =
                                                                                                                             (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_round i round x sti)) st)
    let stateful_protocol_end (x : ST.public_input) (st : state) : (ST.local_output) ST.P.arrayN =
                                                                                                     (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_end i x sti)) st)
    let stateful_protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : (ST.round) List.list) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                                  (List.foldl (fun (ins_st : ((ST.in_msgs) ST.pmap * state)) (round : ST.round) -> (let (ins0) = (Aux.fst3 ins_st) in
                                                                                                                                                                                                                                                                                    (let (st0) = (snd ins_st) in
                                                                                                                                                                                                                                                                                     (let (outs) = (send_messages (stateful_protocol_round round x st0)) in
                                                                                                                                                                                                                                                                                      ((ST.pprset ins0 round (from_messages outs)) , (update_state round x ws outs st0)))))) (ins , st) rounds)
    let stateful_protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : ST.round) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                     (stateful_protocol''' x ws ins st (AuxList.iseq rounds))
    let stateful_protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                     (stateful_protocol'' x ws (ST.pprempty (ST.rounds x) (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                     (let (ins_st') = (stateful_protocol' x ws rs) in
                                                                                                                                                                                                                      (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                       (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                        (tr , outs))))
    let stateful_protocol_sz' (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                             (stateful_protocol'' x ws (ST.pprempty sz (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol_sz (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                                             (let (ins_st') = (stateful_protocol_sz' sz x ws rs) in
                                                                                                                                                                                                                                              (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                                               (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                                                (tr , outs))))
    let local_protocol_round (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.pmsgs =
                                                                                                                                                               (from_local_messages (stateful_local_protocol_round i r x (get_local_state i r x wi ri insi)))
    let local_protocol_end (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.local_output =
                                                                                                                                                     (stateful_local_protocol_end i x (get_local_state i (ST.rounds x) x wi ri insi))
    let local_protocol'' (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : ST.out_msgs =
                                                                                                                                                                                       (List.foldl (fun (outs : ST.out_msgs) (round : Pervasive.int) -> (ST.prset outs round (local_protocol_round i round x wi ri ins))) (ST.prempty sz (Pervasive.witness)) (AuxList.iseq rounds))
    let local_protocol' (i : ST.party) (x : ST.public_input) (vi : ST.view) : ST.out_msgs =
                                                                                              (local_protocol'' i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi) (ST.rounds x) (ST.rounds x))
    let local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                 (let (outs) = (local_protocol' i x vi) in
                                                                                                                  (let (out) = (local_protocol_end i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi)) in
                                                                                                                   (outs , out)))
    let protocol_round (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.pmsgs) ST.P.arrayN =
                                                                                                                                                                                         (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                                          (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_round i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol_end (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                                                                                           (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                            (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_end i x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (round1 : ST.round) (d : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (List.Iota.iota_ round1 d))
    let protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (rounds : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (AuxList.iseq rounds))
    let protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (ST.in_msgs) ST.pmap =
                                                                                                                                  (protocol'' x ws rs (ST.pprempty (ST.rounds x) (Pervasive.witness)) (ST.rounds x))
    let protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                            (let (ins) = (protocol' x ws rs) in
                                                                                                                                                                                                             (let (outs) = (protocol_end x ws rs ins) in
                                                                                                                                                                                                              (let (tr) = (ST.P.zip3 ws ins rs) in
                                                                                                                                                                                                               (tr , outs))))
    let get_view_in_msgs (j : ST.party) (vi : ST.view) : ST.rmsgs =
                                                                      (ST.P.get (Aux.snd3 vi) j)
    let get_view_out_msgs (i : ST.party) (j : ST.party) (x : ST.public_input) (vi : ST.view) : ST.rmsgs =
                                                                                                            (ST.P.get (local_protocol' i x vi) j)
    let consistent_inputs (wij : _Gate) (i : NextMsgMaurerAPI.MaurerAPI.pid) (j : NextMsgMaurerAPI.MaurerAPI.pid) (si : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) (sj : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) : Pervasive.bool =
                                                                                                                                                                                                                                                                                                       (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.smul_valid_share wij si) (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.smul_valid_share wij sj) (NextMsgMaurerAPI.MaurerAPI.consistent_shares i j si sj)))
    let consistent_rands (x : _Gate) (_ : ST.party) (_ : ST.party) (ri : GT.local_rand) (rj : GT.local_rand) : Pervasive.bool =
                                                                                                                                  (Pervasive._and (gate_valid_rand x ri) (gate_valid_rand x rj))
    let valid_inputs (x : ST.public_input) (ws : (ST.local_input) ST.pmap) : Pervasive.bool =
                                                                                                (Pervasive.witness)
    let valid_rands (x : ST.public_input) (ws : (ST.local_rand) ST.pmap) : Pervasive.bool =
                                                                                              (Pervasive.witness)
    let consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                (Pervasive._and (ST.eq_rmsgs (get_view_in_msgs j vi) (get_view_out_msgs j i x vj)) (Pervasive._and (Pervasive.eq (get_view_in_msgs i vj) (get_view_out_msgs i j x vi)) (Pervasive._and (consistent_inputs x i j (Aux.fst3 vi) (Aux.fst3 vj)) (consistent_rands x i j (Aux.thr3 vi) (Aux.thr3 vj)))))
    let consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                    (Pervasive.witness)
    let pairwise_consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                         (Pervasive._and (ST.valid_view x vi) (Pervasive._and (ST.valid_view x vj) (consistent_views x i j vi vj)))
    let pairwise_consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                             (Pervasive.witness)
    let view_output (i : ST.party) (x : ST.public_input) (v : ST.view) : ST.local_output =
                                                                                             (local_protocol_end i x (Aux.fst3 v) (Aux.thr3 v) (Aux.snd3 v))
    let view_outputs (x : ST.public_input) (vs : (ST.view) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                        (ST.P.imap (fun (i : ST.party) (v : ST.view) -> (view_output i x v)) vs)
    let stateful_consistent_outputs : (ST.public_input -> (ST.party -> (ST.party -> (ST.local_output -> (ST.local_output -> Pervasive.bool))))) = Pervasive.witness
    type local_state2 = (local_state * local_state)
    let stateful_consistent_views_outputs_round (r : ST.round) (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : ((local_state * local_state) * Pervasive.bool) =
                                                                                                                                                                                                                                                                                     (let (outs1) = (from_local_messages (stateful_local_protocol_round i r x (Aux.fst3 sts))) in
                                                                                                                                                                                                                                                                                      (let (outs2) = (from_local_messages (stateful_local_protocol_round j r x (snd sts))) in
                                                                                                                                                                                                                                                                                       (let (in1) = (ST.prget ins1 r) in
                                                                                                                                                                                                                                                                                        (let (in2) = (ST.prget ins2 r) in
                                                                                                                                                                                                                                                                                         (let (sts1') = (update_local_state i r x inp1 (to_local_messages in1) (Aux.fst3 sts)) in
                                                                                                                                                                                                                                                                                          (let (sts2') = (update_local_state j r x inp2 (to_local_messages in2) (snd sts)) in
                                                                                                                                                                                                                                                                                           (let (b) = (Pervasive._and (ST.eq_msg (ST.P.get outs1 j) (ST.P.get in2 i)) (ST.eq_msg (ST.P.get outs2 i) (ST.P.get in1 j))) in
                                                                                                                                                                                                                                                                                            ((sts1' , sts2') , b))))))))
    let stateful_consistent_views_outputs''' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) (rounds : (ST.round) List.list) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                                                    (let (go) = (fun (stb : (local_state2 * Pervasive.bool)) (r : ST.round) -> (let (stb') = (stateful_consistent_views_outputs_round r x i j inp1 inp2 ins1 ins2 (fst stb)) in
                                                                                                                                                                                                                                                                                                                                                                ((fst stb') , (Pervasive._and (snd stb) (snd stb'))))) in
                                                                                                                                                                                                                                                                                     (List.foldl go (sts , (Pervasive._true)) rounds))
    let stateful_consistent_views_outputs'' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                   (stateful_consistent_views_outputs''' x i j inp1 inp2 ins1 ins2 sts (AuxList.iseq (ST.rounds x)))
    let stateful_consistent_views_outputs' (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                   (let (st1) = (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) in
                                                                                                                                                                    (let (st2) = (init_local_state j x (Aux.fst3 vj) (Aux.thr3 vj)) in
                                                                                                                                                                     (let (outsb) = (stateful_consistent_views_outputs'' x i j (Aux.fst3 vi) (Aux.fst3 vj) (Aux.snd3 vi) (Aux.snd3 vj) (st1 , st2)) in
                                                                                                                                                                      outsb)))
    let stateful_consistent_views_outputs (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                                 (let (outsb) = (stateful_consistent_views_outputs' x i j vi vj) in
                                                                                                                                                  (let (outs1) = (Aux.fst3 (fst outsb)) in
                                                                                                                                                   (let (outs2) = (snd (fst outsb)) in
                                                                                                                                                    (let (b) = (snd outsb) in
                                                                                                                                                     (let (out1) = (stateful_local_protocol_end i x outs1) in
                                                                                                                                                      (let (out2) = (stateful_local_protocol_end j x outs2) in
                                                                                                                                                       (Pervasive._and b (stateful_consistent_outputs x i j out1 out2))))))))
    let g_protocol (x : _Gate) (ws : (share) GT.pmap) (cs : (GT.local_rand) GT.pmap) : (((share * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))) GT.P.arrayN * (share) GT.P.arrayN) =
                                                                                                                                                                                                             (let (outs) = (GT.P.imap (fun (i : GT.party) (wc : (share * GT.local_rand)) -> (local_gate_start i x (fst wc) (snd wc))) (GT.P.zip ws cs)) in
                                                                                                                                                                                                              (let (ins) = (send_messages outs) in
                                                                                                                                                                                                               (let (o) = (GT.P.imap (fun (i : GT.party) (wi : (share * local_in_msgs)) -> (local_gate_end i x (fst wi) (snd wi))) (GT.P.zip ws ins)) in
                                                                                                                                                                                                                (let (rins) = (GT.P.map (fun (bin : local_messages) -> (GT.P.map (fun (msg : GT.msg) -> (NextMsgArray.Array.init (Pervasive.mk_int 1) (fun (j : Pervasive.int) -> if (Pervasive.eq j (Pervasive.mk_int 0)) then msg else (Pervasive.witness)))) (from_local_messages bin))) ins) in
                                                                                                                                                                                                                 (let (tr) = (GT.P.zip3 ws rins cs) in
                                                                                                                                                                                                                  (tr , o))))))
end
module MaurerConst = struct
    type _Gate = (NextMsgMaurerAPI.MaurerAPI.wid * NextMsgMaurerAPI.MaurerAPI._val)
    type share = (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)
    type local_msgs = Pervasive.unit
    type local_in_msgs = local_msgs
    type local_out_msgs = local_msgs
    module GT = struct
        type public_input = _Gate
        module P = struct
            let rec size : Pervasive.int =
                                             (NextMsgMaurerP.MaurerP.size)
            type ('a) arrayN = ('a) NextMsgMaurerP.MaurerP.arrayN
            let rec get : (('a) Aux.array5 -> (Pervasive.int -> 'a)) =
                                                                         (NextMsgMaurerP.MaurerP.get)
            let rec set : (('a) Aux.array5 -> (Pervasive.int -> ('a -> ('a * ('a * ('a * ('a) Aux.array2)))))) =
                                                                                                                   (NextMsgMaurerP.MaurerP.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a * ('a * ('a * ('a * 'a))))) =
                                                                                         (NextMsgMaurerP.MaurerP.init)
            let rec of_list : (('a) List.list -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                         (NextMsgMaurerP.MaurerP.of_list)
            let rec to_list : (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) List.list) =
                                                                                         (NextMsgMaurerP.MaurerP.to_list)
            let rec to_assoc : (('a) NextMsgMaurerP.MaurerP.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                                            (NextMsgMaurerP.MaurerP.to_assoc)
            let rec create : ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                            (NextMsgMaurerP.MaurerP.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                              (NextMsgMaurerP.MaurerP.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('b) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                             (NextMsgMaurerP.MaurerP.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> (('b) NextMsgMaurerP.MaurerP.arrayN -> ('c) NextMsgMaurerP.MaurerP.arrayN))) =
                                                                                                                                                                           (NextMsgMaurerP.MaurerP.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                                           (NextMsgMaurerP.MaurerP.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool)) =
                                                                                                                                    (NextMsgMaurerP.MaurerP.all)
            let rec allsame : (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool) =
                                                                                         (NextMsgMaurerP.MaurerP.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) NextMsgMaurerP.MaurerP.arrayN) List.list -> (('b) List.list) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                                                                    (NextMsgMaurerP.MaurerP.concat)
        end
        let parties : Pervasive.int =
                                        (P.size)
        type party = Pervasive.int
        let partyset : NextMsgISet.ISet.iset =
                                                 (NextMsgISet.ISet.iset (parties))
        type round = Pervasive.int
        let rounds (_ : public_input) : Pervasive.int =
                                                          (Pervasive.mk_int 1)
        let roundset (p : public_input) : NextMsgISet.ISet.iset =
                                                                    (NextMsgISet.ISet.iset (rounds p))
        type ('a) pmap = ('a) P.arrayN
        type ('a) rmap = ('a) NextMsgArray.Array.array
        type ('a) prmap = (('a) rmap) pmap
        type ('a) ppmap = (('a) pmap) pmap
        type ('a) pprmap = (('a) rmap) ppmap
        type local_input = share
        type local_output = share
        type local_rand = Pervasive.unit
        type msg = Pervasive.unit
        type pmsgs = (msg) pmap
        type rmsgs = (msg) rmap
        type prmsgs = (rmsgs) pmap
        type ppmsgs = (pmsgs) pmap
        type pprmsgs = (prmsgs) pmap
        type in_msgs = prmsgs
        type out_msgs = prmsgs
        type view = (local_input * (in_msgs * local_rand))
        type trace = (view) pmap
        let eq_msg (_ : msg) (_ : msg) : Pervasive.bool =
                                                            (Pervasive._true)
        let eq_pmsgs (m1 : pmsgs) (m2 : pmsgs) : Pervasive.bool =
                                                                    (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (P.get m1 i) (P.get m2 i))) (P.size))
        let eq_rmsgs (m1 : rmsgs) (m2 : rmsgs) : Pervasive.bool =
                                                                    (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size m1) (NextMsgArray.Array.size m2)) (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (NextMsgArray.Array.get m1 i) (NextMsgArray.Array.get m2 i))) (NextMsgArray.Array.size m1)))
        let pinit (f : (party -> 'a)) : ('a) P.arrayN =
                                                          (P.init f)
        let ppinit (f : (party -> (party -> 'a))) : (('a) P.arrayN) P.arrayN =
                                                                                 (pinit (fun (i : party) -> (pinit (f i))))
        let prempty (sz : Pervasive.int) (v : 'a) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                 (pinit (fun (_ : party) -> (NextMsgArray.Array.create sz v)))
        let pprempty (sz : Pervasive.int) (v : 'a) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                             (ppinit (fun (_ : party) (_ : party) -> (NextMsgArray.Array.create sz v)))
        let ppswap (m : ('a) ppmap) : (('a) P.arrayN) P.arrayN =
                                                                   (ppinit (fun (j : Pervasive.int) (i : Pervasive.int) -> (P.get (P.get m i) j)))
        let prget (xs : ('a) prmap) (r : round) : ('a) P.arrayN =
                                                                    (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.get (P.get xs i) r)))
        let pprget (xs : ('a) pprmap) (r : round) : (('a) P.arrayN) P.arrayN =
                                                                                 (ppinit (fun (i : Pervasive.int) (j : Pervasive.int) -> (NextMsgArray.Array.get (P.get (P.get xs i) j) r)))
        let prset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.merge (fun (x0 : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set x0 n y)) xs x)
        let prext (sz : Pervasive.int) (xs : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.init sz (fun (j : Pervasive.int) -> if (Pervasive._and (Int.le (Pervasive.mk_int 0) j) (Int.lt j (NextMsgArray.Array.size (P.get xs i)))) then (NextMsgArray.Array.get (P.get xs i) j) else (Pervasive.witness)))))
        let prextset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                          (prset (prext (Int.plus n (Pervasive.mk_int 1)) xs) n x)
        let pprset (xs : ('a) pprmap) (n : round) (x : ('a) ppmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                             (P.merge (P.merge (fun (ys : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set ys n y))) xs x)
        let prfilter (p : (round -> Pervasive.bool)) (ins : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) ins)
        let pprfilter (p : (round -> Pervasive.bool)) (ins : ('a) pprmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                                    (P.map (fun (xs : (('a) NextMsgArray.Array.array) P.arrayN) -> (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) xs)) ins)
        let rdom (sz : Pervasive.int) (round : round) (xs : ('a) rmap) : Pervasive.bool =
                                                                                            (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size xs) sz) (Pervasive.witness))
        let prdom (sz : Pervasive.int) (round : round) (xs : ('a) prmap) : Pervasive.bool =
                                                                                              (P.all (fun (_ : Pervasive.int) -> (rdom sz round)) xs)
        let pprdom (sz : Pervasive.int) (round : round) (xs : ('a) pprmap) : Pervasive.bool =
                                                                                                (P.all (fun (_ : Pervasive.int) -> (prdom sz round)) xs)
        let rlist (sz : Pervasive.int) (xs : ('a) List.list) : ('a) NextMsgArray.Array.array =
                                                                                                 (List.foldl (fun (rs : ('a) NextMsgArray.Array.array) (i : Pervasive.int) -> (NextMsgArray.Array.set rs i (List.nth (Pervasive.witness) xs i))) (NextMsgArray.Array.create sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let prlist (sz : Pervasive.int) (xs : (pmsgs) List.list) : (msg) prmap =
                                                                                   (List.foldl (fun (rs : (msg) prmap) (i : Pervasive.int) -> (prset rs i (List.nth (Pervasive.witness) xs i))) (prempty sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let pcons (x : ('a) pmap) (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                               (P.merge (fun (x0 : 'a) (xs0 : ('a) List.list) -> (AuxList.cons x0 xs0)) x xs)
        let phead (xs : (('a) List.list) pmap) : ('a) P.arrayN =
                                                                   (P.map (List.head (Pervasive.witness)) xs)
        let pbehead (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                 (P.map (List.behead) xs)
        let prcons (xs : (('a) List.list) pmap) (x : ('a) pmap) : (('a) List.list) P.arrayN =
                                                                                                (P.merge (List.rcons) xs x)
        let pcat (xs : (('a) List.list) pmap) (ys : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                                           (P.merge (fun (x : ('a) List.list) (y : ('a) List.list) -> (AuxList.cat x y)) xs ys)
        let ppcons (x : ('a) ppmap) (xs : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                             (P.merge (pcons) x xs)
        let pprcons (xs : (('a) List.list) ppmap) (x : ('a) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                              (P.merge (prcons) xs x)
        let ppcat (xs : (('a) List.list) ppmap) (ys : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                                         (P.merge (pcat) xs ys)
        let prmsgs_up_to (round : round) (ins : prmsgs) : ((msg) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (prfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let pprmsgs_up_to (round : round) (ins : pprmsgs) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                     (pprfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let get_trace_inputs (tr : trace) : (local_input) P.arrayN =
                                                                       (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.fst3 x)) tr)
        let get_trace_in_msgs (tr : trace) : (in_msgs) P.arrayN =
                                                                    (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.snd3 x)) tr)
        let get_trace_rands (tr : trace) : (local_rand) P.arrayN =
                                                                     (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.thr3 x)) tr)
        let get_view (i : party) (tr : trace) : view =
                                                         (P.get tr i)
        let get_trace_in_msgs_round (round : round) (tr : trace) : ((msg) P.arrayN) P.arrayN =
                                                                                                 (pprget (get_trace_in_msgs tr) round)
        let get_view_in_msgs_round (round : round) (v : view) : (msg) P.arrayN =
                                                                                   (prget (Aux.snd3 v) round)
        let add_view_in_msgs (r : round) (ins : pmsgs) (v : view) : (local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand)) =
                                                                                                                                                 ((Aux.fst3 v) , ((prset (Aux.snd3 v) r ins) , (Aux.thr3 v)))
        let get_trace_in_msgs_up_to (round : round) (tr : trace) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                            (pprmsgs_up_to round (get_trace_in_msgs tr))
        let add_trace_in_msgs (r : round) (ins : ppmsgs) (tr : trace) : ((local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand))) P.arrayN =
                                                                                                                                                                (P.map (fun (ins_v : (pmsgs * view)) -> (add_view_in_msgs r (Aux.fst3 ins_v) (snd ins_v))) (P.zip ins tr))
        let valid_trace (x : public_input) (tr : trace) : Pervasive.bool =
                                                                             (pprdom (rounds x) (rounds x) (get_trace_in_msgs tr))
        let valid_view (x : public_input) (v : view) : Pervasive.bool =
                                                                          (prdom (rounds x) (rounds x) (Aux.snd3 v))
    end
    let local_gate_start (_ : GT.party) (_ : _Gate) (_ : share) (_ : GT.local_rand) : Pervasive.unit =
                                                                                                         (Pervasive.tt)
    let local_gate_end (i : NextMsgMaurerAPI.MaurerAPI.pid) (wc : _Gate) (st : share) (_ : local_in_msgs) : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgISet.ISet.iset) =
                                                                                                                                                                             ((NextMsgMaurerAPI.MaurerAPI.cnst i (snd wc) (fst st)) , (NextMsgISet.ISet.add (snd st) (NextMsgMaurerAPI.MaurerAPI.get_wire_st_next (fst st))))
    let gate_valid_rand (_ : _Gate) (_ : GT.local_rand) : Pervasive.bool =
                                                                             (Pervasive._true)
    let gate_valid_rands (x : _Gate) (cs : (GT.local_rand) GT.P.arrayN) : Pervasive.bool =
                                                                                             (GT.P.all (fun (_ : Pervasive.int) (c : GT.local_rand) -> (gate_valid_rand x c)) cs)
    module ST = struct
        type public_input = GT.public_input
        module P = struct
            let rec size : Pervasive.int =
                                             (GT.P.size)
            type ('a) arrayN = ('a) GT.P.arrayN
            let rec get : (('a) GT.P.arrayN -> (Pervasive.int -> 'a)) =
                                                                          (GT.P.get)
            let rec set : (('a) GT.P.arrayN -> (Pervasive.int -> ('a -> ('a) GT.P.arrayN))) =
                                                                                                (GT.P.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a) GT.P.arrayN) =
                                                                           (GT.P.init)
            let rec of_list : (('a) List.list -> ('a) GT.P.arrayN) =
                                                                       (GT.P.of_list)
            let rec to_list : (('a) GT.P.arrayN -> ('a) List.list) =
                                                                       (GT.P.to_list)
            let rec to_assoc : (('a) GT.P.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                          (GT.P.to_assoc)
            let rec create : ('a -> ('a) GT.P.arrayN) =
                                                          (GT.P.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) GT.P.arrayN)) =
                                                                            (GT.P.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) GT.P.arrayN -> ('b) GT.P.arrayN)) =
                                                                                                         (GT.P.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) GT.P.arrayN -> (('b) GT.P.arrayN -> ('c) GT.P.arrayN))) =
                                                                                                                     (GT.P.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) GT.P.arrayN -> ('a) GT.P.arrayN)) =
                                                                                                                       (GT.P.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) GT.P.arrayN -> Pervasive.bool)) =
                                                                                                                  (GT.P.all)
            let rec allsame : (('a) GT.P.arrayN -> Pervasive.bool) =
                                                                       (GT.P.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) GT.P.arrayN) List.list -> (('b) List.list) GT.P.arrayN) =
                                                                                                (GT.P.concat)
        end
        let rec parties : Pervasive.int =
                                            (GT.parties)
        type party = GT.party
        let rec partyset : NextMsgISet.ISet.iset =
                                                     (GT.partyset)
        type round = GT.round
        let rec rounds : (GT.public_input -> Pervasive.int) =
                                                                (GT.rounds)
        let rec roundset : (GT.public_input -> NextMsgISet.ISet.iset) =
                                                                          (GT.roundset)
        type ('a) pmap = ('a) GT.pmap
        type ('a) rmap = ('a) GT.rmap
        type ('a) prmap = ('a) GT.prmap
        type ('a) ppmap = ('a) GT.ppmap
        type ('a) pprmap = ('a) GT.pprmap
        type local_input = GT.local_input
        type local_output = GT.local_output
        type local_rand = GT.local_rand
        type msg = GT.msg
        type pmsgs = GT.pmsgs
        type rmsgs = GT.rmsgs
        type prmsgs = GT.prmsgs
        type ppmsgs = GT.ppmsgs
        type pprmsgs = GT.pprmsgs
        type in_msgs = GT.in_msgs
        type out_msgs = GT.out_msgs
        type view = GT.view
        type trace = GT.trace
        let rec eq_msg : (GT.msg -> (GT.msg -> Pervasive.bool)) =
                                                                    (GT.eq_msg)
        let rec eq_pmsgs : (GT.pmsgs -> (GT.pmsgs -> Pervasive.bool)) =
                                                                          (GT.eq_pmsgs)
        let rec eq_rmsgs : (GT.rmsgs -> (GT.rmsgs -> Pervasive.bool)) =
                                                                          (GT.eq_rmsgs)
        let rec pinit : ((GT.party -> 'a) -> ('a) GT.P.arrayN) =
                                                                   (GT.pinit)
        let rec ppinit : ((GT.party -> (GT.party -> 'a)) -> (('a) GT.P.arrayN) GT.P.arrayN) =
                                                                                                (GT.ppinit)
        let rec prempty : (Pervasive.int -> ('a -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                     (GT.prempty)
        let rec pprempty : (Pervasive.int -> ('a -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                    (GT.pprempty)
        let rec ppswap : (('a) GT.ppmap -> (('a) GT.P.arrayN) GT.P.arrayN) =
                                                                               (GT.ppswap)
        let rec prget : (('a) GT.prmap -> (GT.round -> ('a) GT.P.arrayN)) =
                                                                              (GT.prget)
        let rec pprget : (('a) GT.pprmap -> (GT.round -> (('a) GT.P.arrayN) GT.P.arrayN)) =
                                                                                              (GT.pprget)
        let rec prset : (('a) GT.prmap -> (Pervasive.int -> (('a) GT.pmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN))) =
                                                                                                                                (GT.prset)
        let rec prext : (Pervasive.int -> (('a) GT.prmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                              (GT.prext)
        let rec prextset : (('a) GT.prmap -> (Pervasive.int -> (('a) GT.pmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN))) =
                                                                                                                                   (GT.prextset)
        let rec pprset : (('a) GT.pprmap -> (GT.round -> (('a) GT.ppmap -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN))) =
                                                                                                                                            (GT.pprset)
        let rec prfilter : ((GT.round -> Pervasive.bool) -> (('a) GT.prmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                                                (GT.prfilter)
        let rec pprfilter : ((GT.round -> Pervasive.bool) -> (('a) GT.pprmap -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                                (GT.pprfilter)
        let rec rdom : (Pervasive.int -> (GT.round -> (('a) GT.rmap -> Pervasive.bool))) =
                                                                                             (GT.rdom)
        let rec prdom : (Pervasive.int -> (GT.round -> (('a) GT.prmap -> Pervasive.bool))) =
                                                                                               (GT.prdom)
        let rec pprdom : (Pervasive.int -> (GT.round -> (('a) GT.pprmap -> Pervasive.bool))) =
                                                                                                 (GT.pprdom)
        let rec rlist : (Pervasive.int -> (('a) List.list -> ('a) NextMsgArray.Array.array)) =
                                                                                                 (GT.rlist)
        let rec prlist : (Pervasive.int -> ((GT.pmsgs) List.list -> (GT.msg) GT.prmap)) =
                                                                                            (GT.prlist)
        let rec pcons : (('a) GT.pmap -> ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                         (GT.pcons)
        let rec phead : ((('a) List.list) GT.pmap -> ('a) GT.P.arrayN) =
                                                                           (GT.phead)
        let rec pbehead : ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN) =
                                                                                         (GT.pbehead)
        let rec prcons : ((('a) List.list) GT.pmap -> (('a) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                          (GT.prcons)
        let rec pcat : ((('a) List.list) GT.pmap -> ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                                    (GT.pcat)
        let rec ppcons : (('a) GT.ppmap -> ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                          (GT.ppcons)
        let rec pprcons : ((('a) List.list) GT.ppmap -> (('a) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                           (GT.pprcons)
        let rec ppcat : ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                     (GT.ppcat)
        let rec prmsgs_up_to : (GT.round -> (GT.prmsgs -> ((GT.msg) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                                (GT.prmsgs_up_to)
        let rec pprmsgs_up_to : (GT.round -> (GT.pprmsgs -> (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                (GT.pprmsgs_up_to)
        let rec get_trace_inputs : (GT.trace -> (GT.local_input) GT.P.arrayN) =
                                                                                  (GT.get_trace_inputs)
        let rec get_trace_in_msgs : (GT.trace -> (GT.in_msgs) GT.P.arrayN) =
                                                                               (GT.get_trace_in_msgs)
        let rec get_trace_rands : (GT.trace -> (GT.local_rand) GT.P.arrayN) =
                                                                                (GT.get_trace_rands)
        let rec get_view : (GT.party -> (GT.trace -> GT.view)) =
                                                                   (GT.get_view)
        let rec get_trace_in_msgs_round : (GT.round -> (GT.trace -> ((GT.msg) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                             (GT.get_trace_in_msgs_round)
        let rec get_view_in_msgs_round : (GT.round -> (GT.view -> (GT.msg) GT.P.arrayN)) =
                                                                                             (GT.get_view_in_msgs_round)
        let rec add_view_in_msgs : (GT.round -> (GT.pmsgs -> (GT.view -> (GT.local_input * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))))) =
                                                                                                                                                                     (GT.add_view_in_msgs)
        let rec get_trace_in_msgs_up_to : (GT.round -> (GT.trace -> (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                        (GT.get_trace_in_msgs_up_to)
        let rec add_trace_in_msgs : (GT.round -> (GT.ppmsgs -> (GT.trace -> ((GT.local_input * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))) GT.P.arrayN))) =
                                                                                                                                                                                      (GT.add_trace_in_msgs)
        let rec valid_trace : (GT.public_input -> (GT.trace -> Pervasive.bool)) =
                                                                                    (GT.valid_trace)
        let rec valid_view : (GT.public_input -> (GT.view -> Pervasive.bool)) =
                                                                                  (GT.valid_view)
    end
    type local_messages = local_msgs
    type messages = (local_messages) ST.pmap
    type local_out_messages = local_messages
    type local_in_messages = local_messages
    type out_messages = messages
    type in_messages = messages
    let rec from_local_messages : (MaurerAdd.local_messages -> (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * Pervasive.unit))))) =
                                                                                                                                                               (MaurerAdd.from_local_messages)
    let rec to_local_messages : (MaurerAdd.ST.pmsgs -> Pervasive.unit) =
                                                                           (MaurerAdd.to_local_messages)
    let rec send_messages : (MaurerAdd.out_messages -> (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * (Pervasive.unit * Pervasive.unit))))) =
                                                                                                                                                       (MaurerAdd.send_messages)
    let from_messages (xs : (local_messages) ST.P.arrayN) : (ST.pmsgs) ST.P.arrayN =
                                                                                       (ST.P.map (from_local_messages) xs)
    let to_messages (xs : (ST.pmsgs) ST.P.arrayN) : (local_messages) ST.P.arrayN =
                                                                                     (ST.P.map (to_local_messages) xs)
    let valid_local_messages (_ : ST.public_input) (_ : ST.round) (_ : local_messages) : Pervasive.bool =
                                                                                                            (Pervasive._true)
    let valid_messages (p : ST.public_input) (r : ST.round) (ms : messages) : Pervasive.bool =
                                                                                                 (ST.P.all (fun (_ : Pervasive.int) -> (valid_local_messages p r)) ms)
    let valid_msg (_ : ST.public_input) (_ : ST.round) (_ : ST.msg) : Pervasive.bool =
                                                                                         (Pervasive._true)
    let valid_pmsgs (p : ST.public_input) (r : ST.round) (ms : ST.pmsgs) : Pervasive.bool =
                                                                                              (ST.P.all (fun (_ : Pervasive.int) -> (valid_msg p r)) ms)
    let valid_ppmsgs (p : ST.public_input) (r : ST.round) (ms : ST.ppmsgs) : Pervasive.bool =
                                                                                                (ST.P.all (fun (_ : Pervasive.int) -> (valid_pmsgs p r)) ms)
    type local_state = (share * (GT.local_rand, local_in_msgs) Aux.either)
    let init_local_state (_ : ST.party) (_ : ST.public_input) (wis : share) (ris : ST.local_rand) : (share * (ST.local_rand, local_in_msgs) Aux.either) =
                                                                                                                                                            (wis , (Aux.L ris))
    let update_local_state (_ : ST.party) (_ : ST.round) (_ : ST.public_input) (_ : ST.local_input) (ins : local_in_messages) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : (share * (GT.local_rand, local_in_messages) Aux.either) =
                                                                                                                                                                                                                                                       ((fst st) , (Aux.R ins))
    let get_local_state (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : local_state =
                                                                                                                                                             (let (go) = (fun (st : local_state) (r0 : ST.round) -> (let (insr) = (ST.prget insi r0) in
                                                                                                                                                                                                                     (update_local_state i r0 x wi (to_local_messages insr) st))) in
                                                                                                                                                              (List.foldl go (init_local_state i x wi ri) (AuxList.iseq r)))
    type state = (local_state) ST.pmap
    let init_state (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                        (ST.P.imap (fun (i : ST.party) (wi_ri : (ST.local_input * ST.local_rand)) -> (init_local_state i x (fst wi_ri) (snd wi_ri))) (ST.P.zip ws rs))
    let update_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (local_in_messages) ST.pmap) (st : state) : (local_state) ST.P.arrayN =
                                                                                                                                                                               (ST.P.imap (fun (i : ST.party) (wsi_insi_sti : (ST.local_input * (local_in_messages * local_state))) -> (update_local_state i round x (Aux.fst3 wsi_insi_sti) (Aux.snd3 wsi_insi_sti) (Aux.thr3 wsi_insi_sti))) (ST.P.zip3 ws ins st))
    let get_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                                                                       (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (get_local_state i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) (ST.P.zip3 ws rs ins))
    let stateful_local_protocol_round (i : GT.party) (_ : ST.round) (g : _Gate) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : local_out_msgs =
                                                                                                                                                                (local_gate_start i g (fst st) (Aux.unL (snd st)))
    let stateful_local_protocol_end (i : GT.party) (g : _Gate) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : share =
                                                                                                                                      (local_gate_end i g (fst st) (Aux.unR (snd st)))
    let stateful_local_protocol''' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : (ST.round) List.list) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                                            (List.foldl (fun (acc : (local_state * ST.out_msgs)) (round : ST.round) -> (let (outs') = (ST.prset (snd acc) round (from_local_messages (stateful_local_protocol_round i round x (Aux.fst3 acc)))) in
                                                                                                                                                                                                                                                                                                        (let (st') = (update_local_state i round x inp (to_local_messages (ST.prget ins round)) (Aux.fst3 acc)) in
                                                                                                                                                                                                                                                                                                         (st' , outs')))) (st , (ST.prempty sz (Pervasive.witness))) rounds)
    let stateful_local_protocol'' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                               (stateful_local_protocol''' i x inp st ins sz (AuxList.iseq rounds))
    let stateful_local_protocol' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) : (local_state * ST.out_msgs) =
                                                                                                                                                                     (stateful_local_protocol'' i x inp st ins (ST.rounds x) (ST.rounds x))
    let stateful_local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                          (let (outs) = (stateful_local_protocol' i x (Aux.fst3 vi) (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) (Aux.snd3 vi)) in
                                                                                                                           (let (out) = (stateful_local_protocol_end i x (Aux.fst3 outs)) in
                                                                                                                            ((snd outs) , out)))
    let stateful_protocol_round (round : ST.round) (x : ST.public_input) (st : state) : (local_out_messages) ST.P.arrayN =
                                                                                                                             (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_round i round x sti)) st)
    let stateful_protocol_end (x : ST.public_input) (st : state) : (ST.local_output) ST.P.arrayN =
                                                                                                     (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_end i x sti)) st)
    let stateful_protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : (ST.round) List.list) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                                  (List.foldl (fun (ins_st : ((ST.in_msgs) ST.pmap * state)) (round : ST.round) -> (let (ins0) = (Aux.fst3 ins_st) in
                                                                                                                                                                                                                                                                                    (let (st0) = (snd ins_st) in
                                                                                                                                                                                                                                                                                     (let (outs) = (send_messages (stateful_protocol_round round x st0)) in
                                                                                                                                                                                                                                                                                      ((ST.pprset ins0 round (from_messages outs)) , (update_state round x ws outs st0)))))) (ins , st) rounds)
    let stateful_protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : ST.round) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                     (stateful_protocol''' x ws ins st (AuxList.iseq rounds))
    let stateful_protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                     (stateful_protocol'' x ws (ST.pprempty (ST.rounds x) (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                     (let (ins_st') = (stateful_protocol' x ws rs) in
                                                                                                                                                                                                                      (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                       (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                        (tr , outs))))
    let stateful_protocol_sz' (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                             (stateful_protocol'' x ws (ST.pprempty sz (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol_sz (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                                             (let (ins_st') = (stateful_protocol_sz' sz x ws rs) in
                                                                                                                                                                                                                                              (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                                               (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                                                (tr , outs))))
    let local_protocol_round (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.pmsgs =
                                                                                                                                                               (from_local_messages (stateful_local_protocol_round i r x (get_local_state i r x wi ri insi)))
    let local_protocol_end (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.local_output =
                                                                                                                                                     (stateful_local_protocol_end i x (get_local_state i (ST.rounds x) x wi ri insi))
    let local_protocol'' (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : ST.out_msgs =
                                                                                                                                                                                       (List.foldl (fun (outs : ST.out_msgs) (round : Pervasive.int) -> (ST.prset outs round (local_protocol_round i round x wi ri ins))) (ST.prempty sz (Pervasive.witness)) (AuxList.iseq rounds))
    let local_protocol' (i : ST.party) (x : ST.public_input) (vi : ST.view) : ST.out_msgs =
                                                                                              (local_protocol'' i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi) (ST.rounds x) (ST.rounds x))
    let local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                 (let (outs) = (local_protocol' i x vi) in
                                                                                                                  (let (out) = (local_protocol_end i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi)) in
                                                                                                                   (outs , out)))
    let protocol_round (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.pmsgs) ST.P.arrayN =
                                                                                                                                                                                         (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                                          (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_round i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol_end (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                                                                                           (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                            (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_end i x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (round1 : ST.round) (d : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (List.Iota.iota_ round1 d))
    let protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (rounds : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (AuxList.iseq rounds))
    let protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (ST.in_msgs) ST.pmap =
                                                                                                                                  (protocol'' x ws rs (ST.pprempty (ST.rounds x) (Pervasive.witness)) (ST.rounds x))
    let protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                            (let (ins) = (protocol' x ws rs) in
                                                                                                                                                                                                             (let (outs) = (protocol_end x ws rs ins) in
                                                                                                                                                                                                              (let (tr) = (ST.P.zip3 ws ins rs) in
                                                                                                                                                                                                               (tr , outs))))
    let get_view_in_msgs (j : ST.party) (vi : ST.view) : ST.rmsgs =
                                                                      (ST.P.get (Aux.snd3 vi) j)
    let get_view_out_msgs (i : ST.party) (j : ST.party) (x : ST.public_input) (vi : ST.view) : ST.rmsgs =
                                                                                                            (ST.P.get (local_protocol' i x vi) j)
    let consistent_inputs (wij : _Gate) (i : NextMsgMaurerAPI.MaurerAPI.pid) (j : NextMsgMaurerAPI.MaurerAPI.pid) (si : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) (sj : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) : Pervasive.bool =
                                                                                                                                                                                                                                                                                                       (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.const_valid_share wij si) (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.const_valid_share wij sj) (NextMsgMaurerAPI.MaurerAPI.consistent_shares i j si sj)))
    let consistent_rands (x : _Gate) (_ : ST.party) (_ : ST.party) (ri : GT.local_rand) (rj : GT.local_rand) : Pervasive.bool =
                                                                                                                                  (Pervasive._and (gate_valid_rand x ri) (gate_valid_rand x rj))
    let valid_inputs (x : ST.public_input) (ws : (ST.local_input) ST.pmap) : Pervasive.bool =
                                                                                                (Pervasive.witness)
    let valid_rands (x : ST.public_input) (ws : (ST.local_rand) ST.pmap) : Pervasive.bool =
                                                                                              (Pervasive.witness)
    let consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                (Pervasive._and (ST.eq_rmsgs (get_view_in_msgs j vi) (get_view_out_msgs j i x vj)) (Pervasive._and (Pervasive.eq (get_view_in_msgs i vj) (get_view_out_msgs i j x vi)) (Pervasive._and (consistent_inputs x i j (Aux.fst3 vi) (Aux.fst3 vj)) (consistent_rands x i j (Aux.thr3 vi) (Aux.thr3 vj)))))
    let consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                    (Pervasive.witness)
    let pairwise_consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                         (Pervasive._and (ST.valid_view x vi) (Pervasive._and (ST.valid_view x vj) (consistent_views x i j vi vj)))
    let pairwise_consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                             (Pervasive.witness)
    let view_output (i : ST.party) (x : ST.public_input) (v : ST.view) : ST.local_output =
                                                                                             (local_protocol_end i x (Aux.fst3 v) (Aux.thr3 v) (Aux.snd3 v))
    let view_outputs (x : ST.public_input) (vs : (ST.view) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                        (ST.P.imap (fun (i : ST.party) (v : ST.view) -> (view_output i x v)) vs)
    let stateful_consistent_outputs : (ST.public_input -> (ST.party -> (ST.party -> (ST.local_output -> (ST.local_output -> Pervasive.bool))))) = Pervasive.witness
    type local_state2 = (local_state * local_state)
    let stateful_consistent_views_outputs_round (r : ST.round) (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : ((local_state * local_state) * Pervasive.bool) =
                                                                                                                                                                                                                                                                                     (let (outs1) = (from_local_messages (stateful_local_protocol_round i r x (Aux.fst3 sts))) in
                                                                                                                                                                                                                                                                                      (let (outs2) = (from_local_messages (stateful_local_protocol_round j r x (snd sts))) in
                                                                                                                                                                                                                                                                                       (let (in1) = (ST.prget ins1 r) in
                                                                                                                                                                                                                                                                                        (let (in2) = (ST.prget ins2 r) in
                                                                                                                                                                                                                                                                                         (let (sts1') = (update_local_state i r x inp1 (to_local_messages in1) (Aux.fst3 sts)) in
                                                                                                                                                                                                                                                                                          (let (sts2') = (update_local_state j r x inp2 (to_local_messages in2) (snd sts)) in
                                                                                                                                                                                                                                                                                           (let (b) = (Pervasive._and (ST.eq_msg (ST.P.get outs1 j) (ST.P.get in2 i)) (ST.eq_msg (ST.P.get outs2 i) (ST.P.get in1 j))) in
                                                                                                                                                                                                                                                                                            ((sts1' , sts2') , b))))))))
    let stateful_consistent_views_outputs''' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) (rounds : (ST.round) List.list) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                                                    (let (go) = (fun (stb : (local_state2 * Pervasive.bool)) (r : ST.round) -> (let (stb') = (stateful_consistent_views_outputs_round r x i j inp1 inp2 ins1 ins2 (fst stb)) in
                                                                                                                                                                                                                                                                                                                                                                ((fst stb') , (Pervasive._and (snd stb) (snd stb'))))) in
                                                                                                                                                                                                                                                                                     (List.foldl go (sts , (Pervasive._true)) rounds))
    let stateful_consistent_views_outputs'' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                   (stateful_consistent_views_outputs''' x i j inp1 inp2 ins1 ins2 sts (AuxList.iseq (ST.rounds x)))
    let stateful_consistent_views_outputs' (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                   (let (st1) = (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) in
                                                                                                                                                                    (let (st2) = (init_local_state j x (Aux.fst3 vj) (Aux.thr3 vj)) in
                                                                                                                                                                     (let (outsb) = (stateful_consistent_views_outputs'' x i j (Aux.fst3 vi) (Aux.fst3 vj) (Aux.snd3 vi) (Aux.snd3 vj) (st1 , st2)) in
                                                                                                                                                                      outsb)))
    let stateful_consistent_views_outputs (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                                 (let (outsb) = (stateful_consistent_views_outputs' x i j vi vj) in
                                                                                                                                                  (let (outs1) = (Aux.fst3 (fst outsb)) in
                                                                                                                                                   (let (outs2) = (snd (fst outsb)) in
                                                                                                                                                    (let (b) = (snd outsb) in
                                                                                                                                                     (let (out1) = (stateful_local_protocol_end i x outs1) in
                                                                                                                                                      (let (out2) = (stateful_local_protocol_end j x outs2) in
                                                                                                                                                       (Pervasive._and b (stateful_consistent_outputs x i j out1 out2))))))))
    let g_protocol (x : _Gate) (ws : (share) GT.pmap) (cs : (GT.local_rand) GT.pmap) : (((share * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))) GT.P.arrayN * (share) GT.P.arrayN) =
                                                                                                                                                                                                             (let (outs) = (GT.P.imap (fun (i : GT.party) (wc : (share * GT.local_rand)) -> (local_gate_start i x (fst wc) (snd wc))) (GT.P.zip ws cs)) in
                                                                                                                                                                                                              (let (ins) = (send_messages outs) in
                                                                                                                                                                                                               (let (o) = (GT.P.imap (fun (i : GT.party) (wi : (share * local_in_msgs)) -> (local_gate_end i x (fst wi) (snd wi))) (GT.P.zip ws ins)) in
                                                                                                                                                                                                                (let (rins) = (GT.P.map (fun (bin : local_messages) -> (GT.P.map (fun (msg : GT.msg) -> (NextMsgArray.Array.init (Pervasive.mk_int 1) (fun (j : Pervasive.int) -> if (Pervasive.eq j (Pervasive.mk_int 0)) then msg else (Pervasive.witness)))) (from_local_messages bin))) ins) in
                                                                                                                                                                                                                 (let (tr) = (GT.P.zip3 ws rins cs) in
                                                                                                                                                                                                                  (tr , o))))))
end
module MaurerMul = struct
    type _Gate = (NextMsgMaurerAPI.MaurerAPI.wid * (NextMsgMaurerAPI.MaurerAPI.wid * NextMsgMaurerAPI.MaurerAPI.wid))
    type share = (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)
    type local_msgs = NextMsgMaurerAPI.MaurerAPI.msgs
    type local_in_msgs = local_msgs
    type local_out_msgs = local_msgs
    module GT = struct
        type public_input = _Gate
        module P = struct
            let rec size : Pervasive.int =
                                             (NextMsgMaurerP.MaurerP.size)
            type ('a) arrayN = ('a) NextMsgMaurerP.MaurerP.arrayN
            let rec get : (('a) Aux.array5 -> (Pervasive.int -> 'a)) =
                                                                         (NextMsgMaurerP.MaurerP.get)
            let rec set : (('a) Aux.array5 -> (Pervasive.int -> ('a -> ('a * ('a * ('a * ('a) Aux.array2)))))) =
                                                                                                                   (NextMsgMaurerP.MaurerP.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a * ('a * ('a * ('a * 'a))))) =
                                                                                         (NextMsgMaurerP.MaurerP.init)
            let rec of_list : (('a) List.list -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                         (NextMsgMaurerP.MaurerP.of_list)
            let rec to_list : (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) List.list) =
                                                                                         (NextMsgMaurerP.MaurerP.to_list)
            let rec to_assoc : (('a) NextMsgMaurerP.MaurerP.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                                            (NextMsgMaurerP.MaurerP.to_assoc)
            let rec create : ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                            (NextMsgMaurerP.MaurerP.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                              (NextMsgMaurerP.MaurerP.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('b) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                             (NextMsgMaurerP.MaurerP.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> (('b) NextMsgMaurerP.MaurerP.arrayN -> ('c) NextMsgMaurerP.MaurerP.arrayN))) =
                                                                                                                                                                           (NextMsgMaurerP.MaurerP.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                                           (NextMsgMaurerP.MaurerP.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool)) =
                                                                                                                                    (NextMsgMaurerP.MaurerP.all)
            let rec allsame : (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool) =
                                                                                         (NextMsgMaurerP.MaurerP.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) NextMsgMaurerP.MaurerP.arrayN) List.list -> (('b) List.list) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                                                                    (NextMsgMaurerP.MaurerP.concat)
        end
        let parties : Pervasive.int =
                                        (P.size)
        type party = Pervasive.int
        let partyset : NextMsgISet.ISet.iset =
                                                 (NextMsgISet.ISet.iset (parties))
        type round = Pervasive.int
        let rounds (_ : public_input) : Pervasive.int =
                                                          (Pervasive.mk_int 1)
        let roundset (p : public_input) : NextMsgISet.ISet.iset =
                                                                    (NextMsgISet.ISet.iset (rounds p))
        type ('a) pmap = ('a) P.arrayN
        type ('a) rmap = ('a) NextMsgArray.Array.array
        type ('a) prmap = (('a) rmap) pmap
        type ('a) ppmap = (('a) pmap) pmap
        type ('a) pprmap = (('a) rmap) ppmap
        type local_input = share
        type local_output = share
        type local_rand = NextMsgMaurerAPI.MaurerAPI.rand
        type msg = NextMsgMaurerAPI.MaurerAPI.msg
        type pmsgs = (msg) pmap
        type rmsgs = (msg) rmap
        type prmsgs = (rmsgs) pmap
        type ppmsgs = (pmsgs) pmap
        type pprmsgs = (prmsgs) pmap
        type in_msgs = prmsgs
        type out_msgs = prmsgs
        type view = (local_input * (in_msgs * local_rand))
        type trace = (view) pmap
        let rec eq_msg : (NextMsgMaurerAPI.MaurerAPI.msg -> (NextMsgMaurerAPI.MaurerAPI.msg -> Pervasive.bool)) =
                                                                                                                    (NextMsgMaurerAPI.MaurerAPI.eq_msg)
        let eq_pmsgs (m1 : pmsgs) (m2 : pmsgs) : Pervasive.bool =
                                                                    (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (P.get m1 i) (P.get m2 i))) (P.size))
        let eq_rmsgs (m1 : rmsgs) (m2 : rmsgs) : Pervasive.bool =
                                                                    (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size m1) (NextMsgArray.Array.size m2)) (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (NextMsgArray.Array.get m1 i) (NextMsgArray.Array.get m2 i))) (NextMsgArray.Array.size m1)))
        let pinit (f : (party -> 'a)) : ('a) P.arrayN =
                                                          (P.init f)
        let ppinit (f : (party -> (party -> 'a))) : (('a) P.arrayN) P.arrayN =
                                                                                 (pinit (fun (i : party) -> (pinit (f i))))
        let prempty (sz : Pervasive.int) (v : 'a) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                 (pinit (fun (_ : party) -> (NextMsgArray.Array.create sz v)))
        let pprempty (sz : Pervasive.int) (v : 'a) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                             (ppinit (fun (_ : party) (_ : party) -> (NextMsgArray.Array.create sz v)))
        let ppswap (m : ('a) ppmap) : (('a) P.arrayN) P.arrayN =
                                                                   (ppinit (fun (j : Pervasive.int) (i : Pervasive.int) -> (P.get (P.get m i) j)))
        let prget (xs : ('a) prmap) (r : round) : ('a) P.arrayN =
                                                                    (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.get (P.get xs i) r)))
        let pprget (xs : ('a) pprmap) (r : round) : (('a) P.arrayN) P.arrayN =
                                                                                 (ppinit (fun (i : Pervasive.int) (j : Pervasive.int) -> (NextMsgArray.Array.get (P.get (P.get xs i) j) r)))
        let prset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.merge (fun (x0 : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set x0 n y)) xs x)
        let prext (sz : Pervasive.int) (xs : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.init sz (fun (j : Pervasive.int) -> if (Pervasive._and (Int.le (Pervasive.mk_int 0) j) (Int.lt j (NextMsgArray.Array.size (P.get xs i)))) then (NextMsgArray.Array.get (P.get xs i) j) else (Pervasive.witness)))))
        let prextset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                          (prset (prext (Int.plus n (Pervasive.mk_int 1)) xs) n x)
        let pprset (xs : ('a) pprmap) (n : round) (x : ('a) ppmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                             (P.merge (P.merge (fun (ys : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set ys n y))) xs x)
        let prfilter (p : (round -> Pervasive.bool)) (ins : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) ins)
        let pprfilter (p : (round -> Pervasive.bool)) (ins : ('a) pprmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                                    (P.map (fun (xs : (('a) NextMsgArray.Array.array) P.arrayN) -> (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) xs)) ins)
        let rdom (sz : Pervasive.int) (round : round) (xs : ('a) rmap) : Pervasive.bool =
                                                                                            (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size xs) sz) (Pervasive.witness))
        let prdom (sz : Pervasive.int) (round : round) (xs : ('a) prmap) : Pervasive.bool =
                                                                                              (P.all (fun (_ : Pervasive.int) -> (rdom sz round)) xs)
        let pprdom (sz : Pervasive.int) (round : round) (xs : ('a) pprmap) : Pervasive.bool =
                                                                                                (P.all (fun (_ : Pervasive.int) -> (prdom sz round)) xs)
        let rlist (sz : Pervasive.int) (xs : ('a) List.list) : ('a) NextMsgArray.Array.array =
                                                                                                 (List.foldl (fun (rs : ('a) NextMsgArray.Array.array) (i : Pervasive.int) -> (NextMsgArray.Array.set rs i (List.nth (Pervasive.witness) xs i))) (NextMsgArray.Array.create sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let prlist (sz : Pervasive.int) (xs : (pmsgs) List.list) : (msg) prmap =
                                                                                   (List.foldl (fun (rs : (msg) prmap) (i : Pervasive.int) -> (prset rs i (List.nth (Pervasive.witness) xs i))) (prempty sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let pcons (x : ('a) pmap) (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                               (P.merge (fun (x0 : 'a) (xs0 : ('a) List.list) -> (AuxList.cons x0 xs0)) x xs)
        let phead (xs : (('a) List.list) pmap) : ('a) P.arrayN =
                                                                   (P.map (List.head (Pervasive.witness)) xs)
        let pbehead (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                 (P.map (List.behead) xs)
        let prcons (xs : (('a) List.list) pmap) (x : ('a) pmap) : (('a) List.list) P.arrayN =
                                                                                                (P.merge (List.rcons) xs x)
        let pcat (xs : (('a) List.list) pmap) (ys : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                                           (P.merge (fun (x : ('a) List.list) (y : ('a) List.list) -> (AuxList.cat x y)) xs ys)
        let ppcons (x : ('a) ppmap) (xs : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                             (P.merge (pcons) x xs)
        let pprcons (xs : (('a) List.list) ppmap) (x : ('a) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                              (P.merge (prcons) xs x)
        let ppcat (xs : (('a) List.list) ppmap) (ys : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                                         (P.merge (pcat) xs ys)
        let prmsgs_up_to (round : round) (ins : prmsgs) : ((msg) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (prfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let pprmsgs_up_to (round : round) (ins : pprmsgs) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                     (pprfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let get_trace_inputs (tr : trace) : (local_input) P.arrayN =
                                                                       (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.fst3 x)) tr)
        let get_trace_in_msgs (tr : trace) : (in_msgs) P.arrayN =
                                                                    (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.snd3 x)) tr)
        let get_trace_rands (tr : trace) : (local_rand) P.arrayN =
                                                                     (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.thr3 x)) tr)
        let get_view (i : party) (tr : trace) : view =
                                                         (P.get tr i)
        let get_trace_in_msgs_round (round : round) (tr : trace) : ((msg) P.arrayN) P.arrayN =
                                                                                                 (pprget (get_trace_in_msgs tr) round)
        let get_view_in_msgs_round (round : round) (v : view) : (msg) P.arrayN =
                                                                                   (prget (Aux.snd3 v) round)
        let add_view_in_msgs (r : round) (ins : pmsgs) (v : view) : (local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand)) =
                                                                                                                                                 ((Aux.fst3 v) , ((prset (Aux.snd3 v) r ins) , (Aux.thr3 v)))
        let get_trace_in_msgs_up_to (round : round) (tr : trace) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                            (pprmsgs_up_to round (get_trace_in_msgs tr))
        let add_trace_in_msgs (r : round) (ins : ppmsgs) (tr : trace) : ((local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand))) P.arrayN =
                                                                                                                                                                (P.map (fun (ins_v : (pmsgs * view)) -> (add_view_in_msgs r (Aux.fst3 ins_v) (snd ins_v))) (P.zip ins tr))
        let valid_trace (x : public_input) (tr : trace) : Pervasive.bool =
                                                                             (pprdom (rounds x) (rounds x) (get_trace_in_msgs tr))
        let valid_view (x : public_input) (v : view) : Pervasive.bool =
                                                                          (prdom (rounds x) (rounds x) (Aux.snd3 v))
    end
    let local_gate_start (_ : GT.party) (wij : _Gate) (st : share) (r : GT.local_rand) : NextMsgMaurerAPI.MaurerAPI.msgs =
                                                                                                                             (NextMsgMaurerAPI.MaurerAPI.mul_start (Aux.nth1_3 wij) (Aux.nth2_3 wij) (fst st) r)
    let local_gate_end (_ : GT.party) (_ : _Gate) (st : share) (pmsgs : NextMsgMaurerAPI.MaurerAPI.msgs) : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) =
                                                                                                                                                                                        ((NextMsgMaurerAPI.MaurerAPI.mul_end pmsgs (fst st)) , (snd st))
    let gate_valid_rand (_ : _Gate) (_ : GT.local_rand) : Pervasive.bool =
                                                                             (Pervasive._true)
    let gate_valid_rands (x : _Gate) (cs : (GT.local_rand) GT.P.arrayN) : Pervasive.bool =
                                                                                             (GT.P.all (fun (_ : Pervasive.int) (c : GT.local_rand) -> (gate_valid_rand x c)) cs)
    module ST = struct
        type public_input = GT.public_input
        module P = struct
            let rec size : Pervasive.int =
                                             (GT.P.size)
            type ('a) arrayN = ('a) GT.P.arrayN
            let rec get : (('a) GT.P.arrayN -> (Pervasive.int -> 'a)) =
                                                                          (GT.P.get)
            let rec set : (('a) GT.P.arrayN -> (Pervasive.int -> ('a -> ('a) GT.P.arrayN))) =
                                                                                                (GT.P.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a) GT.P.arrayN) =
                                                                           (GT.P.init)
            let rec of_list : (('a) List.list -> ('a) GT.P.arrayN) =
                                                                       (GT.P.of_list)
            let rec to_list : (('a) GT.P.arrayN -> ('a) List.list) =
                                                                       (GT.P.to_list)
            let rec to_assoc : (('a) GT.P.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                          (GT.P.to_assoc)
            let rec create : ('a -> ('a) GT.P.arrayN) =
                                                          (GT.P.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) GT.P.arrayN)) =
                                                                            (GT.P.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) GT.P.arrayN -> ('b) GT.P.arrayN)) =
                                                                                                         (GT.P.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) GT.P.arrayN -> (('b) GT.P.arrayN -> ('c) GT.P.arrayN))) =
                                                                                                                     (GT.P.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) GT.P.arrayN -> ('a) GT.P.arrayN)) =
                                                                                                                       (GT.P.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) GT.P.arrayN -> Pervasive.bool)) =
                                                                                                                  (GT.P.all)
            let rec allsame : (('a) GT.P.arrayN -> Pervasive.bool) =
                                                                       (GT.P.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) GT.P.arrayN) List.list -> (('b) List.list) GT.P.arrayN) =
                                                                                                (GT.P.concat)
        end
        let rec parties : Pervasive.int =
                                            (GT.parties)
        type party = GT.party
        let rec partyset : NextMsgISet.ISet.iset =
                                                     (GT.partyset)
        type round = GT.round
        let rec rounds : (GT.public_input -> Pervasive.int) =
                                                                (GT.rounds)
        let rec roundset : (GT.public_input -> NextMsgISet.ISet.iset) =
                                                                          (GT.roundset)
        type ('a) pmap = ('a) GT.pmap
        type ('a) rmap = ('a) GT.rmap
        type ('a) prmap = ('a) GT.prmap
        type ('a) ppmap = ('a) GT.ppmap
        type ('a) pprmap = ('a) GT.pprmap
        type local_input = GT.local_input
        type local_output = GT.local_output
        type local_rand = GT.local_rand
        type msg = GT.msg
        type pmsgs = GT.pmsgs
        type rmsgs = GT.rmsgs
        type prmsgs = GT.prmsgs
        type ppmsgs = GT.ppmsgs
        type pprmsgs = GT.pprmsgs
        type in_msgs = GT.in_msgs
        type out_msgs = GT.out_msgs
        type view = GT.view
        type trace = GT.trace
        let rec eq_msg : (GT.msg -> (GT.msg -> Pervasive.bool)) =
                                                                    (GT.eq_msg)
        let rec eq_pmsgs : (GT.pmsgs -> (GT.pmsgs -> Pervasive.bool)) =
                                                                          (GT.eq_pmsgs)
        let rec eq_rmsgs : (GT.rmsgs -> (GT.rmsgs -> Pervasive.bool)) =
                                                                          (GT.eq_rmsgs)
        let rec pinit : ((GT.party -> 'a) -> ('a) GT.P.arrayN) =
                                                                   (GT.pinit)
        let rec ppinit : ((GT.party -> (GT.party -> 'a)) -> (('a) GT.P.arrayN) GT.P.arrayN) =
                                                                                                (GT.ppinit)
        let rec prempty : (Pervasive.int -> ('a -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                     (GT.prempty)
        let rec pprempty : (Pervasive.int -> ('a -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                    (GT.pprempty)
        let rec ppswap : (('a) GT.ppmap -> (('a) GT.P.arrayN) GT.P.arrayN) =
                                                                               (GT.ppswap)
        let rec prget : (('a) GT.prmap -> (GT.round -> ('a) GT.P.arrayN)) =
                                                                              (GT.prget)
        let rec pprget : (('a) GT.pprmap -> (GT.round -> (('a) GT.P.arrayN) GT.P.arrayN)) =
                                                                                              (GT.pprget)
        let rec prset : (('a) GT.prmap -> (Pervasive.int -> (('a) GT.pmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN))) =
                                                                                                                                (GT.prset)
        let rec prext : (Pervasive.int -> (('a) GT.prmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                              (GT.prext)
        let rec prextset : (('a) GT.prmap -> (Pervasive.int -> (('a) GT.pmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN))) =
                                                                                                                                   (GT.prextset)
        let rec pprset : (('a) GT.pprmap -> (GT.round -> (('a) GT.ppmap -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN))) =
                                                                                                                                            (GT.pprset)
        let rec prfilter : ((GT.round -> Pervasive.bool) -> (('a) GT.prmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                                                (GT.prfilter)
        let rec pprfilter : ((GT.round -> Pervasive.bool) -> (('a) GT.pprmap -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                                (GT.pprfilter)
        let rec rdom : (Pervasive.int -> (GT.round -> (('a) GT.rmap -> Pervasive.bool))) =
                                                                                             (GT.rdom)
        let rec prdom : (Pervasive.int -> (GT.round -> (('a) GT.prmap -> Pervasive.bool))) =
                                                                                               (GT.prdom)
        let rec pprdom : (Pervasive.int -> (GT.round -> (('a) GT.pprmap -> Pervasive.bool))) =
                                                                                                 (GT.pprdom)
        let rec rlist : (Pervasive.int -> (('a) List.list -> ('a) NextMsgArray.Array.array)) =
                                                                                                 (GT.rlist)
        let rec prlist : (Pervasive.int -> ((GT.pmsgs) List.list -> (GT.msg) GT.prmap)) =
                                                                                            (GT.prlist)
        let rec pcons : (('a) GT.pmap -> ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                         (GT.pcons)
        let rec phead : ((('a) List.list) GT.pmap -> ('a) GT.P.arrayN) =
                                                                           (GT.phead)
        let rec pbehead : ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN) =
                                                                                         (GT.pbehead)
        let rec prcons : ((('a) List.list) GT.pmap -> (('a) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                          (GT.prcons)
        let rec pcat : ((('a) List.list) GT.pmap -> ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                                    (GT.pcat)
        let rec ppcons : (('a) GT.ppmap -> ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                          (GT.ppcons)
        let rec pprcons : ((('a) List.list) GT.ppmap -> (('a) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                           (GT.pprcons)
        let rec ppcat : ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                     (GT.ppcat)
        let rec prmsgs_up_to : (GT.round -> (GT.prmsgs -> ((GT.msg) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                                (GT.prmsgs_up_to)
        let rec pprmsgs_up_to : (GT.round -> (GT.pprmsgs -> (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                (GT.pprmsgs_up_to)
        let rec get_trace_inputs : (GT.trace -> (GT.local_input) GT.P.arrayN) =
                                                                                  (GT.get_trace_inputs)
        let rec get_trace_in_msgs : (GT.trace -> (GT.in_msgs) GT.P.arrayN) =
                                                                               (GT.get_trace_in_msgs)
        let rec get_trace_rands : (GT.trace -> (GT.local_rand) GT.P.arrayN) =
                                                                                (GT.get_trace_rands)
        let rec get_view : (GT.party -> (GT.trace -> GT.view)) =
                                                                   (GT.get_view)
        let rec get_trace_in_msgs_round : (GT.round -> (GT.trace -> ((GT.msg) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                             (GT.get_trace_in_msgs_round)
        let rec get_view_in_msgs_round : (GT.round -> (GT.view -> (GT.msg) GT.P.arrayN)) =
                                                                                             (GT.get_view_in_msgs_round)
        let rec add_view_in_msgs : (GT.round -> (GT.pmsgs -> (GT.view -> (GT.local_input * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))))) =
                                                                                                                                                                     (GT.add_view_in_msgs)
        let rec get_trace_in_msgs_up_to : (GT.round -> (GT.trace -> (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                        (GT.get_trace_in_msgs_up_to)
        let rec add_trace_in_msgs : (GT.round -> (GT.ppmsgs -> (GT.trace -> ((GT.local_input * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))) GT.P.arrayN))) =
                                                                                                                                                                                      (GT.add_trace_in_msgs)
        let rec valid_trace : (GT.public_input -> (GT.trace -> Pervasive.bool)) =
                                                                                    (GT.valid_trace)
        let rec valid_view : (GT.public_input -> (GT.view -> Pervasive.bool)) =
                                                                                  (GT.valid_view)
    end
    type local_messages = local_msgs
    type messages = (local_messages) ST.pmap
    type local_out_messages = local_messages
    type local_in_messages = local_messages
    type out_messages = messages
    type in_messages = messages
    let from_local_messages (msgs : NextMsgMaurerAPI.MaurerAPI.msgs) : (NextMsgMaurerAPI.MaurerAPI.msg * (NextMsgMaurerAPI.MaurerAPI.msg * (NextMsgMaurerAPI.MaurerAPI.msg * (NextMsgMaurerAPI.MaurerAPI.msg * NextMsgMaurerAPI.MaurerAPI.msg)))) =
                                                                                                                                                                                                                                                      (NextMsgMaurerP.MaurerP.init (fun (i : Pervasive.int) -> (NextMsgMaurerAPI.MaurerAPI.get_msg msgs i)))
    let to_local_messages : ((NextMsgMaurerAPI.MaurerAPI.msg) NextMsgMaurerP.MaurerP.arrayN -> NextMsgMaurerAPI.MaurerAPI.msgs) =
                                                                                                                                    (NextMsgMaurerAPI.MaurerAPI.mk_msgs)
    let rec send_messages : ((NextMsgMaurerAPI.MaurerAPI.msgs) NextMsgMaurerP.MaurerP.arrayN -> (NextMsgMaurerAPI.MaurerAPI.msgs) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                                                                                                     (NextMsgMaurerAPI.MaurerAPI.send_messages)
    let from_messages (xs : (local_messages) ST.P.arrayN) : (ST.pmsgs) ST.P.arrayN =
                                                                                       (ST.P.map (from_local_messages) xs)
    let to_messages (xs : (ST.pmsgs) ST.P.arrayN) : (local_messages) ST.P.arrayN =
                                                                                     (ST.P.map (to_local_messages) xs)
    let valid_local_messages (_ : ST.public_input) (_ : ST.round) (_ : local_messages) : Pervasive.bool =
                                                                                                            (Pervasive._true)
    let valid_messages (p : ST.public_input) (r : ST.round) (ms : messages) : Pervasive.bool =
                                                                                                 (ST.P.all (fun (_ : Pervasive.int) -> (valid_local_messages p r)) ms)
    let valid_msg (_ : ST.public_input) (_ : ST.round) (_ : ST.msg) : Pervasive.bool =
                                                                                         (Pervasive._true)
    let valid_pmsgs (p : ST.public_input) (r : ST.round) (ms : ST.pmsgs) : Pervasive.bool =
                                                                                              (ST.P.all (fun (_ : Pervasive.int) -> (valid_msg p r)) ms)
    let valid_ppmsgs (p : ST.public_input) (r : ST.round) (ms : ST.ppmsgs) : Pervasive.bool =
                                                                                                (ST.P.all (fun (_ : Pervasive.int) -> (valid_pmsgs p r)) ms)
    type local_state = (share * (GT.local_rand, local_in_msgs) Aux.either)
    let init_local_state (_ : ST.party) (_ : ST.public_input) (wis : share) (ris : ST.local_rand) : (share * (ST.local_rand, local_in_msgs) Aux.either) =
                                                                                                                                                            (wis , (Aux.L ris))
    let update_local_state (_ : ST.party) (_ : ST.round) (_ : ST.public_input) (_ : ST.local_input) (ins : local_in_messages) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : (share * (GT.local_rand, local_in_messages) Aux.either) =
                                                                                                                                                                                                                                                       ((fst st) , (Aux.R ins))
    let get_local_state (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : local_state =
                                                                                                                                                             (let (go) = (fun (st : local_state) (r0 : ST.round) -> (let (insr) = (ST.prget insi r0) in
                                                                                                                                                                                                                     (update_local_state i r0 x wi (to_local_messages insr) st))) in
                                                                                                                                                              (List.foldl go (init_local_state i x wi ri) (AuxList.iseq r)))
    type state = (local_state) ST.pmap
    let init_state (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                        (ST.P.imap (fun (i : ST.party) (wi_ri : (ST.local_input * ST.local_rand)) -> (init_local_state i x (fst wi_ri) (snd wi_ri))) (ST.P.zip ws rs))
    let update_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (local_in_messages) ST.pmap) (st : state) : (local_state) ST.P.arrayN =
                                                                                                                                                                               (ST.P.imap (fun (i : ST.party) (wsi_insi_sti : (ST.local_input * (local_in_messages * local_state))) -> (update_local_state i round x (Aux.fst3 wsi_insi_sti) (Aux.snd3 wsi_insi_sti) (Aux.thr3 wsi_insi_sti))) (ST.P.zip3 ws ins st))
    let get_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                                                                       (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (get_local_state i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) (ST.P.zip3 ws rs ins))
    let stateful_local_protocol_round (i : GT.party) (_ : ST.round) (g : _Gate) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : local_out_msgs =
                                                                                                                                                                (local_gate_start i g (fst st) (Aux.unL (snd st)))
    let stateful_local_protocol_end (i : GT.party) (g : _Gate) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : share =
                                                                                                                                      (local_gate_end i g (fst st) (Aux.unR (snd st)))
    let stateful_local_protocol''' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : (ST.round) List.list) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                                            (List.foldl (fun (acc : (local_state * ST.out_msgs)) (round : ST.round) -> (let (outs') = (ST.prset (snd acc) round (from_local_messages (stateful_local_protocol_round i round x (Aux.fst3 acc)))) in
                                                                                                                                                                                                                                                                                                        (let (st') = (update_local_state i round x inp (to_local_messages (ST.prget ins round)) (Aux.fst3 acc)) in
                                                                                                                                                                                                                                                                                                         (st' , outs')))) (st , (ST.prempty sz (Pervasive.witness))) rounds)
    let stateful_local_protocol'' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                               (stateful_local_protocol''' i x inp st ins sz (AuxList.iseq rounds))
    let stateful_local_protocol' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) : (local_state * ST.out_msgs) =
                                                                                                                                                                     (stateful_local_protocol'' i x inp st ins (ST.rounds x) (ST.rounds x))
    let stateful_local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                          (let (outs) = (stateful_local_protocol' i x (Aux.fst3 vi) (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) (Aux.snd3 vi)) in
                                                                                                                           (let (out) = (stateful_local_protocol_end i x (Aux.fst3 outs)) in
                                                                                                                            ((snd outs) , out)))
    let stateful_protocol_round (round : ST.round) (x : ST.public_input) (st : state) : (local_out_messages) ST.P.arrayN =
                                                                                                                             (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_round i round x sti)) st)
    let stateful_protocol_end (x : ST.public_input) (st : state) : (ST.local_output) ST.P.arrayN =
                                                                                                     (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_end i x sti)) st)
    let stateful_protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : (ST.round) List.list) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                                  (List.foldl (fun (ins_st : ((ST.in_msgs) ST.pmap * state)) (round : ST.round) -> (let (ins0) = (Aux.fst3 ins_st) in
                                                                                                                                                                                                                                                                                    (let (st0) = (snd ins_st) in
                                                                                                                                                                                                                                                                                     (let (outs) = (send_messages (stateful_protocol_round round x st0)) in
                                                                                                                                                                                                                                                                                      ((ST.pprset ins0 round (from_messages outs)) , (update_state round x ws outs st0)))))) (ins , st) rounds)
    let stateful_protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : ST.round) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                     (stateful_protocol''' x ws ins st (AuxList.iseq rounds))
    let stateful_protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                     (stateful_protocol'' x ws (ST.pprempty (ST.rounds x) (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                     (let (ins_st') = (stateful_protocol' x ws rs) in
                                                                                                                                                                                                                      (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                       (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                        (tr , outs))))
    let stateful_protocol_sz' (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                             (stateful_protocol'' x ws (ST.pprempty sz (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol_sz (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                                             (let (ins_st') = (stateful_protocol_sz' sz x ws rs) in
                                                                                                                                                                                                                                              (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                                               (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                                                (tr , outs))))
    let local_protocol_round (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.pmsgs =
                                                                                                                                                               (from_local_messages (stateful_local_protocol_round i r x (get_local_state i r x wi ri insi)))
    let local_protocol_end (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.local_output =
                                                                                                                                                     (stateful_local_protocol_end i x (get_local_state i (ST.rounds x) x wi ri insi))
    let local_protocol'' (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : ST.out_msgs =
                                                                                                                                                                                       (List.foldl (fun (outs : ST.out_msgs) (round : Pervasive.int) -> (ST.prset outs round (local_protocol_round i round x wi ri ins))) (ST.prempty sz (Pervasive.witness)) (AuxList.iseq rounds))
    let local_protocol' (i : ST.party) (x : ST.public_input) (vi : ST.view) : ST.out_msgs =
                                                                                              (local_protocol'' i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi) (ST.rounds x) (ST.rounds x))
    let local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                 (let (outs) = (local_protocol' i x vi) in
                                                                                                                  (let (out) = (local_protocol_end i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi)) in
                                                                                                                   (outs , out)))
    let protocol_round (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.pmsgs) ST.P.arrayN =
                                                                                                                                                                                         (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                                          (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_round i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol_end (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                                                                                           (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                            (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_end i x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (round1 : ST.round) (d : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (List.Iota.iota_ round1 d))
    let protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (rounds : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (AuxList.iseq rounds))
    let protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (ST.in_msgs) ST.pmap =
                                                                                                                                  (protocol'' x ws rs (ST.pprempty (ST.rounds x) (Pervasive.witness)) (ST.rounds x))
    let protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                            (let (ins) = (protocol' x ws rs) in
                                                                                                                                                                                                             (let (outs) = (protocol_end x ws rs ins) in
                                                                                                                                                                                                              (let (tr) = (ST.P.zip3 ws ins rs) in
                                                                                                                                                                                                               (tr , outs))))
    let get_view_in_msgs (j : ST.party) (vi : ST.view) : ST.rmsgs =
                                                                      (ST.P.get (Aux.snd3 vi) j)
    let get_view_out_msgs (i : ST.party) (j : ST.party) (x : ST.public_input) (vi : ST.view) : ST.rmsgs =
                                                                                                            (ST.P.get (local_protocol' i x vi) j)
    let consistent_inputs (wij : _Gate) (i : NextMsgMaurerAPI.MaurerAPI.pid) (j : NextMsgMaurerAPI.MaurerAPI.pid) (si : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) (sj : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) : Pervasive.bool =
                                                                                                                                                                                                                                                                                                       (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.add_valid_share wij si) (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.add_valid_share wij sj) (NextMsgMaurerAPI.MaurerAPI.consistent_shares i j si sj)))
    let consistent_rands (x : _Gate) (_ : ST.party) (_ : ST.party) (ri : GT.local_rand) (rj : GT.local_rand) : Pervasive.bool =
                                                                                                                                  (Pervasive._and (gate_valid_rand x ri) (gate_valid_rand x rj))
    let valid_inputs (x : ST.public_input) (ws : (ST.local_input) ST.pmap) : Pervasive.bool =
                                                                                                (Pervasive.witness)
    let valid_rands (x : ST.public_input) (ws : (ST.local_rand) ST.pmap) : Pervasive.bool =
                                                                                              (Pervasive.witness)
    let consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                (Pervasive._and (ST.eq_rmsgs (get_view_in_msgs j vi) (get_view_out_msgs j i x vj)) (Pervasive._and (Pervasive.eq (get_view_in_msgs i vj) (get_view_out_msgs i j x vi)) (Pervasive._and (consistent_inputs x i j (Aux.fst3 vi) (Aux.fst3 vj)) (consistent_rands x i j (Aux.thr3 vi) (Aux.thr3 vj)))))
    let consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                    (Pervasive.witness)
    let pairwise_consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                         (Pervasive._and (ST.valid_view x vi) (Pervasive._and (ST.valid_view x vj) (consistent_views x i j vi vj)))
    let pairwise_consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                             (Pervasive.witness)
    let view_output (i : ST.party) (x : ST.public_input) (v : ST.view) : ST.local_output =
                                                                                             (local_protocol_end i x (Aux.fst3 v) (Aux.thr3 v) (Aux.snd3 v))
    let view_outputs (x : ST.public_input) (vs : (ST.view) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                        (ST.P.imap (fun (i : ST.party) (v : ST.view) -> (view_output i x v)) vs)
    let stateful_consistent_outputs : (ST.public_input -> (ST.party -> (ST.party -> (ST.local_output -> (ST.local_output -> Pervasive.bool))))) = Pervasive.witness
    type local_state2 = (local_state * local_state)
    let stateful_consistent_views_outputs_round (r : ST.round) (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : ((local_state * local_state) * Pervasive.bool) =
                                                                                                                                                                                                                                                                                     (let (outs1) = (from_local_messages (stateful_local_protocol_round i r x (Aux.fst3 sts))) in
                                                                                                                                                                                                                                                                                      (let (outs2) = (from_local_messages (stateful_local_protocol_round j r x (snd sts))) in
                                                                                                                                                                                                                                                                                       (let (in1) = (ST.prget ins1 r) in
                                                                                                                                                                                                                                                                                        (let (in2) = (ST.prget ins2 r) in
                                                                                                                                                                                                                                                                                         (let (sts1') = (update_local_state i r x inp1 (to_local_messages in1) (Aux.fst3 sts)) in
                                                                                                                                                                                                                                                                                          (let (sts2') = (update_local_state j r x inp2 (to_local_messages in2) (snd sts)) in
                                                                                                                                                                                                                                                                                           (let (b) = (Pervasive._and (ST.eq_msg (ST.P.get outs1 j) (ST.P.get in2 i)) (ST.eq_msg (ST.P.get outs2 i) (ST.P.get in1 j))) in
                                                                                                                                                                                                                                                                                            ((sts1' , sts2') , b))))))))
    let stateful_consistent_views_outputs''' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) (rounds : (ST.round) List.list) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                                                    (let (go) = (fun (stb : (local_state2 * Pervasive.bool)) (r : ST.round) -> (let (stb') = (stateful_consistent_views_outputs_round r x i j inp1 inp2 ins1 ins2 (fst stb)) in
                                                                                                                                                                                                                                                                                                                                                                ((fst stb') , (Pervasive._and (snd stb) (snd stb'))))) in
                                                                                                                                                                                                                                                                                     (List.foldl go (sts , (Pervasive._true)) rounds))
    let stateful_consistent_views_outputs'' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                   (stateful_consistent_views_outputs''' x i j inp1 inp2 ins1 ins2 sts (AuxList.iseq (ST.rounds x)))
    let stateful_consistent_views_outputs' (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                   (let (st1) = (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) in
                                                                                                                                                                    (let (st2) = (init_local_state j x (Aux.fst3 vj) (Aux.thr3 vj)) in
                                                                                                                                                                     (let (outsb) = (stateful_consistent_views_outputs'' x i j (Aux.fst3 vi) (Aux.fst3 vj) (Aux.snd3 vi) (Aux.snd3 vj) (st1 , st2)) in
                                                                                                                                                                      outsb)))
    let stateful_consistent_views_outputs (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                                 (let (outsb) = (stateful_consistent_views_outputs' x i j vi vj) in
                                                                                                                                                  (let (outs1) = (Aux.fst3 (fst outsb)) in
                                                                                                                                                   (let (outs2) = (snd (fst outsb)) in
                                                                                                                                                    (let (b) = (snd outsb) in
                                                                                                                                                     (let (out1) = (stateful_local_protocol_end i x outs1) in
                                                                                                                                                      (let (out2) = (stateful_local_protocol_end j x outs2) in
                                                                                                                                                       (Pervasive._and b (stateful_consistent_outputs x i j out1 out2))))))))
    let g_protocol (x : _Gate) (ws : (share) GT.pmap) (cs : (GT.local_rand) GT.pmap) : (((share * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))) GT.P.arrayN * (share) GT.P.arrayN) =
                                                                                                                                                                                                             (let (outs) = (GT.P.imap (fun (i : GT.party) (wc : (share * GT.local_rand)) -> (local_gate_start i x (fst wc) (snd wc))) (GT.P.zip ws cs)) in
                                                                                                                                                                                                              (let (ins) = (send_messages outs) in
                                                                                                                                                                                                               (let (o) = (GT.P.imap (fun (i : GT.party) (wi : (share * local_in_msgs)) -> (local_gate_end i x (fst wi) (snd wi))) (GT.P.zip ws ins)) in
                                                                                                                                                                                                                (let (rins) = (GT.P.map (fun (bin : local_messages) -> (GT.P.map (fun (msg : GT.msg) -> (NextMsgArray.Array.init (Pervasive.mk_int 1) (fun (j : Pervasive.int) -> if (Pervasive.eq j (Pervasive.mk_int 0)) then msg else (Pervasive.witness)))) (from_local_messages bin))) ins) in
                                                                                                                                                                                                                 (let (tr) = (GT.P.zip3 ws rins cs) in
                                                                                                                                                                                                                  (tr , o))))))
end
module MaurerGate = struct
    type gate = | Add of MaurerAdd._Gate
                | SMul of MaurerSMul._Gate
                | Const of MaurerConst._Gate
                | Mul of MaurerMul._Gate
    let gate_start (i : MaurerMul.GT.party) (g : gate) (st : MaurerMul.share) (r : (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.rand) Aux.either) : (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either =
                                                                                                                                                                                                                    begin match g with
                                                                                                                                                                                                                    | (Add wij) -> (Aux.L (Pervasive.tt))
                                                                                                                                                                                                                    | (SMul wij) -> (Aux.L (Pervasive.tt))
                                                                                                                                                                                                                    | (Const wij) -> (Aux.L (Pervasive.tt))
                                                                                                                                                                                                                    | (Mul wij) -> (Aux.R (MaurerMul.local_gate_start i wij st (Aux.unR r)))
                                                                                                                                                                                                                    end
    let gate_end (i : MaurerAdd.GT.party) (g : gate) (st : MaurerAdd.share) (ins : (MaurerAdd.local_in_msgs, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either) : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) =
                                                                                                                                                                                                                                         begin match g with
                                                                                                                                                                                                                                         | (Add wij) -> (MaurerAdd.local_gate_end i wij st (Aux.unL ins))
                                                                                                                                                                                                                                         | (SMul wij) -> (MaurerSMul.local_gate_end i wij st (Aux.unL ins))
                                                                                                                                                                                                                                         | (Const wij) -> (MaurerConst.local_gate_end i wij st (Aux.unL ins))
                                                                                                                                                                                                                                         | (Mul wij) -> (MaurerMul.local_gate_end i wij st (Aux.unR ins))
                                                                                                                                                                                                                                         end
    let gate_consistent_inputs (g : gate) (i : NextMsgMaurerAPI.MaurerAPI.pid) (j : NextMsgMaurerAPI.MaurerAPI.pid) (si : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) (sj : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) : Pervasive.bool =
                                                                                                                                                                                                                                                                                                         begin match g with
                                                                                                                                                                                                                                                                                                         | (Add wij) -> (MaurerAdd.consistent_inputs wij i j si sj)
                                                                                                                                                                                                                                                                                                         | (SMul wij) -> (MaurerSMul.consistent_inputs wij i j si sj)
                                                                                                                                                                                                                                                                                                         | (Const wij) -> (MaurerConst.consistent_inputs wij i j si sj)
                                                                                                                                                                                                                                                                                                         | (Mul wij) -> (MaurerMul.consistent_inputs wij i j si sj)
                                                                                                                                                                                                                                                                                                         end
    let gate_valid_local_messages (g : gate) (r : MaurerAdd.ST.round) (rs : (MaurerAdd.local_messages, MaurerMul.local_messages) Aux.either) : Pervasive.bool =
                                                                                                                                                                  begin match g with
                                                                                                                                                                  | (Add wij) -> (Pervasive._and (Aux.isL rs) (MaurerAdd.valid_local_messages wij r (Aux.unL rs)))
                                                                                                                                                                  | (SMul wij) -> (Pervasive._and (Aux.isL rs) (MaurerSMul.valid_local_messages wij r (Aux.unL rs)))
                                                                                                                                                                  | (Const wij) -> (Pervasive._and (Aux.isL rs) (MaurerConst.valid_local_messages wij r (Aux.unL rs)))
                                                                                                                                                                  | (Mul wij) -> (Pervasive._and (Aux.isR rs) (MaurerMul.valid_local_messages wij r (Aux.unR rs)))
                                                                                                                                                                  end
    let gate_valid_msg (g : gate) (r : MaurerAdd.ST.round) (rs : (MaurerAdd.ST.msg, MaurerMul.ST.msg) Aux.either) : Pervasive.bool =
                                                                                                                                       begin match g with
                                                                                                                                       | (Add wij) -> (Pervasive._and (Aux.isL rs) (MaurerAdd.valid_msg wij r (Aux.unL rs)))
                                                                                                                                       | (SMul wij) -> (Pervasive._and (Aux.isL rs) (MaurerSMul.valid_msg wij r (Aux.unL rs)))
                                                                                                                                       | (Const wij) -> (Pervasive._and (Aux.isL rs) (MaurerConst.valid_msg wij r (Aux.unL rs)))
                                                                                                                                       | (Mul wij) -> (Pervasive._and (Aux.isR rs) (MaurerMul.valid_msg wij r (Aux.unR rs)))
                                                                                                                                       end
    let gate_to_local_messages (ms : ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either) NextMsgMaurerP.MaurerP.arrayN) : (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either =
                                                                                                                                                                                                     if (NextMsgMaurerP.MaurerP.all (fun (_ : Pervasive.int) -> (Aux.isR)) ms) then (Aux.R (NextMsgMaurerAPI.MaurerAPI.mk_msgs (NextMsgMaurerP.MaurerP.map (Aux.unR) ms))) else (Aux.L (Pervasive.tt))
    let gate_from_local_messages (ms : (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either) : ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either)))) =
                                                                                                                                                                                                                                                                                                                                                                                                                                       begin match ms with
                                                                                                                                                                                                                                                                                                                                                                                                                                       | (Aux.L tt) -> (NextMsgMaurerP.MaurerP.init (fun (_ : Pervasive.int) -> (Aux.L tt)))
                                                                                                                                                                                                                                                                                                                                                                                                                                       | (Aux.R ms0) -> (NextMsgMaurerP.MaurerP.init (fun (i : Pervasive.int) -> (Aux.R (NextMsgMaurerAPI.MaurerAPI.get_msg ms0 i))))
                                                                                                                                                                                                                                                                                                                                                                                                                                       end
    let gate_send_messages (ms : ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either) NextMsgMaurerP.MaurerP.arrayN) : ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either) NextMsgMaurerP.MaurerP.arrayN =
                                                                                                                                                                                                                                  if (NextMsgMaurerP.MaurerP.all (fun (_ : Pervasive.int) -> (Aux.isR)) ms) then (NextMsgMaurerP.MaurerP.map (fun (x : NextMsgMaurerAPI.MaurerAPI.msgs) -> (Aux.R x)) (NextMsgMaurerAPI.MaurerAPI.send_messages (NextMsgMaurerP.MaurerP.map (Aux.unR) ms))) else ms
    let gate_valid_rand' (g : gate) (rs : (MaurerAdd.GT.local_rand, MaurerMul.GT.local_rand) Aux.either) : Pervasive.bool =
                                                                                                                              begin match g with
                                                                                                                              | (Add wij) -> (Pervasive._and (Aux.isL rs) (MaurerAdd.gate_valid_rand wij (Aux.unL rs)))
                                                                                                                              | (SMul wij) -> (Pervasive._and (Aux.isL rs) (MaurerSMul.gate_valid_rand wij (Aux.unL rs)))
                                                                                                                              | (Const wij) -> (Pervasive._and (Aux.isL rs) (MaurerConst.gate_valid_rand wij (Aux.unL rs)))
                                                                                                                              | (Mul wij) -> (Pervasive._and (Aux.isR rs) (MaurerMul.gate_valid_rand wij (Aux.unR rs)))
                                                                                                                              end
    type _Gate = gate
    type share = (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)
    type local_msgs = (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either
    type local_in_msgs = local_msgs
    type local_out_msgs = local_msgs
    module GT = struct
        type public_input = _Gate
        module P = struct
            let rec size : Pervasive.int =
                                             (NextMsgMaurerP.MaurerP.size)
            type ('a) arrayN = ('a) NextMsgMaurerP.MaurerP.arrayN
            let rec get : (('a) Aux.array5 -> (Pervasive.int -> 'a)) =
                                                                         (NextMsgMaurerP.MaurerP.get)
            let rec set : (('a) Aux.array5 -> (Pervasive.int -> ('a -> ('a * ('a * ('a * ('a) Aux.array2)))))) =
                                                                                                                   (NextMsgMaurerP.MaurerP.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a * ('a * ('a * ('a * 'a))))) =
                                                                                         (NextMsgMaurerP.MaurerP.init)
            let rec of_list : (('a) List.list -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                         (NextMsgMaurerP.MaurerP.of_list)
            let rec to_list : (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) List.list) =
                                                                                         (NextMsgMaurerP.MaurerP.to_list)
            let rec to_assoc : (('a) NextMsgMaurerP.MaurerP.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                                            (NextMsgMaurerP.MaurerP.to_assoc)
            let rec create : ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                            (NextMsgMaurerP.MaurerP.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                              (NextMsgMaurerP.MaurerP.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('b) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                             (NextMsgMaurerP.MaurerP.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> (('b) NextMsgMaurerP.MaurerP.arrayN -> ('c) NextMsgMaurerP.MaurerP.arrayN))) =
                                                                                                                                                                           (NextMsgMaurerP.MaurerP.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                                           (NextMsgMaurerP.MaurerP.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool)) =
                                                                                                                                    (NextMsgMaurerP.MaurerP.all)
            let rec allsame : (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool) =
                                                                                         (NextMsgMaurerP.MaurerP.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) NextMsgMaurerP.MaurerP.arrayN) List.list -> (('b) List.list) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                                                                    (NextMsgMaurerP.MaurerP.concat)
        end
        let parties : Pervasive.int =
                                        (P.size)
        type party = Pervasive.int
        let partyset : NextMsgISet.ISet.iset =
                                                 (NextMsgISet.ISet.iset (parties))
        type round = Pervasive.int
        let rounds (_ : public_input) : Pervasive.int =
                                                          (Pervasive.mk_int 1)
        let roundset (p : public_input) : NextMsgISet.ISet.iset =
                                                                    (NextMsgISet.ISet.iset (rounds p))
        type ('a) pmap = ('a) P.arrayN
        type ('a) rmap = ('a) NextMsgArray.Array.array
        type ('a) prmap = (('a) rmap) pmap
        type ('a) ppmap = (('a) pmap) pmap
        type ('a) pprmap = (('a) rmap) ppmap
        type local_input = share
        type local_output = share
        type local_rand = (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.rand) Aux.either
        type msg = (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either
        type pmsgs = (msg) pmap
        type rmsgs = (msg) rmap
        type prmsgs = (rmsgs) pmap
        type ppmsgs = (pmsgs) pmap
        type pprmsgs = (prmsgs) pmap
        type in_msgs = prmsgs
        type out_msgs = prmsgs
        type view = (local_input * (in_msgs * local_rand))
        type trace = (view) pmap
        let rec eq_msg (m1 : (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either) (m2 : (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either) : Pervasive.bool =
                                                                                                                                                                                  (Aux.eq_either (Pervasive.eq) (NextMsgMaurerAPI.MaurerAPI.eq_msg) m1 m2)
        let eq_pmsgs (m1 : pmsgs) (m2 : pmsgs) : Pervasive.bool =
                                                                    (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (P.get m1 i) (P.get m2 i))) (P.size))
        let eq_rmsgs (m1 : rmsgs) (m2 : rmsgs) : Pervasive.bool =
                                                                    (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size m1) (NextMsgArray.Array.size m2)) (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (NextMsgArray.Array.get m1 i) (NextMsgArray.Array.get m2 i))) (NextMsgArray.Array.size m1)))
        let pinit (f : (party -> 'a)) : ('a) P.arrayN =
                                                          (P.init f)
        let ppinit (f : (party -> (party -> 'a))) : (('a) P.arrayN) P.arrayN =
                                                                                 (pinit (fun (i : party) -> (pinit (f i))))
        let prempty (sz : Pervasive.int) (v : 'a) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                 (pinit (fun (_ : party) -> (NextMsgArray.Array.create sz v)))
        let pprempty (sz : Pervasive.int) (v : 'a) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                             (ppinit (fun (_ : party) (_ : party) -> (NextMsgArray.Array.create sz v)))
        let ppswap (m : ('a) ppmap) : (('a) P.arrayN) P.arrayN =
                                                                   (ppinit (fun (j : Pervasive.int) (i : Pervasive.int) -> (P.get (P.get m i) j)))
        let prget (xs : ('a) prmap) (r : round) : ('a) P.arrayN =
                                                                    (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.get (P.get xs i) r)))
        let pprget (xs : ('a) pprmap) (r : round) : (('a) P.arrayN) P.arrayN =
                                                                                 (ppinit (fun (i : Pervasive.int) (j : Pervasive.int) -> (NextMsgArray.Array.get (P.get (P.get xs i) j) r)))
        let prset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.merge (fun (x0 : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set x0 n y)) xs x)
        let prext (sz : Pervasive.int) (xs : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.init sz (fun (j : Pervasive.int) -> if (Pervasive._and (Int.le (Pervasive.mk_int 0) j) (Int.lt j (NextMsgArray.Array.size (P.get xs i)))) then (NextMsgArray.Array.get (P.get xs i) j) else (Pervasive.witness)))))
        let prextset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                          (prset (prext (Int.plus n (Pervasive.mk_int 1)) xs) n x)
        let pprset (xs : ('a) pprmap) (n : round) (x : ('a) ppmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                             (P.merge (P.merge (fun (ys : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set ys n y))) xs x)
        let prfilter (p : (round -> Pervasive.bool)) (ins : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) ins)
        let pprfilter (p : (round -> Pervasive.bool)) (ins : ('a) pprmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                                    (P.map (fun (xs : (('a) NextMsgArray.Array.array) P.arrayN) -> (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) xs)) ins)
        let rdom (sz : Pervasive.int) (round : round) (xs : ('a) rmap) : Pervasive.bool =
                                                                                            (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size xs) sz) (Pervasive.witness))
        let prdom (sz : Pervasive.int) (round : round) (xs : ('a) prmap) : Pervasive.bool =
                                                                                              (P.all (fun (_ : Pervasive.int) -> (rdom sz round)) xs)
        let pprdom (sz : Pervasive.int) (round : round) (xs : ('a) pprmap) : Pervasive.bool =
                                                                                                (P.all (fun (_ : Pervasive.int) -> (prdom sz round)) xs)
        let rlist (sz : Pervasive.int) (xs : ('a) List.list) : ('a) NextMsgArray.Array.array =
                                                                                                 (List.foldl (fun (rs : ('a) NextMsgArray.Array.array) (i : Pervasive.int) -> (NextMsgArray.Array.set rs i (List.nth (Pervasive.witness) xs i))) (NextMsgArray.Array.create sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let prlist (sz : Pervasive.int) (xs : (pmsgs) List.list) : (msg) prmap =
                                                                                   (List.foldl (fun (rs : (msg) prmap) (i : Pervasive.int) -> (prset rs i (List.nth (Pervasive.witness) xs i))) (prempty sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let pcons (x : ('a) pmap) (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                               (P.merge (fun (x0 : 'a) (xs0 : ('a) List.list) -> (AuxList.cons x0 xs0)) x xs)
        let phead (xs : (('a) List.list) pmap) : ('a) P.arrayN =
                                                                   (P.map (List.head (Pervasive.witness)) xs)
        let pbehead (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                 (P.map (List.behead) xs)
        let prcons (xs : (('a) List.list) pmap) (x : ('a) pmap) : (('a) List.list) P.arrayN =
                                                                                                (P.merge (List.rcons) xs x)
        let pcat (xs : (('a) List.list) pmap) (ys : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                                           (P.merge (fun (x : ('a) List.list) (y : ('a) List.list) -> (AuxList.cat x y)) xs ys)
        let ppcons (x : ('a) ppmap) (xs : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                             (P.merge (pcons) x xs)
        let pprcons (xs : (('a) List.list) ppmap) (x : ('a) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                              (P.merge (prcons) xs x)
        let ppcat (xs : (('a) List.list) ppmap) (ys : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                                         (P.merge (pcat) xs ys)
        let prmsgs_up_to (round : round) (ins : prmsgs) : ((msg) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (prfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let pprmsgs_up_to (round : round) (ins : pprmsgs) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                     (pprfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let get_trace_inputs (tr : trace) : (local_input) P.arrayN =
                                                                       (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.fst3 x)) tr)
        let get_trace_in_msgs (tr : trace) : (in_msgs) P.arrayN =
                                                                    (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.snd3 x)) tr)
        let get_trace_rands (tr : trace) : (local_rand) P.arrayN =
                                                                     (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.thr3 x)) tr)
        let get_view (i : party) (tr : trace) : view =
                                                         (P.get tr i)
        let get_trace_in_msgs_round (round : round) (tr : trace) : ((msg) P.arrayN) P.arrayN =
                                                                                                 (pprget (get_trace_in_msgs tr) round)
        let get_view_in_msgs_round (round : round) (v : view) : (msg) P.arrayN =
                                                                                   (prget (Aux.snd3 v) round)
        let add_view_in_msgs (r : round) (ins : pmsgs) (v : view) : (local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand)) =
                                                                                                                                                 ((Aux.fst3 v) , ((prset (Aux.snd3 v) r ins) , (Aux.thr3 v)))
        let get_trace_in_msgs_up_to (round : round) (tr : trace) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                            (pprmsgs_up_to round (get_trace_in_msgs tr))
        let add_trace_in_msgs (r : round) (ins : ppmsgs) (tr : trace) : ((local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand))) P.arrayN =
                                                                                                                                                                (P.map (fun (ins_v : (pmsgs * view)) -> (add_view_in_msgs r (Aux.fst3 ins_v) (snd ins_v))) (P.zip ins tr))
        let valid_trace (x : public_input) (tr : trace) : Pervasive.bool =
                                                                             (pprdom (rounds x) (rounds x) (get_trace_in_msgs tr))
        let valid_view (x : public_input) (v : view) : Pervasive.bool =
                                                                          (prdom (rounds x) (rounds x) (Aux.snd3 v))
    end
    let local_gate_start : (MaurerMul.GT.party -> (gate -> (MaurerMul.share -> ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.rand) Aux.either -> (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either)))) =
                                                                                                                                                                                                                     (gate_start)
    let local_gate_end : (MaurerAdd.GT.party -> (gate -> (MaurerAdd.share -> ((MaurerAdd.local_in_msgs, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either -> (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st))))) =
                                                                                                                                                                                                                                        (gate_end)
    let gate_valid_rand : (gate -> ((MaurerAdd.GT.local_rand, MaurerMul.GT.local_rand) Aux.either -> Pervasive.bool)) =
                                                                                                                          (gate_valid_rand')
    let gate_valid_rands (x : _Gate) (cs : (GT.local_rand) GT.P.arrayN) : Pervasive.bool =
                                                                                             (GT.P.all (fun (_ : Pervasive.int) (c : GT.local_rand) -> (gate_valid_rand x c)) cs)
    module ST = struct
        type public_input = GT.public_input
        module P = struct
            let rec size : Pervasive.int =
                                             (GT.P.size)
            type ('a) arrayN = ('a) GT.P.arrayN
            let rec get : (('a) GT.P.arrayN -> (Pervasive.int -> 'a)) =
                                                                          (GT.P.get)
            let rec set : (('a) GT.P.arrayN -> (Pervasive.int -> ('a -> ('a) GT.P.arrayN))) =
                                                                                                (GT.P.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a) GT.P.arrayN) =
                                                                           (GT.P.init)
            let rec of_list : (('a) List.list -> ('a) GT.P.arrayN) =
                                                                       (GT.P.of_list)
            let rec to_list : (('a) GT.P.arrayN -> ('a) List.list) =
                                                                       (GT.P.to_list)
            let rec to_assoc : (('a) GT.P.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                          (GT.P.to_assoc)
            let rec create : ('a -> ('a) GT.P.arrayN) =
                                                          (GT.P.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) GT.P.arrayN)) =
                                                                            (GT.P.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) GT.P.arrayN -> ('b) GT.P.arrayN)) =
                                                                                                         (GT.P.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) GT.P.arrayN -> (('b) GT.P.arrayN -> ('c) GT.P.arrayN))) =
                                                                                                                     (GT.P.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) GT.P.arrayN -> ('a) GT.P.arrayN)) =
                                                                                                                       (GT.P.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) GT.P.arrayN -> Pervasive.bool)) =
                                                                                                                  (GT.P.all)
            let rec allsame : (('a) GT.P.arrayN -> Pervasive.bool) =
                                                                       (GT.P.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) GT.P.arrayN) List.list -> (('b) List.list) GT.P.arrayN) =
                                                                                                (GT.P.concat)
        end
        let rec parties : Pervasive.int =
                                            (GT.parties)
        type party = GT.party
        let rec partyset : NextMsgISet.ISet.iset =
                                                     (GT.partyset)
        type round = GT.round
        let rec rounds : (GT.public_input -> Pervasive.int) =
                                                                (GT.rounds)
        let rec roundset : (GT.public_input -> NextMsgISet.ISet.iset) =
                                                                          (GT.roundset)
        type ('a) pmap = ('a) GT.pmap
        type ('a) rmap = ('a) GT.rmap
        type ('a) prmap = ('a) GT.prmap
        type ('a) ppmap = ('a) GT.ppmap
        type ('a) pprmap = ('a) GT.pprmap
        type local_input = GT.local_input
        type local_output = GT.local_output
        type local_rand = GT.local_rand
        type msg = GT.msg
        type pmsgs = GT.pmsgs
        type rmsgs = GT.rmsgs
        type prmsgs = GT.prmsgs
        type ppmsgs = GT.ppmsgs
        type pprmsgs = GT.pprmsgs
        type in_msgs = GT.in_msgs
        type out_msgs = GT.out_msgs
        type view = GT.view
        type trace = GT.trace
        let rec eq_msg : (GT.msg -> (GT.msg -> Pervasive.bool)) =
                                                                    (GT.eq_msg)
        let rec eq_pmsgs : (GT.pmsgs -> (GT.pmsgs -> Pervasive.bool)) =
                                                                          (GT.eq_pmsgs)
        let rec eq_rmsgs : (GT.rmsgs -> (GT.rmsgs -> Pervasive.bool)) =
                                                                          (GT.eq_rmsgs)
        let rec pinit : ((GT.party -> 'a) -> ('a) GT.P.arrayN) =
                                                                   (GT.pinit)
        let rec ppinit : ((GT.party -> (GT.party -> 'a)) -> (('a) GT.P.arrayN) GT.P.arrayN) =
                                                                                                (GT.ppinit)
        let rec prempty : (Pervasive.int -> ('a -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                     (GT.prempty)
        let rec pprempty : (Pervasive.int -> ('a -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                    (GT.pprempty)
        let rec ppswap : (('a) GT.ppmap -> (('a) GT.P.arrayN) GT.P.arrayN) =
                                                                               (GT.ppswap)
        let rec prget : (('a) GT.prmap -> (GT.round -> ('a) GT.P.arrayN)) =
                                                                              (GT.prget)
        let rec pprget : (('a) GT.pprmap -> (GT.round -> (('a) GT.P.arrayN) GT.P.arrayN)) =
                                                                                              (GT.pprget)
        let rec prset : (('a) GT.prmap -> (Pervasive.int -> (('a) GT.pmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN))) =
                                                                                                                                (GT.prset)
        let rec prext : (Pervasive.int -> (('a) GT.prmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                              (GT.prext)
        let rec prextset : (('a) GT.prmap -> (Pervasive.int -> (('a) GT.pmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN))) =
                                                                                                                                   (GT.prextset)
        let rec pprset : (('a) GT.pprmap -> (GT.round -> (('a) GT.ppmap -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN))) =
                                                                                                                                            (GT.pprset)
        let rec prfilter : ((GT.round -> Pervasive.bool) -> (('a) GT.prmap -> (('a) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                                                (GT.prfilter)
        let rec pprfilter : ((GT.round -> Pervasive.bool) -> (('a) GT.pprmap -> ((('a) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                                (GT.pprfilter)
        let rec rdom : (Pervasive.int -> (GT.round -> (('a) GT.rmap -> Pervasive.bool))) =
                                                                                             (GT.rdom)
        let rec prdom : (Pervasive.int -> (GT.round -> (('a) GT.prmap -> Pervasive.bool))) =
                                                                                               (GT.prdom)
        let rec pprdom : (Pervasive.int -> (GT.round -> (('a) GT.pprmap -> Pervasive.bool))) =
                                                                                                 (GT.pprdom)
        let rec rlist : (Pervasive.int -> (('a) List.list -> ('a) NextMsgArray.Array.array)) =
                                                                                                 (GT.rlist)
        let rec prlist : (Pervasive.int -> ((GT.pmsgs) List.list -> (GT.msg) GT.prmap)) =
                                                                                            (GT.prlist)
        let rec pcons : (('a) GT.pmap -> ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                         (GT.pcons)
        let rec phead : ((('a) List.list) GT.pmap -> ('a) GT.P.arrayN) =
                                                                           (GT.phead)
        let rec pbehead : ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN) =
                                                                                         (GT.pbehead)
        let rec prcons : ((('a) List.list) GT.pmap -> (('a) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                          (GT.prcons)
        let rec pcat : ((('a) List.list) GT.pmap -> ((('a) List.list) GT.pmap -> (('a) List.list) GT.P.arrayN)) =
                                                                                                                    (GT.pcat)
        let rec ppcons : (('a) GT.ppmap -> ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                          (GT.ppcons)
        let rec pprcons : ((('a) List.list) GT.ppmap -> (('a) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                           (GT.pprcons)
        let rec ppcat : ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.ppmap -> ((('a) List.list) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                     (GT.ppcat)
        let rec prmsgs_up_to : (GT.round -> (GT.prmsgs -> ((GT.msg) NextMsgArray.Array.array) GT.P.arrayN)) =
                                                                                                                (GT.prmsgs_up_to)
        let rec pprmsgs_up_to : (GT.round -> (GT.pprmsgs -> (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                (GT.pprmsgs_up_to)
        let rec get_trace_inputs : (GT.trace -> (GT.local_input) GT.P.arrayN) =
                                                                                  (GT.get_trace_inputs)
        let rec get_trace_in_msgs : (GT.trace -> (GT.in_msgs) GT.P.arrayN) =
                                                                               (GT.get_trace_in_msgs)
        let rec get_trace_rands : (GT.trace -> (GT.local_rand) GT.P.arrayN) =
                                                                                (GT.get_trace_rands)
        let rec get_view : (GT.party -> (GT.trace -> GT.view)) =
                                                                   (GT.get_view)
        let rec get_trace_in_msgs_round : (GT.round -> (GT.trace -> ((GT.msg) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                             (GT.get_trace_in_msgs_round)
        let rec get_view_in_msgs_round : (GT.round -> (GT.view -> (GT.msg) GT.P.arrayN)) =
                                                                                             (GT.get_view_in_msgs_round)
        let rec add_view_in_msgs : (GT.round -> (GT.pmsgs -> (GT.view -> (GT.local_input * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))))) =
                                                                                                                                                                     (GT.add_view_in_msgs)
        let rec get_trace_in_msgs_up_to : (GT.round -> (GT.trace -> (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN) GT.P.arrayN)) =
                                                                                                                                        (GT.get_trace_in_msgs_up_to)
        let rec add_trace_in_msgs : (GT.round -> (GT.ppmsgs -> (GT.trace -> ((GT.local_input * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))) GT.P.arrayN))) =
                                                                                                                                                                                      (GT.add_trace_in_msgs)
        let rec valid_trace : (GT.public_input -> (GT.trace -> Pervasive.bool)) =
                                                                                    (GT.valid_trace)
        let rec valid_view : (GT.public_input -> (GT.view -> Pervasive.bool)) =
                                                                                  (GT.valid_view)
    end
    type local_messages = local_msgs
    type messages = (local_messages) ST.pmap
    type local_out_messages = local_messages
    type local_in_messages = local_messages
    type out_messages = messages
    type in_messages = messages
    let from_local_messages : ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either -> ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either))))) =
                                                                                                                                                                                                                                                                                                                                                                                                                                (gate_from_local_messages)
    let to_local_messages : (((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either) NextMsgMaurerP.MaurerP.arrayN -> (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either) =
                                                                                                                                                                                              (gate_to_local_messages)
    let send_messages : (((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either) NextMsgMaurerP.MaurerP.arrayN -> ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                                                                                                                                                           (gate_send_messages)
    let from_messages (xs : (local_messages) ST.P.arrayN) : (ST.pmsgs) ST.P.arrayN =
                                                                                       (ST.P.map (from_local_messages) xs)
    let to_messages (xs : (ST.pmsgs) ST.P.arrayN) : (local_messages) ST.P.arrayN =
                                                                                     (ST.P.map (to_local_messages) xs)
    let valid_local_messages : (gate -> (MaurerAdd.ST.round -> ((MaurerAdd.local_messages, MaurerMul.local_messages) Aux.either -> Pervasive.bool))) =
                                                                                                                                                         (gate_valid_local_messages)
    let valid_messages (p : ST.public_input) (r : ST.round) (ms : messages) : Pervasive.bool =
                                                                                                 (ST.P.all (fun (_ : Pervasive.int) -> (valid_local_messages p r)) ms)
    let valid_msg : (gate -> (MaurerAdd.ST.round -> ((MaurerAdd.ST.msg, MaurerMul.ST.msg) Aux.either -> Pervasive.bool))) =
                                                                                                                              (gate_valid_msg)
    let valid_pmsgs (p : ST.public_input) (r : ST.round) (ms : ST.pmsgs) : Pervasive.bool =
                                                                                              (ST.P.all (fun (_ : Pervasive.int) -> (valid_msg p r)) ms)
    let valid_ppmsgs (p : ST.public_input) (r : ST.round) (ms : ST.ppmsgs) : Pervasive.bool =
                                                                                                (ST.P.all (fun (_ : Pervasive.int) -> (valid_pmsgs p r)) ms)
    type local_state = (share * (GT.local_rand, local_in_msgs) Aux.either)
    let init_local_state (_ : ST.party) (_ : ST.public_input) (wis : share) (ris : ST.local_rand) : (share * (ST.local_rand, local_in_msgs) Aux.either) =
                                                                                                                                                            (wis , (Aux.L ris))
    let update_local_state (_ : ST.party) (_ : ST.round) (_ : ST.public_input) (_ : ST.local_input) (ins : local_in_messages) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : (share * (GT.local_rand, local_in_messages) Aux.either) =
                                                                                                                                                                                                                                                       ((fst st) , (Aux.R ins))
    let get_local_state (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : local_state =
                                                                                                                                                             (let (go) = (fun (st : local_state) (r0 : ST.round) -> (let (insr) = (ST.prget insi r0) in
                                                                                                                                                                                                                     (update_local_state i r0 x wi (to_local_messages insr) st))) in
                                                                                                                                                              (List.foldl go (init_local_state i x wi ri) (AuxList.iseq r)))
    type state = (local_state) ST.pmap
    let init_state (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                        (ST.P.imap (fun (i : ST.party) (wi_ri : (ST.local_input * ST.local_rand)) -> (init_local_state i x (fst wi_ri) (snd wi_ri))) (ST.P.zip ws rs))
    let update_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (local_in_messages) ST.pmap) (st : state) : (local_state) ST.P.arrayN =
                                                                                                                                                                               (ST.P.imap (fun (i : ST.party) (wsi_insi_sti : (ST.local_input * (local_in_messages * local_state))) -> (update_local_state i round x (Aux.fst3 wsi_insi_sti) (Aux.snd3 wsi_insi_sti) (Aux.thr3 wsi_insi_sti))) (ST.P.zip3 ws ins st))
    let get_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                                                                       (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (get_local_state i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) (ST.P.zip3 ws rs ins))
    let stateful_local_protocol_round (i : GT.party) (_ : ST.round) (g : _Gate) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : local_out_msgs =
                                                                                                                                                                (local_gate_start i g (fst st) (Aux.unL (snd st)))
    let stateful_local_protocol_end (i : GT.party) (g : _Gate) (st : (share * (GT.local_rand, local_in_msgs) Aux.either)) : share =
                                                                                                                                      (local_gate_end i g (fst st) (Aux.unR (snd st)))
    let stateful_local_protocol''' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : (ST.round) List.list) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                                            (List.foldl (fun (acc : (local_state * ST.out_msgs)) (round : ST.round) -> (let (outs') = (ST.prset (snd acc) round (from_local_messages (stateful_local_protocol_round i round x (Aux.fst3 acc)))) in
                                                                                                                                                                                                                                                                                                        (let (st') = (update_local_state i round x inp (to_local_messages (ST.prget ins round)) (Aux.fst3 acc)) in
                                                                                                                                                                                                                                                                                                         (st' , outs')))) (st , (ST.prempty sz (Pervasive.witness))) rounds)
    let stateful_local_protocol'' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                               (stateful_local_protocol''' i x inp st ins sz (AuxList.iseq rounds))
    let stateful_local_protocol' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) : (local_state * ST.out_msgs) =
                                                                                                                                                                     (stateful_local_protocol'' i x inp st ins (ST.rounds x) (ST.rounds x))
    let stateful_local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                          (let (outs) = (stateful_local_protocol' i x (Aux.fst3 vi) (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) (Aux.snd3 vi)) in
                                                                                                                           (let (out) = (stateful_local_protocol_end i x (Aux.fst3 outs)) in
                                                                                                                            ((snd outs) , out)))
    let stateful_protocol_round (round : ST.round) (x : ST.public_input) (st : state) : (local_out_messages) ST.P.arrayN =
                                                                                                                             (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_round i round x sti)) st)
    let stateful_protocol_end (x : ST.public_input) (st : state) : (ST.local_output) ST.P.arrayN =
                                                                                                     (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_end i x sti)) st)
    let stateful_protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : (ST.round) List.list) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                                  (List.foldl (fun (ins_st : ((ST.in_msgs) ST.pmap * state)) (round : ST.round) -> (let (ins0) = (Aux.fst3 ins_st) in
                                                                                                                                                                                                                                                                                    (let (st0) = (snd ins_st) in
                                                                                                                                                                                                                                                                                     (let (outs) = (send_messages (stateful_protocol_round round x st0)) in
                                                                                                                                                                                                                                                                                      ((ST.pprset ins0 round (from_messages outs)) , (update_state round x ws outs st0)))))) (ins , st) rounds)
    let stateful_protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : ST.round) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                     (stateful_protocol''' x ws ins st (AuxList.iseq rounds))
    let stateful_protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                     (stateful_protocol'' x ws (ST.pprempty (ST.rounds x) (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                     (let (ins_st') = (stateful_protocol' x ws rs) in
                                                                                                                                                                                                                      (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                       (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                        (tr , outs))))
    let stateful_protocol_sz' (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                             (stateful_protocol'' x ws (ST.pprempty sz (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol_sz (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                                             (let (ins_st') = (stateful_protocol_sz' sz x ws rs) in
                                                                                                                                                                                                                                              (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                                               (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                                                (tr , outs))))
    let local_protocol_round (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.pmsgs =
                                                                                                                                                               (from_local_messages (stateful_local_protocol_round i r x (get_local_state i r x wi ri insi)))
    let local_protocol_end (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.local_output =
                                                                                                                                                     (stateful_local_protocol_end i x (get_local_state i (ST.rounds x) x wi ri insi))
    let local_protocol'' (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : ST.out_msgs =
                                                                                                                                                                                       (List.foldl (fun (outs : ST.out_msgs) (round : Pervasive.int) -> (ST.prset outs round (local_protocol_round i round x wi ri ins))) (ST.prempty sz (Pervasive.witness)) (AuxList.iseq rounds))
    let local_protocol' (i : ST.party) (x : ST.public_input) (vi : ST.view) : ST.out_msgs =
                                                                                              (local_protocol'' i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi) (ST.rounds x) (ST.rounds x))
    let local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                 (let (outs) = (local_protocol' i x vi) in
                                                                                                                  (let (out) = (local_protocol_end i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi)) in
                                                                                                                   (outs , out)))
    let protocol_round (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.pmsgs) ST.P.arrayN =
                                                                                                                                                                                         (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                                          (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_round i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol_end (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                                                                                           (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                            (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_end i x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (round1 : ST.round) (d : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (List.Iota.iota_ round1 d))
    let protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (rounds : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (AuxList.iseq rounds))
    let protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (ST.in_msgs) ST.pmap =
                                                                                                                                  (protocol'' x ws rs (ST.pprempty (ST.rounds x) (Pervasive.witness)) (ST.rounds x))
    let protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                            (let (ins) = (protocol' x ws rs) in
                                                                                                                                                                                                             (let (outs) = (protocol_end x ws rs ins) in
                                                                                                                                                                                                              (let (tr) = (ST.P.zip3 ws ins rs) in
                                                                                                                                                                                                               (tr , outs))))
    let get_view_in_msgs (j : ST.party) (vi : ST.view) : ST.rmsgs =
                                                                      (ST.P.get (Aux.snd3 vi) j)
    let get_view_out_msgs (i : ST.party) (j : ST.party) (x : ST.public_input) (vi : ST.view) : ST.rmsgs =
                                                                                                            (ST.P.get (local_protocol' i x vi) j)
    let consistent_inputs : (gate -> (NextMsgMaurerAPI.MaurerAPI.pid -> (NextMsgMaurerAPI.MaurerAPI.pid -> ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) -> ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) -> Pervasive.bool))))) =
                                                                                                                                                                                                                                                                                             (gate_consistent_inputs)
    let consistent_rands (x : _Gate) (_ : ST.party) (_ : ST.party) (ri : GT.local_rand) (rj : GT.local_rand) : Pervasive.bool =
                                                                                                                                  (Pervasive._and (gate_valid_rand x ri) (gate_valid_rand x rj))
    let valid_inputs (x : ST.public_input) (ws : (ST.local_input) ST.pmap) : Pervasive.bool =
                                                                                                (Pervasive.witness)
    let valid_rands (x : ST.public_input) (ws : (ST.local_rand) ST.pmap) : Pervasive.bool =
                                                                                              (Pervasive.witness)
    let consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                (Pervasive._and (ST.eq_rmsgs (get_view_in_msgs j vi) (get_view_out_msgs j i x vj)) (Pervasive._and (Pervasive.eq (get_view_in_msgs i vj) (get_view_out_msgs i j x vi)) (Pervasive._and (consistent_inputs x i j (Aux.fst3 vi) (Aux.fst3 vj)) (consistent_rands x i j (Aux.thr3 vi) (Aux.thr3 vj)))))
    let consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                    (Pervasive.witness)
    let pairwise_consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                         (Pervasive._and (ST.valid_view x vi) (Pervasive._and (ST.valid_view x vj) (consistent_views x i j vi vj)))
    let pairwise_consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                             (Pervasive.witness)
    let view_output (i : ST.party) (x : ST.public_input) (v : ST.view) : ST.local_output =
                                                                                             (local_protocol_end i x (Aux.fst3 v) (Aux.thr3 v) (Aux.snd3 v))
    let view_outputs (x : ST.public_input) (vs : (ST.view) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                        (ST.P.imap (fun (i : ST.party) (v : ST.view) -> (view_output i x v)) vs)
    let stateful_consistent_outputs : (ST.public_input -> (ST.party -> (ST.party -> (ST.local_output -> (ST.local_output -> Pervasive.bool))))) = Pervasive.witness
    type local_state2 = (local_state * local_state)
    let stateful_consistent_views_outputs_round (r : ST.round) (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : ((local_state * local_state) * Pervasive.bool) =
                                                                                                                                                                                                                                                                                     (let (outs1) = (from_local_messages (stateful_local_protocol_round i r x (Aux.fst3 sts))) in
                                                                                                                                                                                                                                                                                      (let (outs2) = (from_local_messages (stateful_local_protocol_round j r x (snd sts))) in
                                                                                                                                                                                                                                                                                       (let (in1) = (ST.prget ins1 r) in
                                                                                                                                                                                                                                                                                        (let (in2) = (ST.prget ins2 r) in
                                                                                                                                                                                                                                                                                         (let (sts1') = (update_local_state i r x inp1 (to_local_messages in1) (Aux.fst3 sts)) in
                                                                                                                                                                                                                                                                                          (let (sts2') = (update_local_state j r x inp2 (to_local_messages in2) (snd sts)) in
                                                                                                                                                                                                                                                                                           (let (b) = (Pervasive._and (ST.eq_msg (ST.P.get outs1 j) (ST.P.get in2 i)) (ST.eq_msg (ST.P.get outs2 i) (ST.P.get in1 j))) in
                                                                                                                                                                                                                                                                                            ((sts1' , sts2') , b))))))))
    let stateful_consistent_views_outputs''' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) (rounds : (ST.round) List.list) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                                                    (let (go) = (fun (stb : (local_state2 * Pervasive.bool)) (r : ST.round) -> (let (stb') = (stateful_consistent_views_outputs_round r x i j inp1 inp2 ins1 ins2 (fst stb)) in
                                                                                                                                                                                                                                                                                                                                                                ((fst stb') , (Pervasive._and (snd stb) (snd stb'))))) in
                                                                                                                                                                                                                                                                                     (List.foldl go (sts , (Pervasive._true)) rounds))
    let stateful_consistent_views_outputs'' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                   (stateful_consistent_views_outputs''' x i j inp1 inp2 ins1 ins2 sts (AuxList.iseq (ST.rounds x)))
    let stateful_consistent_views_outputs' (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                   (let (st1) = (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) in
                                                                                                                                                                    (let (st2) = (init_local_state j x (Aux.fst3 vj) (Aux.thr3 vj)) in
                                                                                                                                                                     (let (outsb) = (stateful_consistent_views_outputs'' x i j (Aux.fst3 vi) (Aux.fst3 vj) (Aux.snd3 vi) (Aux.snd3 vj) (st1 , st2)) in
                                                                                                                                                                      outsb)))
    let stateful_consistent_views_outputs (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                                 (let (outsb) = (stateful_consistent_views_outputs' x i j vi vj) in
                                                                                                                                                  (let (outs1) = (Aux.fst3 (fst outsb)) in
                                                                                                                                                   (let (outs2) = (snd (fst outsb)) in
                                                                                                                                                    (let (b) = (snd outsb) in
                                                                                                                                                     (let (out1) = (stateful_local_protocol_end i x outs1) in
                                                                                                                                                      (let (out2) = (stateful_local_protocol_end j x outs2) in
                                                                                                                                                       (Pervasive._and b (stateful_consistent_outputs x i j out1 out2))))))))
    let g_protocol (x : _Gate) (ws : (share) GT.pmap) (cs : (GT.local_rand) GT.pmap) : (((share * (((GT.msg) NextMsgArray.Array.array) GT.P.arrayN * GT.local_rand))) GT.P.arrayN * (share) GT.P.arrayN) =
                                                                                                                                                                                                             (let (outs) = (GT.P.imap (fun (i : GT.party) (wc : (share * GT.local_rand)) -> (local_gate_start i x (fst wc) (snd wc))) (GT.P.zip ws cs)) in
                                                                                                                                                                                                              (let (ins) = (send_messages outs) in
                                                                                                                                                                                                               (let (o) = (GT.P.imap (fun (i : GT.party) (wi : (share * local_in_msgs)) -> (local_gate_end i x (fst wi) (snd wi))) (GT.P.zip ws ins)) in
                                                                                                                                                                                                                (let (rins) = (GT.P.map (fun (bin : local_messages) -> (GT.P.map (fun (msg : GT.msg) -> (NextMsgArray.Array.init (Pervasive.mk_int 1) (fun (j : Pervasive.int) -> if (Pervasive.eq j (Pervasive.mk_int 0)) then msg else (Pervasive.witness)))) (from_local_messages bin))) ins) in
                                                                                                                                                                                                                 (let (tr) = (GT.P.zip3 ws rins cs) in
                                                                                                                                                                                                                  (tr , o))))))
end
module MaurerCircuit = struct
    type circuit = (MaurerGate._Gate) List.list
    let valid_gate' (n : Pervasive.int) (g : MaurerGate._Gate) (pubs : NextMsgISet.ISet.iset) : (NextMsgISet.ISet.iset * Pervasive.bool) =
                                                                                                                                             begin match g with
                                                                                                                                             | (MaurerGate.Add x) -> (pubs , (Pervasive._and (Pervasive.eq (Aux.nth0_3 x) n) (Pervasive._and (Int.le (Pervasive.mk_int 0) (Aux.nth1_3 x)) (Pervasive._and (Int.lt (Aux.nth1_3 x) n) (Pervasive._and (Int.le (Pervasive.mk_int 0) (Aux.nth2_3 x)) (Int.lt (Aux.nth2_3 x) n))))))
                                                                                                                                             | (MaurerGate.SMul x) -> (pubs , (Pervasive._and (Pervasive.eq (Aux.nth0_3 x) n) (Pervasive._and (Int.le (Pervasive.mk_int 0) (Aux.nth1_3 x)) (Pervasive._and (Int.lt (Aux.nth1_3 x) n) (Pervasive._and (Int.le (Pervasive.mk_int 0) (Aux.nth2_3 x)) (Pervasive._and (Int.lt (Aux.nth2_3 x) n) (NextMsgISet.ISet.mem (Aux.nth2_3 x) pubs)))))))
                                                                                                                                             | (MaurerGate.Const x) -> ((NextMsgISet.ISet.add pubs (fst x)) , (Pervasive.eq (fst x) n))
                                                                                                                                             | (MaurerGate.Mul x) -> (pubs , (Pervasive._and (Pervasive.eq (Aux.nth0_3 x) n) (Pervasive._and (Int.le (Pervasive.mk_int 0) (Aux.nth1_3 x)) (Pervasive._and (Int.lt (Aux.nth1_3 x) n) (Pervasive._and (Int.le (Pervasive.mk_int 0) (Aux.nth2_3 x)) (Int.lt (Aux.nth2_3 x) n))))))
                                                                                                                                             end
    let rec valid_circuit' (n : Pervasive.int) (c : (MaurerGate._Gate) List.list) (pubs : NextMsgISet.ISet.iset) : Pervasive.bool =
                                                                                                                                      begin match c with
                                                                                                                                      | (List.Nil) -> (Pervasive._true)
                                                                                                                                      | (List.Cons (g , c')) -> (let (r) = (valid_gate' n g pubs) in
                                                                                                                                                                 (Pervasive._and (snd r) (valid_circuit' (Int.plus n (Pervasive.mk_int 1)) c' (fst r))))
                                                                                                                                      end
    let valid_circuit (x : circuit) (n : Pervasive.int) (ps : NextMsgISet.ISet.iset) : Pervasive.bool =
                                                                                                          (Pervasive._and (Int.le (Pervasive.mk_int 0) n) (Pervasive._and (Int.lt (Pervasive.mk_int 0) (Int.plus n (List.size x))) (Pervasive._and (NextMsgISet.ISet.subset ps (NextMsgISet.ISet.iset n)) (valid_circuit' n x ps))))
    let g_pubs (g : MaurerGate._Gate) (pubs : NextMsgISet.ISet.iset) : NextMsgISet.ISet.iset =
                                                                                                 begin match g with
                                                                                                 | (MaurerGate.Add x) -> pubs
                                                                                                 | (MaurerGate.SMul x) -> pubs
                                                                                                 | (MaurerGate.Const x) -> (NextMsgISet.ISet.add pubs (fst x))
                                                                                                 | (MaurerGate.Mul x) -> pubs
                                                                                                 end
    let g_wire (g : MaurerGate._Gate) : Pervasive.int =
                                                          begin match g with
                                                          | (MaurerGate.Add x) -> (Aux.nth0_3 x)
                                                          | (MaurerGate.SMul x) -> (Aux.nth0_3 x)
                                                          | (MaurerGate.Const x) -> (fst x)
                                                          | (MaurerGate.Mul x) -> (Aux.nth0_3 x)
                                                          end
    let rec check_c_wire (c : (MaurerGate._Gate) List.list) (i : Pervasive.int) : Pervasive.bool =
                                                                                                     begin match c with
                                                                                                     | (List.Nil) -> (Pervasive._true)
                                                                                                     | (List.Cons (g , c')) -> (Pervasive._and (Pervasive.eq (g_wire g) i) (check_c_wire c' (Int.plus i (Pervasive.mk_int 1))))
                                                                                                     end
    let c_pubs (c : (MaurerGate._Gate) List.list) (pubs : NextMsgISet.ISet.iset) : NextMsgISet.ISet.iset =
                                                                                                             (List.foldl (fun (y : NextMsgISet.ISet.iset) (x : MaurerGate._Gate) -> (g_pubs x y)) pubs c)
    module G = struct
        type _Gate = MaurerGate._Gate
        type share = MaurerGate.share
        type local_msgs = MaurerGate.local_msgs
        type local_in_msgs = MaurerGate.local_in_msgs
        type local_out_msgs = MaurerGate.local_out_msgs
        module GT = struct
            type public_input = MaurerGate.GT.public_input
            module P = struct
                let rec size : Pervasive.int =
                                                 (MaurerGate.GT.P.size)
                type ('a) arrayN = ('a) MaurerGate.GT.P.arrayN
                let rec get : (('a) Aux.array5 -> (Pervasive.int -> 'a)) =
                                                                             (MaurerGate.GT.P.get)
                let rec set : (('a) Aux.array5 -> (Pervasive.int -> ('a -> ('a * ('a * ('a * ('a) Aux.array2)))))) =
                                                                                                                       (MaurerGate.GT.P.set)
                let rec init : ((Pervasive.int -> 'a) -> ('a * ('a * ('a * ('a * 'a))))) =
                                                                                             (MaurerGate.GT.P.init)
                let rec of_list : (('a) List.list -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                             (MaurerGate.GT.P.of_list)
                let rec to_list : (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) List.list) =
                                                                                             (MaurerGate.GT.P.to_list)
                let rec to_assoc : (('a) NextMsgMaurerP.MaurerP.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                                                (MaurerGate.GT.P.to_assoc)
                let rec create : ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                (MaurerGate.GT.P.create)
                let rec singl : (Pervasive.int -> ('a -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                  (MaurerGate.GT.P.singl)
                let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('b) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                                 (MaurerGate.GT.P.imap)
                let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                              (imap (fun (_ : Pervasive.int) -> f) xs)
                let rec merge : (('a -> ('b -> 'c)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> (('b) NextMsgMaurerP.MaurerP.arrayN -> ('c) NextMsgMaurerP.MaurerP.arrayN))) =
                                                                                                                                                                               (MaurerGate.GT.P.merge)
                let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                       (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
                let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> ('a) NextMsgMaurerP.MaurerP.arrayN)) =
                                                                                                                                                               (MaurerGate.GT.P.filter)
                let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool)) =
                                                                                                                                        (MaurerGate.GT.P.all)
                let rec allsame : (('a) NextMsgMaurerP.MaurerP.arrayN -> Pervasive.bool) =
                                                                                             (MaurerGate.GT.P.allsame)
                let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                                  (zip xs (zip ys zs))
                let rec concat : ((('b) NextMsgMaurerP.MaurerP.arrayN) List.list -> (('b) List.list) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                                                                        (MaurerGate.GT.P.concat)
            end
            let rec parties : Pervasive.int =
                                                (MaurerGate.GT.parties)
            type party = MaurerGate.GT.party
            let rec partyset : NextMsgISet.ISet.iset =
                                                         (MaurerGate.GT.partyset)
            type round = MaurerGate.GT.round
            let rec rounds : (MaurerGate.GT.public_input -> Pervasive.int) =
                                                                               (MaurerGate.GT.rounds)
            let rec roundset : (MaurerGate.GT.public_input -> NextMsgISet.ISet.iset) =
                                                                                         (MaurerGate.GT.roundset)
            type ('a) pmap = ('a) MaurerGate.GT.pmap
            type ('a) rmap = ('a) MaurerGate.GT.rmap
            type ('a) prmap = ('a) MaurerGate.GT.prmap
            type ('a) ppmap = ('a) MaurerGate.GT.ppmap
            type ('a) pprmap = ('a) MaurerGate.GT.pprmap
            type local_input = MaurerGate.GT.local_input
            type local_output = MaurerGate.GT.local_output
            type local_rand = MaurerGate.GT.local_rand
            type msg = MaurerGate.GT.msg
            type pmsgs = MaurerGate.GT.pmsgs
            type rmsgs = MaurerGate.GT.rmsgs
            type prmsgs = MaurerGate.GT.prmsgs
            type ppmsgs = MaurerGate.GT.ppmsgs
            type pprmsgs = MaurerGate.GT.pprmsgs
            type in_msgs = MaurerGate.GT.in_msgs
            type out_msgs = MaurerGate.GT.out_msgs
            type view = MaurerGate.GT.view
            type trace = MaurerGate.GT.trace
            let rec eq_msg : ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either -> ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either -> Pervasive.bool)) =
                                                                                                                                                                                  (MaurerGate.GT.eq_msg)
            let rec eq_pmsgs : (MaurerGate.GT.pmsgs -> (MaurerGate.GT.pmsgs -> Pervasive.bool)) =
                                                                                                    (MaurerGate.GT.eq_pmsgs)
            let rec eq_rmsgs : (MaurerGate.GT.rmsgs -> (MaurerGate.GT.rmsgs -> Pervasive.bool)) =
                                                                                                    (MaurerGate.GT.eq_rmsgs)
            let rec pinit : ((MaurerGate.GT.party -> 'a) -> ('a) MaurerGate.GT.P.arrayN) =
                                                                                             (MaurerGate.GT.pinit)
            let rec ppinit : ((MaurerGate.GT.party -> (MaurerGate.GT.party -> 'a)) -> (('a) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN) =
                                                                                                                                                (MaurerGate.GT.ppinit)
            let rec prempty : (Pervasive.int -> ('a -> (('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN)) =
                                                                                                                    (MaurerGate.GT.prempty)
            let rec pprempty : (Pervasive.int -> ('a -> ((('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                              (MaurerGate.GT.pprempty)
            let rec ppswap : (('a) MaurerGate.GT.ppmap -> (('a) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN) =
                                                                                                                    (MaurerGate.GT.ppswap)
            let rec prget : (('a) MaurerGate.GT.prmap -> (MaurerGate.GT.round -> ('a) MaurerGate.GT.P.arrayN)) =
                                                                                                                   (MaurerGate.GT.prget)
            let rec pprget : (('a) MaurerGate.GT.pprmap -> (MaurerGate.GT.round -> (('a) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                              (MaurerGate.GT.pprget)
            let rec prset : (('a) MaurerGate.GT.prmap -> (Pervasive.int -> (('a) MaurerGate.GT.pmap -> (('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN))) =
                                                                                                                                                                     (MaurerGate.GT.prset)
            let rec prext : (Pervasive.int -> (('a) MaurerGate.GT.prmap -> (('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN)) =
                                                                                                                                        (MaurerGate.GT.prext)
            let rec prextset : (('a) MaurerGate.GT.prmap -> (Pervasive.int -> (('a) MaurerGate.GT.pmap -> (('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN))) =
                                                                                                                                                                        (MaurerGate.GT.prextset)
            let rec pprset : (('a) MaurerGate.GT.pprmap -> (MaurerGate.GT.round -> (('a) MaurerGate.GT.ppmap -> ((('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN))) =
                                                                                                                                                                                                       (MaurerGate.GT.pprset)
            let rec prfilter : ((MaurerGate.GT.round -> Pervasive.bool) -> (('a) MaurerGate.GT.prmap -> (('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                     (MaurerGate.GT.prfilter)
            let rec pprfilter : ((MaurerGate.GT.round -> Pervasive.bool) -> (('a) MaurerGate.GT.pprmap -> ((('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                                                (MaurerGate.GT.pprfilter)
            let rec rdom : (Pervasive.int -> (MaurerGate.GT.round -> (('a) MaurerGate.GT.rmap -> Pervasive.bool))) =
                                                                                                                       (MaurerGate.GT.rdom)
            let rec prdom : (Pervasive.int -> (MaurerGate.GT.round -> (('a) MaurerGate.GT.prmap -> Pervasive.bool))) =
                                                                                                                         (MaurerGate.GT.prdom)
            let rec pprdom : (Pervasive.int -> (MaurerGate.GT.round -> (('a) MaurerGate.GT.pprmap -> Pervasive.bool))) =
                                                                                                                           (MaurerGate.GT.pprdom)
            let rec rlist : (Pervasive.int -> (('a) List.list -> ('a) NextMsgArray.Array.array)) =
                                                                                                     (MaurerGate.GT.rlist)
            let rec prlist : (Pervasive.int -> ((MaurerGate.GT.pmsgs) List.list -> (MaurerGate.GT.msg) MaurerGate.GT.prmap)) =
                                                                                                                                 (MaurerGate.GT.prlist)
            let rec pcons : (('a) MaurerGate.GT.pmap -> ((('a) List.list) MaurerGate.GT.pmap -> (('a) List.list) MaurerGate.GT.P.arrayN)) =
                                                                                                                                              (MaurerGate.GT.pcons)
            let rec phead : ((('a) List.list) MaurerGate.GT.pmap -> ('a) MaurerGate.GT.P.arrayN) =
                                                                                                     (MaurerGate.GT.phead)
            let rec pbehead : ((('a) List.list) MaurerGate.GT.pmap -> (('a) List.list) MaurerGate.GT.P.arrayN) =
                                                                                                                   (MaurerGate.GT.pbehead)
            let rec prcons : ((('a) List.list) MaurerGate.GT.pmap -> (('a) MaurerGate.GT.pmap -> (('a) List.list) MaurerGate.GT.P.arrayN)) =
                                                                                                                                               (MaurerGate.GT.prcons)
            let rec pcat : ((('a) List.list) MaurerGate.GT.pmap -> ((('a) List.list) MaurerGate.GT.pmap -> (('a) List.list) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                         (MaurerGate.GT.pcat)
            let rec ppcons : (('a) MaurerGate.GT.ppmap -> ((('a) List.list) MaurerGate.GT.ppmap -> ((('a) List.list) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                          (MaurerGate.GT.ppcons)
            let rec pprcons : ((('a) List.list) MaurerGate.GT.ppmap -> (('a) MaurerGate.GT.ppmap -> ((('a) List.list) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                           (MaurerGate.GT.pprcons)
            let rec ppcat : ((('a) List.list) MaurerGate.GT.ppmap -> ((('a) List.list) MaurerGate.GT.ppmap -> ((('a) List.list) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                                     (MaurerGate.GT.ppcat)
            let rec prmsgs_up_to : (MaurerGate.GT.round -> (MaurerGate.GT.prmsgs -> ((MaurerGate.GT.msg) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                (MaurerGate.GT.prmsgs_up_to)
            let rec pprmsgs_up_to : (MaurerGate.GT.round -> (MaurerGate.GT.pprmsgs -> (((MaurerGate.GT.msg) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                                           (MaurerGate.GT.pprmsgs_up_to)
            let rec get_trace_inputs : (MaurerGate.GT.trace -> (MaurerGate.GT.local_input) MaurerGate.GT.P.arrayN) =
                                                                                                                       (MaurerGate.GT.get_trace_inputs)
            let rec get_trace_in_msgs : (MaurerGate.GT.trace -> (MaurerGate.GT.in_msgs) MaurerGate.GT.P.arrayN) =
                                                                                                                    (MaurerGate.GT.get_trace_in_msgs)
            let rec get_trace_rands : (MaurerGate.GT.trace -> (MaurerGate.GT.local_rand) MaurerGate.GT.P.arrayN) =
                                                                                                                     (MaurerGate.GT.get_trace_rands)
            let rec get_view : (MaurerGate.GT.party -> (MaurerGate.GT.trace -> MaurerGate.GT.view)) =
                                                                                                        (MaurerGate.GT.get_view)
            let rec get_trace_in_msgs_round : (MaurerGate.GT.round -> (MaurerGate.GT.trace -> ((MaurerGate.GT.msg) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                        (MaurerGate.GT.get_trace_in_msgs_round)
            let rec get_view_in_msgs_round : (MaurerGate.GT.round -> (MaurerGate.GT.view -> (MaurerGate.GT.msg) MaurerGate.GT.P.arrayN)) =
                                                                                                                                             (MaurerGate.GT.get_view_in_msgs_round)
            let rec add_view_in_msgs : (MaurerGate.GT.round -> (MaurerGate.GT.pmsgs -> (MaurerGate.GT.view -> (MaurerGate.GT.local_input * (((MaurerGate.GT.msg) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN * MaurerGate.GT.local_rand))))) =
                                                                                                                                                                                                                                                      (MaurerGate.GT.add_view_in_msgs)
            let rec get_trace_in_msgs_up_to : (MaurerGate.GT.round -> (MaurerGate.GT.trace -> (((MaurerGate.GT.msg) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                                                   (MaurerGate.GT.get_trace_in_msgs_up_to)
            let rec add_trace_in_msgs : (MaurerGate.GT.round -> (MaurerGate.GT.ppmsgs -> (MaurerGate.GT.trace -> ((MaurerGate.GT.local_input * (((MaurerGate.GT.msg) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN * MaurerGate.GT.local_rand))) MaurerGate.GT.P.arrayN))) =
                                                                                                                                                                                                                                                                                  (MaurerGate.GT.add_trace_in_msgs)
            let rec valid_trace : (MaurerGate.GT.public_input -> (MaurerGate.GT.trace -> Pervasive.bool)) =
                                                                                                              (MaurerGate.GT.valid_trace)
            let rec valid_view : (MaurerGate.GT.public_input -> (MaurerGate.GT.view -> Pervasive.bool)) =
                                                                                                            (MaurerGate.GT.valid_view)
        end
        let rec local_gate_start : (MaurerMul.GT.party -> (MaurerGate.gate -> (MaurerMul.share -> ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.rand) Aux.either -> (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either)))) =
                                                                                                                                                                                                                                        (MaurerGate.local_gate_start)
        let rec local_gate_end : (MaurerAdd.GT.party -> (MaurerGate.gate -> (MaurerAdd.share -> ((MaurerAdd.local_in_msgs, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either -> (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st))))) =
                                                                                                                                                                                                                                                           (MaurerGate.local_gate_end)
        let rec gate_valid_rand : (MaurerGate.gate -> ((MaurerAdd.GT.local_rand, MaurerMul.GT.local_rand) Aux.either -> Pervasive.bool)) =
                                                                                                                                             (MaurerGate.gate_valid_rand)
        let rec gate_valid_rands : (MaurerGate._Gate -> ((MaurerGate.GT.local_rand) MaurerGate.GT.P.arrayN -> Pervasive.bool)) =
                                                                                                                                   (MaurerGate.gate_valid_rands)
        module ST = struct
            type public_input = MaurerGate.ST.public_input
            module P = struct
                let rec size : Pervasive.int =
                                                 (MaurerGate.ST.P.size)
                type ('a) arrayN = ('a) MaurerGate.ST.P.arrayN
                let rec get : (('a) MaurerGate.GT.P.arrayN -> (Pervasive.int -> 'a)) =
                                                                                         (MaurerGate.ST.P.get)
                let rec set : (('a) MaurerGate.GT.P.arrayN -> (Pervasive.int -> ('a -> ('a) MaurerGate.GT.P.arrayN))) =
                                                                                                                          (MaurerGate.ST.P.set)
                let rec init : ((Pervasive.int -> 'a) -> ('a) MaurerGate.GT.P.arrayN) =
                                                                                          (MaurerGate.ST.P.init)
                let rec of_list : (('a) List.list -> ('a) MaurerGate.GT.P.arrayN) =
                                                                                      (MaurerGate.ST.P.of_list)
                let rec to_list : (('a) MaurerGate.GT.P.arrayN -> ('a) List.list) =
                                                                                      (MaurerGate.ST.P.to_list)
                let rec to_assoc : (('a) MaurerGate.GT.P.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                                         (MaurerGate.ST.P.to_assoc)
                let rec create : ('a -> ('a) MaurerGate.GT.P.arrayN) =
                                                                         (MaurerGate.ST.P.create)
                let rec singl : (Pervasive.int -> ('a -> ('a) MaurerGate.GT.P.arrayN)) =
                                                                                           (MaurerGate.ST.P.singl)
                let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) MaurerGate.GT.P.arrayN -> ('b) MaurerGate.GT.P.arrayN)) =
                                                                                                                                   (MaurerGate.ST.P.imap)
                let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                              (imap (fun (_ : Pervasive.int) -> f) xs)
                let rec merge : (('a -> ('b -> 'c)) -> (('a) MaurerGate.GT.P.arrayN -> (('b) MaurerGate.GT.P.arrayN -> ('c) MaurerGate.GT.P.arrayN))) =
                                                                                                                                                          (MaurerGate.ST.P.merge)
                let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                       (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
                let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) MaurerGate.GT.P.arrayN -> ('a) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                 (MaurerGate.ST.P.filter)
                let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) MaurerGate.GT.P.arrayN -> Pervasive.bool)) =
                                                                                                                                 (MaurerGate.ST.P.all)
                let rec allsame : (('a) MaurerGate.GT.P.arrayN -> Pervasive.bool) =
                                                                                      (MaurerGate.ST.P.allsame)
                let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                                  (zip xs (zip ys zs))
                let rec concat : ((('b) MaurerGate.GT.P.arrayN) List.list -> (('b) List.list) MaurerGate.GT.P.arrayN) =
                                                                                                                          (MaurerGate.ST.P.concat)
            end
            let rec parties : Pervasive.int =
                                                (MaurerGate.ST.parties)
            type party = MaurerGate.ST.party
            let rec partyset : NextMsgISet.ISet.iset =
                                                         (MaurerGate.ST.partyset)
            type round = MaurerGate.ST.round
            let rec rounds : (MaurerGate.GT.public_input -> Pervasive.int) =
                                                                               (MaurerGate.ST.rounds)
            let rec roundset : (MaurerGate.GT.public_input -> NextMsgISet.ISet.iset) =
                                                                                         (MaurerGate.ST.roundset)
            type ('a) pmap = ('a) MaurerGate.ST.pmap
            type ('a) rmap = ('a) MaurerGate.ST.rmap
            type ('a) prmap = ('a) MaurerGate.ST.prmap
            type ('a) ppmap = ('a) MaurerGate.ST.ppmap
            type ('a) pprmap = ('a) MaurerGate.ST.pprmap
            type local_input = MaurerGate.ST.local_input
            type local_output = MaurerGate.ST.local_output
            type local_rand = MaurerGate.ST.local_rand
            type msg = MaurerGate.ST.msg
            type pmsgs = MaurerGate.ST.pmsgs
            type rmsgs = MaurerGate.ST.rmsgs
            type prmsgs = MaurerGate.ST.prmsgs
            type ppmsgs = MaurerGate.ST.ppmsgs
            type pprmsgs = MaurerGate.ST.pprmsgs
            type in_msgs = MaurerGate.ST.in_msgs
            type out_msgs = MaurerGate.ST.out_msgs
            type view = MaurerGate.ST.view
            type trace = MaurerGate.ST.trace
            let rec eq_msg : (MaurerGate.GT.msg -> (MaurerGate.GT.msg -> Pervasive.bool)) =
                                                                                              (MaurerGate.ST.eq_msg)
            let rec eq_pmsgs : (MaurerGate.GT.pmsgs -> (MaurerGate.GT.pmsgs -> Pervasive.bool)) =
                                                                                                    (MaurerGate.ST.eq_pmsgs)
            let rec eq_rmsgs : (MaurerGate.GT.rmsgs -> (MaurerGate.GT.rmsgs -> Pervasive.bool)) =
                                                                                                    (MaurerGate.ST.eq_rmsgs)
            let rec pinit : ((MaurerGate.GT.party -> 'a) -> ('a) MaurerGate.GT.P.arrayN) =
                                                                                             (MaurerGate.ST.pinit)
            let rec ppinit : ((MaurerGate.GT.party -> (MaurerGate.GT.party -> 'a)) -> (('a) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN) =
                                                                                                                                                (MaurerGate.ST.ppinit)
            let rec prempty : (Pervasive.int -> ('a -> (('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN)) =
                                                                                                                    (MaurerGate.ST.prempty)
            let rec pprempty : (Pervasive.int -> ('a -> ((('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                              (MaurerGate.ST.pprempty)
            let rec ppswap : (('a) MaurerGate.GT.ppmap -> (('a) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN) =
                                                                                                                    (MaurerGate.ST.ppswap)
            let rec prget : (('a) MaurerGate.GT.prmap -> (MaurerGate.GT.round -> ('a) MaurerGate.GT.P.arrayN)) =
                                                                                                                   (MaurerGate.ST.prget)
            let rec pprget : (('a) MaurerGate.GT.pprmap -> (MaurerGate.GT.round -> (('a) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                              (MaurerGate.ST.pprget)
            let rec prset : (('a) MaurerGate.GT.prmap -> (Pervasive.int -> (('a) MaurerGate.GT.pmap -> (('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN))) =
                                                                                                                                                                     (MaurerGate.ST.prset)
            let rec prext : (Pervasive.int -> (('a) MaurerGate.GT.prmap -> (('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN)) =
                                                                                                                                        (MaurerGate.ST.prext)
            let rec prextset : (('a) MaurerGate.GT.prmap -> (Pervasive.int -> (('a) MaurerGate.GT.pmap -> (('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN))) =
                                                                                                                                                                        (MaurerGate.ST.prextset)
            let rec pprset : (('a) MaurerGate.GT.pprmap -> (MaurerGate.GT.round -> (('a) MaurerGate.GT.ppmap -> ((('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN))) =
                                                                                                                                                                                                       (MaurerGate.ST.pprset)
            let rec prfilter : ((MaurerGate.GT.round -> Pervasive.bool) -> (('a) MaurerGate.GT.prmap -> (('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                     (MaurerGate.ST.prfilter)
            let rec pprfilter : ((MaurerGate.GT.round -> Pervasive.bool) -> (('a) MaurerGate.GT.pprmap -> ((('a) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                                                (MaurerGate.ST.pprfilter)
            let rec rdom : (Pervasive.int -> (MaurerGate.GT.round -> (('a) MaurerGate.GT.rmap -> Pervasive.bool))) =
                                                                                                                       (MaurerGate.ST.rdom)
            let rec prdom : (Pervasive.int -> (MaurerGate.GT.round -> (('a) MaurerGate.GT.prmap -> Pervasive.bool))) =
                                                                                                                         (MaurerGate.ST.prdom)
            let rec pprdom : (Pervasive.int -> (MaurerGate.GT.round -> (('a) MaurerGate.GT.pprmap -> Pervasive.bool))) =
                                                                                                                           (MaurerGate.ST.pprdom)
            let rec rlist : (Pervasive.int -> (('a) List.list -> ('a) NextMsgArray.Array.array)) =
                                                                                                     (MaurerGate.ST.rlist)
            let rec prlist : (Pervasive.int -> ((MaurerGate.GT.pmsgs) List.list -> (MaurerGate.GT.msg) MaurerGate.GT.prmap)) =
                                                                                                                                 (MaurerGate.ST.prlist)
            let rec pcons : (('a) MaurerGate.GT.pmap -> ((('a) List.list) MaurerGate.GT.pmap -> (('a) List.list) MaurerGate.GT.P.arrayN)) =
                                                                                                                                              (MaurerGate.ST.pcons)
            let rec phead : ((('a) List.list) MaurerGate.GT.pmap -> ('a) MaurerGate.GT.P.arrayN) =
                                                                                                     (MaurerGate.ST.phead)
            let rec pbehead : ((('a) List.list) MaurerGate.GT.pmap -> (('a) List.list) MaurerGate.GT.P.arrayN) =
                                                                                                                   (MaurerGate.ST.pbehead)
            let rec prcons : ((('a) List.list) MaurerGate.GT.pmap -> (('a) MaurerGate.GT.pmap -> (('a) List.list) MaurerGate.GT.P.arrayN)) =
                                                                                                                                               (MaurerGate.ST.prcons)
            let rec pcat : ((('a) List.list) MaurerGate.GT.pmap -> ((('a) List.list) MaurerGate.GT.pmap -> (('a) List.list) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                         (MaurerGate.ST.pcat)
            let rec ppcons : (('a) MaurerGate.GT.ppmap -> ((('a) List.list) MaurerGate.GT.ppmap -> ((('a) List.list) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                          (MaurerGate.ST.ppcons)
            let rec pprcons : ((('a) List.list) MaurerGate.GT.ppmap -> (('a) MaurerGate.GT.ppmap -> ((('a) List.list) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                           (MaurerGate.ST.pprcons)
            let rec ppcat : ((('a) List.list) MaurerGate.GT.ppmap -> ((('a) List.list) MaurerGate.GT.ppmap -> ((('a) List.list) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                                     (MaurerGate.ST.ppcat)
            let rec prmsgs_up_to : (MaurerGate.GT.round -> (MaurerGate.GT.prmsgs -> ((MaurerGate.GT.msg) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                (MaurerGate.ST.prmsgs_up_to)
            let rec pprmsgs_up_to : (MaurerGate.GT.round -> (MaurerGate.GT.pprmsgs -> (((MaurerGate.GT.msg) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                                           (MaurerGate.ST.pprmsgs_up_to)
            let rec get_trace_inputs : (MaurerGate.GT.trace -> (MaurerGate.GT.local_input) MaurerGate.GT.P.arrayN) =
                                                                                                                       (MaurerGate.ST.get_trace_inputs)
            let rec get_trace_in_msgs : (MaurerGate.GT.trace -> (MaurerGate.GT.in_msgs) MaurerGate.GT.P.arrayN) =
                                                                                                                    (MaurerGate.ST.get_trace_in_msgs)
            let rec get_trace_rands : (MaurerGate.GT.trace -> (MaurerGate.GT.local_rand) MaurerGate.GT.P.arrayN) =
                                                                                                                     (MaurerGate.ST.get_trace_rands)
            let rec get_view : (MaurerGate.GT.party -> (MaurerGate.GT.trace -> MaurerGate.GT.view)) =
                                                                                                        (MaurerGate.ST.get_view)
            let rec get_trace_in_msgs_round : (MaurerGate.GT.round -> (MaurerGate.GT.trace -> ((MaurerGate.GT.msg) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                        (MaurerGate.ST.get_trace_in_msgs_round)
            let rec get_view_in_msgs_round : (MaurerGate.GT.round -> (MaurerGate.GT.view -> (MaurerGate.GT.msg) MaurerGate.GT.P.arrayN)) =
                                                                                                                                             (MaurerGate.ST.get_view_in_msgs_round)
            let rec add_view_in_msgs : (MaurerGate.GT.round -> (MaurerGate.GT.pmsgs -> (MaurerGate.GT.view -> (MaurerGate.GT.local_input * (((MaurerGate.GT.msg) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN * MaurerGate.GT.local_rand))))) =
                                                                                                                                                                                                                                                      (MaurerGate.ST.add_view_in_msgs)
            let rec get_trace_in_msgs_up_to : (MaurerGate.GT.round -> (MaurerGate.GT.trace -> (((MaurerGate.GT.msg) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN) MaurerGate.GT.P.arrayN)) =
                                                                                                                                                                                                   (MaurerGate.ST.get_trace_in_msgs_up_to)
            let rec add_trace_in_msgs : (MaurerGate.GT.round -> (MaurerGate.GT.ppmsgs -> (MaurerGate.GT.trace -> ((MaurerGate.GT.local_input * (((MaurerGate.GT.msg) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN * MaurerGate.GT.local_rand))) MaurerGate.GT.P.arrayN))) =
                                                                                                                                                                                                                                                                                  (MaurerGate.ST.add_trace_in_msgs)
            let rec valid_trace : (MaurerGate.GT.public_input -> (MaurerGate.GT.trace -> Pervasive.bool)) =
                                                                                                              (MaurerGate.ST.valid_trace)
            let rec valid_view : (MaurerGate.GT.public_input -> (MaurerGate.GT.view -> Pervasive.bool)) =
                                                                                                            (MaurerGate.ST.valid_view)
        end
        type local_messages = MaurerGate.local_messages
        type messages = MaurerGate.messages
        type local_out_messages = MaurerGate.local_out_messages
        type local_in_messages = MaurerGate.local_in_messages
        type out_messages = MaurerGate.out_messages
        type in_messages = MaurerGate.in_messages
        let rec from_local_messages : ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either -> ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either * (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either))))) =
                                                                                                                                                                                                                                                                                                                                                                                                                                        (MaurerGate.from_local_messages)
        let rec to_local_messages : (((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either) NextMsgMaurerP.MaurerP.arrayN -> (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either) =
                                                                                                                                                                                                      (MaurerGate.to_local_messages)
        let rec send_messages : (((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either) NextMsgMaurerP.MaurerP.arrayN -> ((Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either) NextMsgMaurerP.MaurerP.arrayN) =
                                                                                                                                                                                                                                   (MaurerGate.send_messages)
        let rec from_messages : ((MaurerGate.local_messages) MaurerGate.ST.P.arrayN -> (MaurerGate.ST.pmsgs) MaurerGate.ST.P.arrayN) =
                                                                                                                                         (MaurerGate.from_messages)
        let rec to_messages : ((MaurerGate.ST.pmsgs) MaurerGate.ST.P.arrayN -> (MaurerGate.local_messages) MaurerGate.ST.P.arrayN) =
                                                                                                                                       (MaurerGate.to_messages)
        let rec valid_local_messages : (MaurerGate.gate -> (MaurerAdd.ST.round -> ((MaurerAdd.local_messages, MaurerMul.local_messages) Aux.either -> Pervasive.bool))) =
                                                                                                                                                                            (MaurerGate.valid_local_messages)
        let rec valid_messages : (MaurerGate.ST.public_input -> (MaurerGate.ST.round -> (MaurerGate.messages -> Pervasive.bool))) =
                                                                                                                                      (MaurerGate.valid_messages)
        let rec valid_msg : (MaurerGate.gate -> (MaurerAdd.ST.round -> ((MaurerAdd.ST.msg, MaurerMul.ST.msg) Aux.either -> Pervasive.bool))) =
                                                                                                                                                 (MaurerGate.valid_msg)
        let rec valid_pmsgs : (MaurerGate.ST.public_input -> (MaurerGate.ST.round -> (MaurerGate.ST.pmsgs -> Pervasive.bool))) =
                                                                                                                                   (MaurerGate.valid_pmsgs)
        let rec valid_ppmsgs : (MaurerGate.ST.public_input -> (MaurerGate.ST.round -> (MaurerGate.ST.ppmsgs -> Pervasive.bool))) =
                                                                                                                                     (MaurerGate.valid_ppmsgs)
        type local_state = MaurerGate.local_state
        let rec init_local_state : (MaurerGate.ST.party -> (MaurerGate.ST.public_input -> (MaurerGate.share -> (MaurerGate.ST.local_rand -> (MaurerGate.share * (MaurerGate.ST.local_rand, MaurerGate.local_in_msgs) Aux.either))))) =
                                                                                                                                                                                                                                         (MaurerGate.init_local_state)
        let rec update_local_state : (MaurerGate.ST.party -> (MaurerGate.ST.round -> (MaurerGate.ST.public_input -> (MaurerGate.ST.local_input -> (MaurerGate.local_in_messages -> ((MaurerGate.share * (MaurerGate.GT.local_rand, MaurerGate.local_in_msgs) Aux.either) -> (MaurerGate.share * (MaurerGate.GT.local_rand, MaurerGate.local_in_messages) Aux.either))))))) =
                                                                                                                                                                                                                                                                                                                                                                               (MaurerGate.update_local_state)
        let rec get_local_state : (MaurerGate.ST.party -> (MaurerGate.ST.round -> (MaurerGate.ST.public_input -> (MaurerGate.ST.local_input -> (MaurerGate.ST.local_rand -> (MaurerGate.ST.in_msgs -> MaurerGate.local_state)))))) =
                                                                                                                                                                                                                                       (MaurerGate.get_local_state)
        type state = MaurerGate.state
        let rec init_state : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> (MaurerGate.local_state) MaurerGate.ST.P.arrayN))) =
                                                                                                                                                                                                                        (MaurerGate.init_state)
        let rec update_state : (MaurerGate.ST.round -> (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.local_in_messages) MaurerGate.ST.pmap -> (MaurerGate.state -> (MaurerGate.local_state) MaurerGate.ST.P.arrayN))))) =
                                                                                                                                                                                                                                                                             (MaurerGate.update_state)
        let rec get_state : (MaurerGate.ST.round -> (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> ((MaurerGate.ST.in_msgs) MaurerGate.ST.pmap -> (MaurerGate.local_state) MaurerGate.ST.P.arrayN))))) =
                                                                                                                                                                                                                                                                                                (MaurerGate.get_state)
        let rec stateful_local_protocol_round : (MaurerGate.GT.party -> (MaurerGate.ST.round -> (MaurerGate._Gate -> ((MaurerGate.share * (MaurerGate.GT.local_rand, MaurerGate.local_in_msgs) Aux.either) -> MaurerGate.local_out_msgs)))) =
                                                                                                                                                                                                                                                (MaurerGate.stateful_local_protocol_round)
        let rec stateful_local_protocol_end : (MaurerGate.GT.party -> (MaurerGate._Gate -> ((MaurerGate.share * (MaurerGate.GT.local_rand, MaurerGate.local_in_msgs) Aux.either) -> MaurerGate.share))) =
                                                                                                                                                                                                            (MaurerGate.stateful_local_protocol_end)
        let rec stateful_local_protocol''' : (MaurerGate.ST.party -> (MaurerGate.ST.public_input -> (MaurerGate.ST.local_input -> (MaurerGate.local_state -> (MaurerGate.ST.in_msgs -> (Pervasive.int -> ((MaurerGate.ST.round) List.list -> (MaurerGate.local_state * MaurerGate.ST.out_msgs)))))))) =
                                                                                                                                                                                                                                                                                                          (MaurerGate.stateful_local_protocol''')
        let rec stateful_local_protocol'' : (MaurerGate.ST.party -> (MaurerGate.ST.public_input -> (MaurerGate.ST.local_input -> (MaurerGate.local_state -> (MaurerGate.ST.in_msgs -> (Pervasive.int -> (MaurerGate.ST.round -> (MaurerGate.local_state * MaurerGate.ST.out_msgs)))))))) =
                                                                                                                                                                                                                                                                                             (MaurerGate.stateful_local_protocol'')
        let rec stateful_local_protocol' : (MaurerGate.ST.party -> (MaurerGate.ST.public_input -> (MaurerGate.ST.local_input -> (MaurerGate.local_state -> (MaurerGate.ST.in_msgs -> (MaurerGate.local_state * MaurerGate.ST.out_msgs)))))) =
                                                                                                                                                                                                                                                (MaurerGate.stateful_local_protocol')
        let rec stateful_local_protocol : (MaurerGate.ST.party -> (MaurerGate.ST.public_input -> (MaurerGate.ST.view -> (MaurerGate.ST.out_msgs * MaurerGate.ST.local_output)))) =
                                                                                                                                                                                     (MaurerGate.stateful_local_protocol)
        let rec stateful_protocol_round : (MaurerGate.ST.round -> (MaurerGate.ST.public_input -> (MaurerGate.state -> (MaurerGate.local_out_messages) MaurerGate.ST.P.arrayN))) =
                                                                                                                                                                                    (MaurerGate.stateful_protocol_round)
        let rec stateful_protocol_end : (MaurerGate.ST.public_input -> (MaurerGate.state -> (MaurerGate.ST.local_output) MaurerGate.ST.P.arrayN)) =
                                                                                                                                                      (MaurerGate.stateful_protocol_end)
        let rec stateful_protocol''' : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.in_msgs) MaurerGate.ST.pmap -> (MaurerGate.state -> ((MaurerGate.ST.round) List.list -> ((MaurerGate.ST.in_msgs) MaurerGate.ST.pmap * MaurerGate.state)))))) =
                                                                                                                                                                                                                                                                                                          (MaurerGate.stateful_protocol''')
        let rec stateful_protocol'' : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.in_msgs) MaurerGate.ST.pmap -> (MaurerGate.state -> (MaurerGate.ST.round -> ((MaurerGate.ST.in_msgs) MaurerGate.ST.pmap * MaurerGate.state)))))) =
                                                                                                                                                                                                                                                                                             (MaurerGate.stateful_protocol'')
        let rec stateful_protocol' : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> ((MaurerGate.ST.in_msgs) MaurerGate.ST.pmap * MaurerGate.state)))) =
                                                                                                                                                                                                                                                (MaurerGate.stateful_protocol')
        let rec stateful_protocol : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> (((MaurerGate.ST.local_input * (MaurerGate.ST.in_msgs * MaurerGate.ST.local_rand))) MaurerGate.ST.P.arrayN * (MaurerGate.ST.local_output) MaurerGate.ST.P.arrayN)))) =
                                                                                                                                                                                                                                                                                                                                                 (MaurerGate.stateful_protocol)
        let rec stateful_protocol_sz' : (Pervasive.int -> (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> ((MaurerGate.ST.in_msgs) MaurerGate.ST.pmap * MaurerGate.state))))) =
                                                                                                                                                                                                                                                                      (MaurerGate.stateful_protocol_sz')
        let rec stateful_protocol_sz : (Pervasive.int -> (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> (((MaurerGate.ST.local_input * (MaurerGate.ST.in_msgs * MaurerGate.ST.local_rand))) MaurerGate.ST.P.arrayN * (MaurerGate.ST.local_output) MaurerGate.ST.P.arrayN))))) =
                                                                                                                                                                                                                                                                                                                                                                       (MaurerGate.stateful_protocol_sz)
        let rec local_protocol_round : (MaurerGate.ST.party -> (MaurerGate.ST.round -> (MaurerGate.ST.public_input -> (MaurerGate.ST.local_input -> (MaurerGate.ST.local_rand -> (MaurerGate.ST.in_msgs -> MaurerGate.ST.pmsgs)))))) =
                                                                                                                                                                                                                                         (MaurerGate.local_protocol_round)
        let rec local_protocol_end : (MaurerGate.ST.party -> (MaurerGate.ST.public_input -> (MaurerGate.ST.local_input -> (MaurerGate.ST.local_rand -> (MaurerGate.ST.in_msgs -> MaurerGate.ST.local_output))))) =
                                                                                                                                                                                                                     (MaurerGate.local_protocol_end)
        let rec local_protocol'' : (MaurerGate.ST.party -> (MaurerGate.ST.public_input -> (MaurerGate.ST.local_input -> (MaurerGate.ST.local_rand -> (MaurerGate.ST.in_msgs -> (Pervasive.int -> (MaurerGate.ST.round -> MaurerGate.ST.out_msgs))))))) =
                                                                                                                                                                                                                                                           (MaurerGate.local_protocol'')
        let rec local_protocol' : (MaurerGate.ST.party -> (MaurerGate.ST.public_input -> (MaurerGate.ST.view -> MaurerGate.ST.out_msgs))) =
                                                                                                                                              (MaurerGate.local_protocol')
        let rec local_protocol : (MaurerGate.ST.party -> (MaurerGate.ST.public_input -> (MaurerGate.ST.view -> (MaurerGate.ST.out_msgs * MaurerGate.ST.local_output)))) =
                                                                                                                                                                            (MaurerGate.local_protocol)
        let rec protocol_round : (MaurerGate.ST.round -> (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> ((MaurerGate.ST.in_msgs) MaurerGate.ST.pmap -> (MaurerGate.ST.pmsgs) MaurerGate.ST.P.arrayN))))) =
                                                                                                                                                                                                                                                                                                  (MaurerGate.protocol_round)
        let rec protocol_end : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> ((MaurerGate.ST.in_msgs) MaurerGate.ST.pmap -> (MaurerGate.ST.local_output) MaurerGate.ST.P.arrayN)))) =
                                                                                                                                                                                                                                                                              (MaurerGate.protocol_end)
        let rec protocol''' : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> ((MaurerGate.ST.in_msgs) MaurerGate.ST.pmap -> (MaurerGate.ST.round -> (MaurerGate.ST.round -> (MaurerGate.ST.in_msgs) MaurerGate.ST.pmap)))))) =
                                                                                                                                                                                                                                                                                                                      (MaurerGate.protocol''')
        let rec protocol'' : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> ((MaurerGate.ST.in_msgs) MaurerGate.ST.pmap -> (MaurerGate.ST.round -> (MaurerGate.ST.in_msgs) MaurerGate.ST.pmap))))) =
                                                                                                                                                                                                                                                                                            (MaurerGate.protocol'')
        let rec protocol' : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> (MaurerGate.ST.in_msgs) MaurerGate.ST.pmap))) =
                                                                                                                                                                                                                  (MaurerGate.protocol')
        let rec protocol : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> (((MaurerGate.ST.local_input * (MaurerGate.ST.in_msgs * MaurerGate.ST.local_rand))) MaurerGate.ST.P.arrayN * (MaurerGate.ST.local_output) MaurerGate.ST.P.arrayN)))) =
                                                                                                                                                                                                                                                                                                                                        (MaurerGate.protocol)
        let rec get_view_in_msgs : (MaurerGate.ST.party -> (MaurerGate.ST.view -> MaurerGate.ST.rmsgs)) =
                                                                                                            (MaurerGate.get_view_in_msgs)
        let rec get_view_out_msgs : (MaurerGate.ST.party -> (MaurerGate.ST.party -> (MaurerGate.ST.public_input -> (MaurerGate.ST.view -> MaurerGate.ST.rmsgs)))) =
                                                                                                                                                                      (MaurerGate.get_view_out_msgs)
        let rec consistent_inputs : (MaurerGate.gate -> (NextMsgMaurerAPI.MaurerAPI.pid -> (NextMsgMaurerAPI.MaurerAPI.pid -> ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) -> ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) -> Pervasive.bool))))) =
                                                                                                                                                                                                                                                                                                                (MaurerGate.consistent_inputs)
        let rec consistent_rands : (MaurerGate._Gate -> (MaurerGate.ST.party -> (MaurerGate.ST.party -> (MaurerGate.GT.local_rand -> (MaurerGate.GT.local_rand -> Pervasive.bool))))) =
                                                                                                                                                                                          (MaurerGate.consistent_rands)
        let rec valid_inputs : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_input) MaurerGate.ST.pmap -> Pervasive.bool)) =
                                                                                                                                      (MaurerGate.valid_inputs)
        let rec valid_rands : (MaurerGate.ST.public_input -> ((MaurerGate.ST.local_rand) MaurerGate.ST.pmap -> Pervasive.bool)) =
                                                                                                                                    (MaurerGate.valid_rands)
        let rec consistent_views : (MaurerGate.ST.public_input -> (MaurerGate.ST.party -> (MaurerGate.ST.party -> (MaurerGate.ST.view -> (MaurerGate.ST.view -> Pervasive.bool))))) =
                                                                                                                                                                                        (MaurerGate.consistent_views)
        let rec consistent_trace : (MaurerGate.ST.public_input -> (MaurerGate.ST.trace -> Pervasive.bool)) =
                                                                                                               (MaurerGate.consistent_trace)
        let rec pairwise_consistent_views : (MaurerGate.ST.public_input -> (MaurerGate.ST.party -> (MaurerGate.ST.party -> (MaurerGate.ST.view -> (MaurerGate.ST.view -> Pervasive.bool))))) =
                                                                                                                                                                                                 (MaurerGate.pairwise_consistent_views)
        let rec pairwise_consistent_trace : (MaurerGate.ST.public_input -> (MaurerGate.ST.trace -> Pervasive.bool)) =
                                                                                                                        (MaurerGate.pairwise_consistent_trace)
        let rec view_output : (MaurerGate.ST.party -> (MaurerGate.ST.public_input -> (MaurerGate.ST.view -> MaurerGate.ST.local_output))) =
                                                                                                                                              (MaurerGate.view_output)
        let rec view_outputs : (MaurerGate.ST.public_input -> ((MaurerGate.ST.view) MaurerGate.ST.pmap -> (MaurerGate.ST.local_output) MaurerGate.ST.P.arrayN)) =
                                                                                                                                                                    (MaurerGate.view_outputs)
        let rec stateful_consistent_outputs : (MaurerGate.ST.public_input -> (MaurerGate.ST.party -> (MaurerGate.ST.party -> (MaurerGate.ST.local_output -> (MaurerGate.ST.local_output -> Pervasive.bool))))) =
                                                                                                                                                                                                                   (MaurerGate.stateful_consistent_outputs)
        type local_state2 = MaurerGate.local_state2
        let rec stateful_consistent_views_outputs_round : (MaurerGate.ST.round -> (MaurerGate.ST.public_input -> (MaurerGate.ST.party -> (MaurerGate.ST.party -> (MaurerGate.ST.local_input -> (MaurerGate.ST.local_input -> (MaurerGate.ST.in_msgs -> (MaurerGate.ST.in_msgs -> (MaurerGate.local_state2 -> ((MaurerGate.local_state * MaurerGate.local_state) * Pervasive.bool)))))))))) =
                                                                                                                                                                                                                                                                                                                                                                                               (MaurerGate.stateful_consistent_views_outputs_round)
        let rec stateful_consistent_views_outputs''' : (MaurerGate.ST.public_input -> (MaurerGate.ST.party -> (MaurerGate.ST.party -> (MaurerGate.ST.local_input -> (MaurerGate.ST.local_input -> (MaurerGate.ST.in_msgs -> (MaurerGate.ST.in_msgs -> (MaurerGate.local_state2 -> ((MaurerGate.ST.round) List.list -> (MaurerGate.local_state2 * Pervasive.bool)))))))))) =
                                                                                                                                                                                                                                                                                                                                                                              (MaurerGate.stateful_consistent_views_outputs''')
        let rec stateful_consistent_views_outputs'' : (MaurerGate.ST.public_input -> (MaurerGate.ST.party -> (MaurerGate.ST.party -> (MaurerGate.ST.local_input -> (MaurerGate.ST.local_input -> (MaurerGate.ST.in_msgs -> (MaurerGate.ST.in_msgs -> (MaurerGate.local_state2 -> (MaurerGate.local_state2 * Pervasive.bool))))))))) =
                                                                                                                                                                                                                                                                                                                                        (MaurerGate.stateful_consistent_views_outputs'')
        let rec stateful_consistent_views_outputs' : (MaurerGate.ST.public_input -> (MaurerGate.ST.party -> (MaurerGate.ST.party -> (MaurerGate.ST.view -> (MaurerGate.ST.view -> (MaurerGate.local_state2 * Pervasive.bool)))))) =
                                                                                                                                                                                                                                      (MaurerGate.stateful_consistent_views_outputs')
        let rec stateful_consistent_views_outputs : (MaurerGate.ST.public_input -> (MaurerGate.ST.party -> (MaurerGate.ST.party -> (MaurerGate.ST.view -> (MaurerGate.ST.view -> Pervasive.bool))))) =
                                                                                                                                                                                                         (MaurerGate.stateful_consistent_views_outputs)
        let rec g_protocol : (MaurerGate._Gate -> ((MaurerGate.share) MaurerGate.GT.pmap -> ((MaurerGate.GT.local_rand) MaurerGate.GT.pmap -> (((MaurerGate.share * (((MaurerGate.GT.msg) NextMsgArray.Array.array) MaurerGate.GT.P.arrayN * MaurerGate.GT.local_rand))) MaurerGate.GT.P.arrayN * (MaurerGate.share) MaurerGate.GT.P.arrayN)))) =
                                                                                                                                                                                                                                                                                                                                                    (MaurerGate.g_protocol)
    end
    type _Circuit = (G._Gate) List.list
    module CT = struct
        type public_input = _Circuit
        module P = struct
            let rec size : Pervasive.int =
                                             (G.GT.P.size)
            type ('a) arrayN = ('a) G.GT.P.arrayN
            let rec get : (('a) G.GT.P.arrayN -> (Pervasive.int -> 'a)) =
                                                                            (G.GT.P.get)
            let rec set : (('a) G.GT.P.arrayN -> (Pervasive.int -> ('a -> ('a) G.GT.P.arrayN))) =
                                                                                                    (G.GT.P.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a) G.GT.P.arrayN) =
                                                                             (G.GT.P.init)
            let rec of_list : (('a) List.list -> ('a) G.GT.P.arrayN) =
                                                                         (G.GT.P.of_list)
            let rec to_list : (('a) G.GT.P.arrayN -> ('a) List.list) =
                                                                         (G.GT.P.to_list)
            let rec to_assoc : (('a) G.GT.P.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                            (G.GT.P.to_assoc)
            let rec create : ('a -> ('a) G.GT.P.arrayN) =
                                                            (G.GT.P.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) G.GT.P.arrayN)) =
                                                                              (G.GT.P.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) G.GT.P.arrayN -> ('b) G.GT.P.arrayN)) =
                                                                                                             (G.GT.P.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) G.GT.P.arrayN -> (('b) G.GT.P.arrayN -> ('c) G.GT.P.arrayN))) =
                                                                                                                           (G.GT.P.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) G.GT.P.arrayN -> ('a) G.GT.P.arrayN)) =
                                                                                                                           (G.GT.P.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) G.GT.P.arrayN -> Pervasive.bool)) =
                                                                                                                    (G.GT.P.all)
            let rec allsame : (('a) G.GT.P.arrayN -> Pervasive.bool) =
                                                                         (G.GT.P.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) G.GT.P.arrayN) List.list -> (('b) List.list) G.GT.P.arrayN) =
                                                                                                    (G.GT.P.concat)
        end
        let rec parties : Pervasive.int =
                                            (G.GT.parties)
        type party = Pervasive.int
        let partyset : NextMsgISet.ISet.iset =
                                                 (NextMsgISet.ISet.iset (parties))
        type round = Pervasive.int
        let rounds (c : (G._Gate) List.list) : Pervasive.int =
                                                                 (List.size c)
        let roundset (p : public_input) : NextMsgISet.ISet.iset =
                                                                    (NextMsgISet.ISet.iset (rounds p))
        type ('a) pmap = ('a) P.arrayN
        type ('a) rmap = ('a) NextMsgArray.Array.array
        type ('a) prmap = (('a) rmap) pmap
        type ('a) ppmap = (('a) pmap) pmap
        type ('a) pprmap = (('a) rmap) ppmap
        type local_input = G.share
        type local_output = G.share
        type local_rand = (G.GT.local_rand) List.list
        type msg = G.GT.msg
        type pmsgs = (msg) pmap
        type rmsgs = (msg) rmap
        type prmsgs = (rmsgs) pmap
        type ppmsgs = (pmsgs) pmap
        type pprmsgs = (prmsgs) pmap
        type in_msgs = prmsgs
        type out_msgs = prmsgs
        type view = (local_input * (in_msgs * local_rand))
        type trace = (view) pmap
        let rec eq_msg : (G.GT.msg -> (G.GT.msg -> Pervasive.bool)) =
                                                                        (G.GT.eq_msg)
        let eq_pmsgs (m1 : pmsgs) (m2 : pmsgs) : Pervasive.bool =
                                                                    (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (P.get m1 i) (P.get m2 i))) (P.size))
        let eq_rmsgs (m1 : rmsgs) (m2 : rmsgs) : Pervasive.bool =
                                                                    (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size m1) (NextMsgArray.Array.size m2)) (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (NextMsgArray.Array.get m1 i) (NextMsgArray.Array.get m2 i))) (NextMsgArray.Array.size m1)))
        let pinit (f : (party -> 'a)) : ('a) P.arrayN =
                                                          (P.init f)
        let ppinit (f : (party -> (party -> 'a))) : (('a) P.arrayN) P.arrayN =
                                                                                 (pinit (fun (i : party) -> (pinit (f i))))
        let prempty (sz : Pervasive.int) (v : 'a) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                 (pinit (fun (_ : party) -> (NextMsgArray.Array.create sz v)))
        let pprempty (sz : Pervasive.int) (v : 'a) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                             (ppinit (fun (_ : party) (_ : party) -> (NextMsgArray.Array.create sz v)))
        let ppswap (m : ('a) ppmap) : (('a) P.arrayN) P.arrayN =
                                                                   (ppinit (fun (j : Pervasive.int) (i : Pervasive.int) -> (P.get (P.get m i) j)))
        let prget (xs : ('a) prmap) (r : round) : ('a) P.arrayN =
                                                                    (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.get (P.get xs i) r)))
        let pprget (xs : ('a) pprmap) (r : round) : (('a) P.arrayN) P.arrayN =
                                                                                 (ppinit (fun (i : Pervasive.int) (j : Pervasive.int) -> (NextMsgArray.Array.get (P.get (P.get xs i) j) r)))
        let prset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.merge (fun (x0 : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set x0 n y)) xs x)
        let prext (sz : Pervasive.int) (xs : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.init sz (fun (j : Pervasive.int) -> if (Pervasive._and (Int.le (Pervasive.mk_int 0) j) (Int.lt j (NextMsgArray.Array.size (P.get xs i)))) then (NextMsgArray.Array.get (P.get xs i) j) else (Pervasive.witness)))))
        let prextset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                          (prset (prext (Int.plus n (Pervasive.mk_int 1)) xs) n x)
        let pprset (xs : ('a) pprmap) (n : round) (x : ('a) ppmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                             (P.merge (P.merge (fun (ys : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set ys n y))) xs x)
        let prfilter (p : (round -> Pervasive.bool)) (ins : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) ins)
        let pprfilter (p : (round -> Pervasive.bool)) (ins : ('a) pprmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                                    (P.map (fun (xs : (('a) NextMsgArray.Array.array) P.arrayN) -> (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) xs)) ins)
        let rdom (sz : Pervasive.int) (round : round) (xs : ('a) rmap) : Pervasive.bool =
                                                                                            (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size xs) sz) (Pervasive.witness))
        let prdom (sz : Pervasive.int) (round : round) (xs : ('a) prmap) : Pervasive.bool =
                                                                                              (P.all (fun (_ : Pervasive.int) -> (rdom sz round)) xs)
        let pprdom (sz : Pervasive.int) (round : round) (xs : ('a) pprmap) : Pervasive.bool =
                                                                                                (P.all (fun (_ : Pervasive.int) -> (prdom sz round)) xs)
        let rlist (sz : Pervasive.int) (xs : ('a) List.list) : ('a) NextMsgArray.Array.array =
                                                                                                 (List.foldl (fun (rs : ('a) NextMsgArray.Array.array) (i : Pervasive.int) -> (NextMsgArray.Array.set rs i (List.nth (Pervasive.witness) xs i))) (NextMsgArray.Array.create sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let prlist (sz : Pervasive.int) (xs : (pmsgs) List.list) : (msg) prmap =
                                                                                   (List.foldl (fun (rs : (msg) prmap) (i : Pervasive.int) -> (prset rs i (List.nth (Pervasive.witness) xs i))) (prempty sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let pcons (x : ('a) pmap) (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                               (P.merge (fun (x0 : 'a) (xs0 : ('a) List.list) -> (AuxList.cons x0 xs0)) x xs)
        let phead (xs : (('a) List.list) pmap) : ('a) P.arrayN =
                                                                   (P.map (List.head (Pervasive.witness)) xs)
        let pbehead (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                 (P.map (List.behead) xs)
        let prcons (xs : (('a) List.list) pmap) (x : ('a) pmap) : (('a) List.list) P.arrayN =
                                                                                                (P.merge (List.rcons) xs x)
        let pcat (xs : (('a) List.list) pmap) (ys : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                                           (P.merge (fun (x : ('a) List.list) (y : ('a) List.list) -> (AuxList.cat x y)) xs ys)
        let ppcons (x : ('a) ppmap) (xs : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                             (P.merge (pcons) x xs)
        let pprcons (xs : (('a) List.list) ppmap) (x : ('a) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                              (P.merge (prcons) xs x)
        let ppcat (xs : (('a) List.list) ppmap) (ys : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                                         (P.merge (pcat) xs ys)
        let prmsgs_up_to (round : round) (ins : prmsgs) : ((msg) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (prfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let pprmsgs_up_to (round : round) (ins : pprmsgs) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                     (pprfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let get_trace_inputs (tr : trace) : (local_input) P.arrayN =
                                                                       (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.fst3 x)) tr)
        let get_trace_in_msgs (tr : trace) : (in_msgs) P.arrayN =
                                                                    (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.snd3 x)) tr)
        let get_trace_rands (tr : trace) : (local_rand) P.arrayN =
                                                                     (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.thr3 x)) tr)
        let get_view (i : party) (tr : trace) : view =
                                                         (P.get tr i)
        let get_trace_in_msgs_round (round : round) (tr : trace) : ((msg) P.arrayN) P.arrayN =
                                                                                                 (pprget (get_trace_in_msgs tr) round)
        let get_view_in_msgs_round (round : round) (v : view) : (msg) P.arrayN =
                                                                                   (prget (Aux.snd3 v) round)
        let add_view_in_msgs (r : round) (ins : pmsgs) (v : view) : (local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand)) =
                                                                                                                                                 ((Aux.fst3 v) , ((prset (Aux.snd3 v) r ins) , (Aux.thr3 v)))
        let get_trace_in_msgs_up_to (round : round) (tr : trace) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                            (pprmsgs_up_to round (get_trace_in_msgs tr))
        let add_trace_in_msgs (r : round) (ins : ppmsgs) (tr : trace) : ((local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand))) P.arrayN =
                                                                                                                                                                (P.map (fun (ins_v : (pmsgs * view)) -> (add_view_in_msgs r (Aux.fst3 ins_v) (snd ins_v))) (P.zip ins tr))
        let valid_trace (x : public_input) (tr : trace) : Pervasive.bool =
                                                                             (pprdom (rounds x) (rounds x) (get_trace_in_msgs tr))
        let valid_view (x : public_input) (v : view) : Pervasive.bool =
                                                                          (prdom (rounds x) (rounds x) (Aux.snd3 v))
    end
    let circ_valid_rand (c : (G._Gate) List.list) (rs : CT.local_rand) : Pervasive.bool =
                                                                                            (Pervasive._and (Pervasive.eq (List.size c) (List.size rs)) (AuxList.lsame (fun (g : G._Gate) (r : G.GT.local_rand) -> (G.gate_valid_rand g r)) c rs))
    module ST = struct
        type public_input = CT.public_input
        module P = struct
            let rec size : Pervasive.int =
                                             (CT.P.size)
            type ('a) arrayN = ('a) CT.P.arrayN
            let rec get : (('a) G.GT.P.arrayN -> (Pervasive.int -> 'a)) =
                                                                            (CT.P.get)
            let rec set : (('a) G.GT.P.arrayN -> (Pervasive.int -> ('a -> ('a) G.GT.P.arrayN))) =
                                                                                                    (CT.P.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a) G.GT.P.arrayN) =
                                                                             (CT.P.init)
            let rec of_list : (('a) List.list -> ('a) G.GT.P.arrayN) =
                                                                         (CT.P.of_list)
            let rec to_list : (('a) G.GT.P.arrayN -> ('a) List.list) =
                                                                         (CT.P.to_list)
            let rec to_assoc : (('a) G.GT.P.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                            (CT.P.to_assoc)
            let rec create : ('a -> ('a) G.GT.P.arrayN) =
                                                            (CT.P.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) G.GT.P.arrayN)) =
                                                                              (CT.P.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) G.GT.P.arrayN -> ('b) G.GT.P.arrayN)) =
                                                                                                             (CT.P.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) G.GT.P.arrayN -> (('b) G.GT.P.arrayN -> ('c) G.GT.P.arrayN))) =
                                                                                                                           (CT.P.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) G.GT.P.arrayN -> ('a) G.GT.P.arrayN)) =
                                                                                                                           (CT.P.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) G.GT.P.arrayN -> Pervasive.bool)) =
                                                                                                                    (CT.P.all)
            let rec allsame : (('a) G.GT.P.arrayN -> Pervasive.bool) =
                                                                         (CT.P.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) G.GT.P.arrayN) List.list -> (('b) List.list) G.GT.P.arrayN) =
                                                                                                    (CT.P.concat)
        end
        let rec parties : Pervasive.int =
                                            (CT.parties)
        type party = CT.party
        let rec partyset : NextMsgISet.ISet.iset =
                                                     (CT.partyset)
        type round = CT.round
        let rec rounds : ((G._Gate) List.list -> Pervasive.int) =
                                                                    (CT.rounds)
        let rec roundset : (CT.public_input -> NextMsgISet.ISet.iset) =
                                                                          (CT.roundset)
        type ('a) pmap = ('a) CT.pmap
        type ('a) rmap = ('a) CT.rmap
        type ('a) prmap = ('a) CT.prmap
        type ('a) ppmap = ('a) CT.ppmap
        type ('a) pprmap = ('a) CT.pprmap
        type local_input = CT.local_input
        type local_output = CT.local_output
        type local_rand = CT.local_rand
        type msg = CT.msg
        type pmsgs = CT.pmsgs
        type rmsgs = CT.rmsgs
        type prmsgs = CT.prmsgs
        type ppmsgs = CT.ppmsgs
        type pprmsgs = CT.pprmsgs
        type in_msgs = CT.in_msgs
        type out_msgs = CT.out_msgs
        type view = CT.view
        type trace = CT.trace
        let rec eq_msg : (G.GT.msg -> (G.GT.msg -> Pervasive.bool)) =
                                                                        (CT.eq_msg)
        let rec eq_pmsgs : (CT.pmsgs -> (CT.pmsgs -> Pervasive.bool)) =
                                                                          (CT.eq_pmsgs)
        let rec eq_rmsgs : (CT.rmsgs -> (CT.rmsgs -> Pervasive.bool)) =
                                                                          (CT.eq_rmsgs)
        let rec pinit : ((CT.party -> 'a) -> ('a) CT.P.arrayN) =
                                                                   (CT.pinit)
        let rec ppinit : ((CT.party -> (CT.party -> 'a)) -> (('a) CT.P.arrayN) CT.P.arrayN) =
                                                                                                (CT.ppinit)
        let rec prempty : (Pervasive.int -> ('a -> (('a) NextMsgArray.Array.array) CT.P.arrayN)) =
                                                                                                     (CT.prempty)
        let rec pprempty : (Pervasive.int -> ('a -> ((('a) NextMsgArray.Array.array) CT.P.arrayN) CT.P.arrayN)) =
                                                                                                                    (CT.pprempty)
        let rec ppswap : (('a) CT.ppmap -> (('a) CT.P.arrayN) CT.P.arrayN) =
                                                                               (CT.ppswap)
        let rec prget : (('a) CT.prmap -> (CT.round -> ('a) CT.P.arrayN)) =
                                                                              (CT.prget)
        let rec pprget : (('a) CT.pprmap -> (CT.round -> (('a) CT.P.arrayN) CT.P.arrayN)) =
                                                                                              (CT.pprget)
        let rec prset : (('a) CT.prmap -> (Pervasive.int -> (('a) CT.pmap -> (('a) NextMsgArray.Array.array) CT.P.arrayN))) =
                                                                                                                                (CT.prset)
        let rec prext : (Pervasive.int -> (('a) CT.prmap -> (('a) NextMsgArray.Array.array) CT.P.arrayN)) =
                                                                                                              (CT.prext)
        let rec prextset : (('a) CT.prmap -> (Pervasive.int -> (('a) CT.pmap -> (('a) NextMsgArray.Array.array) CT.P.arrayN))) =
                                                                                                                                   (CT.prextset)
        let rec pprset : (('a) CT.pprmap -> (CT.round -> (('a) CT.ppmap -> ((('a) NextMsgArray.Array.array) CT.P.arrayN) CT.P.arrayN))) =
                                                                                                                                            (CT.pprset)
        let rec prfilter : ((CT.round -> Pervasive.bool) -> (('a) CT.prmap -> (('a) NextMsgArray.Array.array) CT.P.arrayN)) =
                                                                                                                                (CT.prfilter)
        let rec pprfilter : ((CT.round -> Pervasive.bool) -> (('a) CT.pprmap -> ((('a) NextMsgArray.Array.array) CT.P.arrayN) CT.P.arrayN)) =
                                                                                                                                                (CT.pprfilter)
        let rec rdom : (Pervasive.int -> (CT.round -> (('a) CT.rmap -> Pervasive.bool))) =
                                                                                             (CT.rdom)
        let rec prdom : (Pervasive.int -> (CT.round -> (('a) CT.prmap -> Pervasive.bool))) =
                                                                                               (CT.prdom)
        let rec pprdom : (Pervasive.int -> (CT.round -> (('a) CT.pprmap -> Pervasive.bool))) =
                                                                                                 (CT.pprdom)
        let rec rlist : (Pervasive.int -> (('a) List.list -> ('a) NextMsgArray.Array.array)) =
                                                                                                 (CT.rlist)
        let rec prlist : (Pervasive.int -> ((CT.pmsgs) List.list -> (CT.msg) CT.prmap)) =
                                                                                            (CT.prlist)
        let rec pcons : (('a) CT.pmap -> ((('a) List.list) CT.pmap -> (('a) List.list) CT.P.arrayN)) =
                                                                                                         (CT.pcons)
        let rec phead : ((('a) List.list) CT.pmap -> ('a) CT.P.arrayN) =
                                                                           (CT.phead)
        let rec pbehead : ((('a) List.list) CT.pmap -> (('a) List.list) CT.P.arrayN) =
                                                                                         (CT.pbehead)
        let rec prcons : ((('a) List.list) CT.pmap -> (('a) CT.pmap -> (('a) List.list) CT.P.arrayN)) =
                                                                                                          (CT.prcons)
        let rec pcat : ((('a) List.list) CT.pmap -> ((('a) List.list) CT.pmap -> (('a) List.list) CT.P.arrayN)) =
                                                                                                                    (CT.pcat)
        let rec ppcons : (('a) CT.ppmap -> ((('a) List.list) CT.ppmap -> ((('a) List.list) CT.P.arrayN) CT.P.arrayN)) =
                                                                                                                          (CT.ppcons)
        let rec pprcons : ((('a) List.list) CT.ppmap -> (('a) CT.ppmap -> ((('a) List.list) CT.P.arrayN) CT.P.arrayN)) =
                                                                                                                           (CT.pprcons)
        let rec ppcat : ((('a) List.list) CT.ppmap -> ((('a) List.list) CT.ppmap -> ((('a) List.list) CT.P.arrayN) CT.P.arrayN)) =
                                                                                                                                     (CT.ppcat)
        let rec prmsgs_up_to : (CT.round -> (CT.prmsgs -> ((CT.msg) NextMsgArray.Array.array) CT.P.arrayN)) =
                                                                                                                (CT.prmsgs_up_to)
        let rec pprmsgs_up_to : (CT.round -> (CT.pprmsgs -> (((CT.msg) NextMsgArray.Array.array) CT.P.arrayN) CT.P.arrayN)) =
                                                                                                                                (CT.pprmsgs_up_to)
        let rec get_trace_inputs : (CT.trace -> (CT.local_input) CT.P.arrayN) =
                                                                                  (CT.get_trace_inputs)
        let rec get_trace_in_msgs : (CT.trace -> (CT.in_msgs) CT.P.arrayN) =
                                                                               (CT.get_trace_in_msgs)
        let rec get_trace_rands : (CT.trace -> (CT.local_rand) CT.P.arrayN) =
                                                                                (CT.get_trace_rands)
        let rec get_view : (CT.party -> (CT.trace -> CT.view)) =
                                                                   (CT.get_view)
        let rec get_trace_in_msgs_round : (CT.round -> (CT.trace -> ((CT.msg) CT.P.arrayN) CT.P.arrayN)) =
                                                                                                             (CT.get_trace_in_msgs_round)
        let rec get_view_in_msgs_round : (CT.round -> (CT.view -> (CT.msg) CT.P.arrayN)) =
                                                                                             (CT.get_view_in_msgs_round)
        let rec add_view_in_msgs : (CT.round -> (CT.pmsgs -> (CT.view -> (CT.local_input * (((CT.msg) NextMsgArray.Array.array) CT.P.arrayN * CT.local_rand))))) =
                                                                                                                                                                     (CT.add_view_in_msgs)
        let rec get_trace_in_msgs_up_to : (CT.round -> (CT.trace -> (((CT.msg) NextMsgArray.Array.array) CT.P.arrayN) CT.P.arrayN)) =
                                                                                                                                        (CT.get_trace_in_msgs_up_to)
        let rec add_trace_in_msgs : (CT.round -> (CT.ppmsgs -> (CT.trace -> ((CT.local_input * (((CT.msg) NextMsgArray.Array.array) CT.P.arrayN * CT.local_rand))) CT.P.arrayN))) =
                                                                                                                                                                                      (CT.add_trace_in_msgs)
        let rec valid_trace : (CT.public_input -> (CT.trace -> Pervasive.bool)) =
                                                                                    (CT.valid_trace)
        let rec valid_view : (CT.public_input -> (CT.view -> Pervasive.bool)) =
                                                                                  (CT.valid_view)
    end
    type local_messages = G.local_msgs
    type messages = (local_messages) ST.pmap
    type local_out_messages = local_messages
    type local_in_messages = local_messages
    type out_messages = messages
    type in_messages = messages
    let rec from_local_messages : (G.local_messages -> G.ST.pmsgs) =
                                                                       (G.from_local_messages)
    let rec to_local_messages : (G.ST.pmsgs -> G.local_messages) =
                                                                     (G.to_local_messages)
    let rec send_messages : (G.out_messages -> G.in_messages) =
                                                                  (G.send_messages)
    let from_messages (xs : (local_messages) ST.P.arrayN) : (ST.pmsgs) ST.P.arrayN =
                                                                                       (ST.P.map (from_local_messages) xs)
    let to_messages (xs : (ST.pmsgs) ST.P.arrayN) : (local_messages) ST.P.arrayN =
                                                                                     (ST.P.map (to_local_messages) xs)
    let rec valid_local_messages (p : (G.ST.public_input) List.list) (r : Pervasive.int) (ms : G.local_messages) : Pervasive.bool =
                                                                                                                                      (G.valid_local_messages (List.nth (Pervasive.witness) p r) (Pervasive.mk_int 0) ms)
    let valid_messages (p : ST.public_input) (r : ST.round) (ms : messages) : Pervasive.bool =
                                                                                                 (ST.P.all (fun (_ : Pervasive.int) -> (valid_local_messages p r)) ms)
    let rec valid_msg (p : (G.ST.public_input) List.list) (r : Pervasive.int) (ms : G.ST.msg) : Pervasive.bool =
                                                                                                                   (G.valid_msg (List.nth (Pervasive.witness) p r) (Pervasive.mk_int 0) ms)
    let valid_pmsgs (p : ST.public_input) (r : ST.round) (ms : ST.pmsgs) : Pervasive.bool =
                                                                                              (ST.P.all (fun (_ : Pervasive.int) -> (valid_msg p r)) ms)
    let valid_ppmsgs (p : ST.public_input) (r : ST.round) (ms : ST.ppmsgs) : Pervasive.bool =
                                                                                                (ST.P.all (fun (_ : Pervasive.int) -> (valid_pmsgs p r)) ms)
    type local_state = (G.share * CT.local_rand)
    let init_local_state (_ : ST.party) (_ : ST.public_input) (ws : CT.local_input) (rs : ST.local_rand) : (CT.local_input * ST.local_rand) =
                                                                                                                                                (ws , rs)
    let update_local_state (i : G.GT.party) (r : CT.round) (c : CT.public_input) (_ : CT.local_input) (ins : local_in_messages) (st : (G.share * CT.local_rand)) : (G.share * (G.GT.local_rand) List.list) =
                                                                                                                                                                                                               (let (g) = (List.nth (Pervasive.witness) c r) in
                                                                                                                                                                                                                ((G.local_gate_end i g (fst st) ins) , (List.behead (snd st))))
    let get_local_state (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : local_state =
                                                                                                                                                             (let (go) = (fun (st : local_state) (r0 : ST.round) -> (let (insr) = (ST.prget insi r0) in
                                                                                                                                                                                                                     (update_local_state i r0 x wi (to_local_messages insr) st))) in
                                                                                                                                                              (List.foldl go (init_local_state i x wi ri) (AuxList.iseq r)))
    type state = (local_state) ST.pmap
    let init_state (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                        (ST.P.imap (fun (i : ST.party) (wi_ri : (ST.local_input * ST.local_rand)) -> (init_local_state i x (fst wi_ri) (snd wi_ri))) (ST.P.zip ws rs))
    let update_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (local_in_messages) ST.pmap) (st : state) : (local_state) ST.P.arrayN =
                                                                                                                                                                               (ST.P.imap (fun (i : ST.party) (wsi_insi_sti : (ST.local_input * (local_in_messages * local_state))) -> (update_local_state i round x (Aux.fst3 wsi_insi_sti) (Aux.snd3 wsi_insi_sti) (Aux.thr3 wsi_insi_sti))) (ST.P.zip3 ws ins st))
    let get_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                                                                       (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (get_local_state i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) (ST.P.zip3 ws rs ins))
    let stateful_local_protocol_round (i : G.GT.party) (r : CT.round) (c : CT.public_input) (st : (G.share * CT.local_rand)) : G.local_out_msgs =
                                                                                                                                                    (let (g) = (List.nth (Pervasive.witness) c r) in
                                                                                                                                                     (G.local_gate_start i g (fst st) (List.head (Pervasive.witness) (snd st))))
    let stateful_local_protocol_end (_ : CT.party) (_ : CT.public_input) (st : (G.share * CT.local_rand)) : G.share =
                                                                                                                        (fst st)
    let stateful_local_protocol''' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : (ST.round) List.list) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                                            (List.foldl (fun (acc : (local_state * ST.out_msgs)) (round : ST.round) -> (let (outs') = (ST.prset (snd acc) round (from_local_messages (stateful_local_protocol_round i round x (Aux.fst3 acc)))) in
                                                                                                                                                                                                                                                                                                        (let (st') = (update_local_state i round x inp (to_local_messages (ST.prget ins round)) (Aux.fst3 acc)) in
                                                                                                                                                                                                                                                                                                         (st' , outs')))) (st , (ST.prempty sz (Pervasive.witness))) rounds)
    let stateful_local_protocol'' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                               (stateful_local_protocol''' i x inp st ins sz (AuxList.iseq rounds))
    let stateful_local_protocol' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) : (local_state * ST.out_msgs) =
                                                                                                                                                                     (stateful_local_protocol'' i x inp st ins (ST.rounds x) (ST.rounds x))
    let stateful_local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                          (let (outs) = (stateful_local_protocol' i x (Aux.fst3 vi) (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) (Aux.snd3 vi)) in
                                                                                                                           (let (out) = (stateful_local_protocol_end i x (Aux.fst3 outs)) in
                                                                                                                            ((snd outs) , out)))
    let stateful_protocol_round (round : ST.round) (x : ST.public_input) (st : state) : (local_out_messages) ST.P.arrayN =
                                                                                                                             (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_round i round x sti)) st)
    let stateful_protocol_end (x : ST.public_input) (st : state) : (ST.local_output) ST.P.arrayN =
                                                                                                     (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_end i x sti)) st)
    let stateful_protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : (ST.round) List.list) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                                  (List.foldl (fun (ins_st : ((ST.in_msgs) ST.pmap * state)) (round : ST.round) -> (let (ins0) = (Aux.fst3 ins_st) in
                                                                                                                                                                                                                                                                                    (let (st0) = (snd ins_st) in
                                                                                                                                                                                                                                                                                     (let (outs) = (send_messages (stateful_protocol_round round x st0)) in
                                                                                                                                                                                                                                                                                      ((ST.pprset ins0 round (from_messages outs)) , (update_state round x ws outs st0)))))) (ins , st) rounds)
    let stateful_protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : ST.round) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                     (stateful_protocol''' x ws ins st (AuxList.iseq rounds))
    let stateful_protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                     (stateful_protocol'' x ws (ST.pprempty (ST.rounds x) (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                     (let (ins_st') = (stateful_protocol' x ws rs) in
                                                                                                                                                                                                                      (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                       (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                        (tr , outs))))
    let stateful_protocol_sz' (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                             (stateful_protocol'' x ws (ST.pprempty sz (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol_sz (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                                             (let (ins_st') = (stateful_protocol_sz' sz x ws rs) in
                                                                                                                                                                                                                                              (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                                               (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                                                (tr , outs))))
    let local_protocol_round (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.pmsgs =
                                                                                                                                                               (from_local_messages (stateful_local_protocol_round i r x (get_local_state i r x wi ri insi)))
    let local_protocol_end (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.local_output =
                                                                                                                                                     (stateful_local_protocol_end i x (get_local_state i (ST.rounds x) x wi ri insi))
    let local_protocol'' (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : ST.out_msgs =
                                                                                                                                                                                       (List.foldl (fun (outs : ST.out_msgs) (round : Pervasive.int) -> (ST.prset outs round (local_protocol_round i round x wi ri ins))) (ST.prempty sz (Pervasive.witness)) (AuxList.iseq rounds))
    let local_protocol' (i : ST.party) (x : ST.public_input) (vi : ST.view) : ST.out_msgs =
                                                                                              (local_protocol'' i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi) (ST.rounds x) (ST.rounds x))
    let local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                 (let (outs) = (local_protocol' i x vi) in
                                                                                                                  (let (out) = (local_protocol_end i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi)) in
                                                                                                                   (outs , out)))
    let protocol_round (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.pmsgs) ST.P.arrayN =
                                                                                                                                                                                         (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                                          (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_round i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol_end (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                                                                                           (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                            (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_end i x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (round1 : ST.round) (d : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (List.Iota.iota_ round1 d))
    let protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (rounds : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (AuxList.iseq rounds))
    let protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (ST.in_msgs) ST.pmap =
                                                                                                                                  (protocol'' x ws rs (ST.pprempty (ST.rounds x) (Pervasive.witness)) (ST.rounds x))
    let protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                            (let (ins) = (protocol' x ws rs) in
                                                                                                                                                                                                             (let (outs) = (protocol_end x ws rs ins) in
                                                                                                                                                                                                              (let (tr) = (ST.P.zip3 ws ins rs) in
                                                                                                                                                                                                               (tr , outs))))
    let get_view_in_msgs (j : ST.party) (vi : ST.view) : ST.rmsgs =
                                                                      (ST.P.get (Aux.snd3 vi) j)
    let get_view_out_msgs (i : ST.party) (j : ST.party) (x : ST.public_input) (vi : ST.view) : ST.rmsgs =
                                                                                                            (ST.P.get (local_protocol' i x vi) j)
    let consistent_inputs (x : circuit) (i : NextMsgMaurerAPI.MaurerAPI.pid) (j : NextMsgMaurerAPI.MaurerAPI.pid) (wi : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) (wj : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) : Pervasive.bool =
                                                                                                                                                                                                                                                                                                       (Pervasive._and (valid_circuit x (NextMsgMaurerAPI.MaurerAPI.get_wire_st_next (fst wi)) (snd wi)) (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.g_valid_share wi) (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.g_valid_share wj) (NextMsgMaurerAPI.MaurerAPI.consistent_shares i j wi wj))))
    let consistent_rands (c : (G._Gate) List.list) (_ : ST.party) (_ : ST.party) (r1 : CT.local_rand) (r2 : CT.local_rand) : Pervasive.bool =
                                                                                                                                                (Pervasive._and (circ_valid_rand c r1) (circ_valid_rand c r2))
    let valid_inputs (x : ST.public_input) (ws : (ST.local_input) ST.pmap) : Pervasive.bool =
                                                                                                (Pervasive.witness)
    let valid_rands (x : ST.public_input) (ws : (ST.local_rand) ST.pmap) : Pervasive.bool =
                                                                                              (Pervasive.witness)
    let consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                (Pervasive._and (ST.eq_rmsgs (get_view_in_msgs j vi) (get_view_out_msgs j i x vj)) (Pervasive._and (Pervasive.eq (get_view_in_msgs i vj) (get_view_out_msgs i j x vi)) (Pervasive._and (consistent_inputs x i j (Aux.fst3 vi) (Aux.fst3 vj)) (consistent_rands x i j (Aux.thr3 vi) (Aux.thr3 vj)))))
    let consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                    (Pervasive.witness)
    let pairwise_consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                         (Pervasive._and (ST.valid_view x vi) (Pervasive._and (ST.valid_view x vj) (consistent_views x i j vi vj)))
    let pairwise_consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                             (Pervasive.witness)
    let view_output (i : ST.party) (x : ST.public_input) (v : ST.view) : ST.local_output =
                                                                                             (local_protocol_end i x (Aux.fst3 v) (Aux.thr3 v) (Aux.snd3 v))
    let view_outputs (x : ST.public_input) (vs : (ST.view) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                        (ST.P.imap (fun (i : ST.party) (v : ST.view) -> (view_output i x v)) vs)
    let stateful_consistent_outputs : (ST.public_input -> (ST.party -> (ST.party -> (ST.local_output -> (ST.local_output -> Pervasive.bool))))) = Pervasive.witness
    type local_state2 = (local_state * local_state)
    let stateful_consistent_views_outputs_round (r : ST.round) (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : ((local_state * local_state) * Pervasive.bool) =
                                                                                                                                                                                                                                                                                     (let (outs1) = (from_local_messages (stateful_local_protocol_round i r x (Aux.fst3 sts))) in
                                                                                                                                                                                                                                                                                      (let (outs2) = (from_local_messages (stateful_local_protocol_round j r x (snd sts))) in
                                                                                                                                                                                                                                                                                       (let (in1) = (ST.prget ins1 r) in
                                                                                                                                                                                                                                                                                        (let (in2) = (ST.prget ins2 r) in
                                                                                                                                                                                                                                                                                         (let (sts1') = (update_local_state i r x inp1 (to_local_messages in1) (Aux.fst3 sts)) in
                                                                                                                                                                                                                                                                                          (let (sts2') = (update_local_state j r x inp2 (to_local_messages in2) (snd sts)) in
                                                                                                                                                                                                                                                                                           (let (b) = (Pervasive._and (ST.eq_msg (ST.P.get outs1 j) (ST.P.get in2 i)) (ST.eq_msg (ST.P.get outs2 i) (ST.P.get in1 j))) in
                                                                                                                                                                                                                                                                                            ((sts1' , sts2') , b))))))))
    let stateful_consistent_views_outputs''' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) (rounds : (ST.round) List.list) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                                                    (let (go) = (fun (stb : (local_state2 * Pervasive.bool)) (r : ST.round) -> (let (stb') = (stateful_consistent_views_outputs_round r x i j inp1 inp2 ins1 ins2 (fst stb)) in
                                                                                                                                                                                                                                                                                                                                                                ((fst stb') , (Pervasive._and (snd stb) (snd stb'))))) in
                                                                                                                                                                                                                                                                                     (List.foldl go (sts , (Pervasive._true)) rounds))
    let stateful_consistent_views_outputs'' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                   (stateful_consistent_views_outputs''' x i j inp1 inp2 ins1 ins2 sts (AuxList.iseq (ST.rounds x)))
    let stateful_consistent_views_outputs' (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                   (let (st1) = (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) in
                                                                                                                                                                    (let (st2) = (init_local_state j x (Aux.fst3 vj) (Aux.thr3 vj)) in
                                                                                                                                                                     (let (outsb) = (stateful_consistent_views_outputs'' x i j (Aux.fst3 vi) (Aux.fst3 vj) (Aux.snd3 vi) (Aux.snd3 vj) (st1 , st2)) in
                                                                                                                                                                      outsb)))
    let stateful_consistent_views_outputs (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                                 (let (outsb) = (stateful_consistent_views_outputs' x i j vi vj) in
                                                                                                                                                  (let (outs1) = (Aux.fst3 (fst outsb)) in
                                                                                                                                                   (let (outs2) = (snd (fst outsb)) in
                                                                                                                                                    (let (b) = (snd outsb) in
                                                                                                                                                     (let (out1) = (stateful_local_protocol_end i x outs1) in
                                                                                                                                                      (let (out2) = (stateful_local_protocol_end j x outs2) in
                                                                                                                                                       (Pervasive._and b (stateful_consistent_outputs x i j out1 out2))))))))
    let rec circ_protocol' (c : (G._Gate) List.list) (ws : (CT.local_input) CT.pmap) (rs : ((G.GT.local_rand) List.list) CT.pmap) : (((CT.msg) List.list) CT.ppmap * (((G.GT.local_rand) List.list) CT.pmap * (CT.local_output) CT.pmap)) =
                                                                                                                                                                                                                                              begin match c with
                                                                                                                                                                                                                                              | (List.Nil) -> ((CT.ppinit (fun (_ : CT.party) (_ : CT.party) -> List.Nil)) , ((CT.pinit (fun (_ : CT.party) -> List.Nil)) , ws))
                                                                                                                                                                                                                                              | (List.Cons (g , c')) -> (let (r) = (CT.P.map (List.head (Pervasive.witness)) rs) in
                                                                                                                                                                                                                                                                         (let (_to) = (G.g_protocol g ws r) in
                                                                                                                                                                                                                                                                          (let (ws') = (snd _to) in
                                                                                                                                                                                                                                                                           (let (r1) = (CT.P.map (fun (x : (G.share * (((G.GT.msg) NextMsgArray.Array.array) G.GT.P.arrayN * G.GT.local_rand))) -> (Aux.thr3 x)) (Aux.fst3 _to)) in
                                                                                                                                                                                                                                                                            (let (outs) = (stateful_protocol_round (Pervasive.mk_int 0) c (CT.P.zip ws rs)) in
                                                                                                                                                                                                                                                                             (let (ins1) = (from_messages (send_messages outs)) in
                                                                                                                                                                                                                                                                              (let (tro) = (circ_protocol' c' ws' (CT.P.map (List.behead) rs)) in
                                                                                                                                                                                                                                                                               ((CT.ppcons ins1 (Aux.fst3 tro)) , ((CT.pcons r1 (Aux.snd3 tro)) , (Aux.thr3 tro))))))))))
                                                                                                                                                                                                                                              end
    let circ_protocol (c : _Circuit) (ws : (CT.local_input) CT.pmap) (rs : (CT.local_rand) CT.pmap) : (((CT.local_input * (((CT.msg) NextMsgArray.Array.array) CT.P.arrayN * (G.GT.local_rand) List.list))) CT.P.arrayN * (CT.local_output) CT.pmap) =
                                                                                                                                                                                                                                                         (let (o) = (circ_protocol' c ws rs) in
                                                                                                                                                                                                                                                          (let (vins) = (CT.P.map (fun (xs : ((CT.msg) List.list) CT.P.arrayN) -> (CT.P.map (CT.rlist (List.size c)) xs)) (Aux.fst3 o)) in
                                                                                                                                                                                                                                                           (let (tr) = (CT.P.zip3 ws vins (Aux.snd3 o)) in
                                                                                                                                                                                                                                                            (tr , (Aux.thr3 o)))))
    let circ_valid_rands (x : (G._Gate) List.list) (cs : (CT.local_rand) G.GT.P.arrayN) : Pervasive.bool =
                                                                                                             (CT.P.all (fun (_ : Pervasive.int) (c : CT.local_rand) -> (circ_valid_rand x c)) cs)
end
module MaurerReveal = struct
    module M = struct
        module ST = struct
            type public_input = MaurerCircuit.ST.public_input
            module P = struct
                let rec size : Pervasive.int =
                                                 (MaurerCircuit.ST.P.size)
                type ('a) arrayN = ('a) MaurerCircuit.ST.P.arrayN
                let rec get : (('a) MaurerCircuit.G.GT.P.arrayN -> (Pervasive.int -> 'a)) =
                                                                                              (MaurerCircuit.ST.P.get)
                let rec set : (('a) MaurerCircuit.G.GT.P.arrayN -> (Pervasive.int -> ('a -> ('a) MaurerCircuit.G.GT.P.arrayN))) =
                                                                                                                                    (MaurerCircuit.ST.P.set)
                let rec init : ((Pervasive.int -> 'a) -> ('a) MaurerCircuit.G.GT.P.arrayN) =
                                                                                               (MaurerCircuit.ST.P.init)
                let rec of_list : (('a) List.list -> ('a) MaurerCircuit.G.GT.P.arrayN) =
                                                                                           (MaurerCircuit.ST.P.of_list)
                let rec to_list : (('a) MaurerCircuit.G.GT.P.arrayN -> ('a) List.list) =
                                                                                           (MaurerCircuit.ST.P.to_list)
                let rec to_assoc : (('a) MaurerCircuit.G.GT.P.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                                              (MaurerCircuit.ST.P.to_assoc)
                let rec create : ('a -> ('a) MaurerCircuit.G.GT.P.arrayN) =
                                                                              (MaurerCircuit.ST.P.create)
                let rec singl : (Pervasive.int -> ('a -> ('a) MaurerCircuit.G.GT.P.arrayN)) =
                                                                                                (MaurerCircuit.ST.P.singl)
                let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) MaurerCircuit.G.GT.P.arrayN -> ('b) MaurerCircuit.G.GT.P.arrayN)) =
                                                                                                                                             (MaurerCircuit.ST.P.imap)
                let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                              (imap (fun (_ : Pervasive.int) -> f) xs)
                let rec merge : (('a -> ('b -> 'c)) -> (('a) MaurerCircuit.G.GT.P.arrayN -> (('b) MaurerCircuit.G.GT.P.arrayN -> ('c) MaurerCircuit.G.GT.P.arrayN))) =
                                                                                                                                                                         (MaurerCircuit.ST.P.merge)
                let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                       (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
                let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) MaurerCircuit.G.GT.P.arrayN -> ('a) MaurerCircuit.G.GT.P.arrayN)) =
                                                                                                                                                           (MaurerCircuit.ST.P.filter)
                let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) MaurerCircuit.G.GT.P.arrayN -> Pervasive.bool)) =
                                                                                                                                      (MaurerCircuit.ST.P.all)
                let rec allsame : (('a) MaurerCircuit.G.GT.P.arrayN -> Pervasive.bool) =
                                                                                           (MaurerCircuit.ST.P.allsame)
                let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                                  (zip xs (zip ys zs))
                let rec concat : ((('b) MaurerCircuit.G.GT.P.arrayN) List.list -> (('b) List.list) MaurerCircuit.G.GT.P.arrayN) =
                                                                                                                                    (MaurerCircuit.ST.P.concat)
            end
            let rec parties : Pervasive.int =
                                                (MaurerCircuit.ST.parties)
            type party = MaurerCircuit.ST.party
            let rec partyset : NextMsgISet.ISet.iset =
                                                         (MaurerCircuit.ST.partyset)
            type round = MaurerCircuit.ST.round
            let rec rounds : ((MaurerCircuit.G._Gate) List.list -> Pervasive.int) =
                                                                                      (MaurerCircuit.ST.rounds)
            let rec roundset : (MaurerCircuit.CT.public_input -> NextMsgISet.ISet.iset) =
                                                                                            (MaurerCircuit.ST.roundset)
            type ('a) pmap = ('a) MaurerCircuit.ST.pmap
            type ('a) rmap = ('a) MaurerCircuit.ST.rmap
            type ('a) prmap = ('a) MaurerCircuit.ST.prmap
            type ('a) ppmap = ('a) MaurerCircuit.ST.ppmap
            type ('a) pprmap = ('a) MaurerCircuit.ST.pprmap
            type local_input = MaurerCircuit.ST.local_input
            type local_output = MaurerCircuit.ST.local_output
            type local_rand = MaurerCircuit.ST.local_rand
            type msg = MaurerCircuit.ST.msg
            type pmsgs = MaurerCircuit.ST.pmsgs
            type rmsgs = MaurerCircuit.ST.rmsgs
            type prmsgs = MaurerCircuit.ST.prmsgs
            type ppmsgs = MaurerCircuit.ST.ppmsgs
            type pprmsgs = MaurerCircuit.ST.pprmsgs
            type in_msgs = MaurerCircuit.ST.in_msgs
            type out_msgs = MaurerCircuit.ST.out_msgs
            type view = MaurerCircuit.ST.view
            type trace = MaurerCircuit.ST.trace
            let rec eq_msg : (MaurerCircuit.G.GT.msg -> (MaurerCircuit.G.GT.msg -> Pervasive.bool)) =
                                                                                                        (MaurerCircuit.ST.eq_msg)
            let rec eq_pmsgs : (MaurerCircuit.CT.pmsgs -> (MaurerCircuit.CT.pmsgs -> Pervasive.bool)) =
                                                                                                          (MaurerCircuit.ST.eq_pmsgs)
            let rec eq_rmsgs : (MaurerCircuit.CT.rmsgs -> (MaurerCircuit.CT.rmsgs -> Pervasive.bool)) =
                                                                                                          (MaurerCircuit.ST.eq_rmsgs)
            let rec pinit : ((MaurerCircuit.CT.party -> 'a) -> ('a) MaurerCircuit.CT.P.arrayN) =
                                                                                                   (MaurerCircuit.ST.pinit)
            let rec ppinit : ((MaurerCircuit.CT.party -> (MaurerCircuit.CT.party -> 'a)) -> (('a) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN) =
                                                                                                                                                            (MaurerCircuit.ST.ppinit)
            let rec prempty : (Pervasive.int -> ('a -> (('a) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                       (MaurerCircuit.ST.prempty)
            let rec pprempty : (Pervasive.int -> ('a -> ((('a) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                    (MaurerCircuit.ST.pprempty)
            let rec ppswap : (('a) MaurerCircuit.CT.ppmap -> (('a) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN) =
                                                                                                                             (MaurerCircuit.ST.ppswap)
            let rec prget : (('a) MaurerCircuit.CT.prmap -> (MaurerCircuit.CT.round -> ('a) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                            (MaurerCircuit.ST.prget)
            let rec pprget : (('a) MaurerCircuit.CT.pprmap -> (MaurerCircuit.CT.round -> (('a) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                          (MaurerCircuit.ST.pprget)
            let rec prset : (('a) MaurerCircuit.CT.prmap -> (Pervasive.int -> (('a) MaurerCircuit.CT.pmap -> (('a) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN))) =
                                                                                                                                                                              (MaurerCircuit.ST.prset)
            let rec prext : (Pervasive.int -> (('a) MaurerCircuit.CT.prmap -> (('a) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                              (MaurerCircuit.ST.prext)
            let rec prextset : (('a) MaurerCircuit.CT.prmap -> (Pervasive.int -> (('a) MaurerCircuit.CT.pmap -> (('a) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN))) =
                                                                                                                                                                                 (MaurerCircuit.ST.prextset)
            let rec pprset : (('a) MaurerCircuit.CT.pprmap -> (MaurerCircuit.CT.round -> (('a) MaurerCircuit.CT.ppmap -> ((('a) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN))) =
                                                                                                                                                                                                                      (MaurerCircuit.ST.pprset)
            let rec prfilter : ((MaurerCircuit.CT.round -> Pervasive.bool) -> (('a) MaurerCircuit.CT.prmap -> (('a) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                                              (MaurerCircuit.ST.prfilter)
            let rec pprfilter : ((MaurerCircuit.CT.round -> Pervasive.bool) -> (('a) MaurerCircuit.CT.pprmap -> ((('a) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                                                                            (MaurerCircuit.ST.pprfilter)
            let rec rdom : (Pervasive.int -> (MaurerCircuit.CT.round -> (('a) MaurerCircuit.CT.rmap -> Pervasive.bool))) =
                                                                                                                             (MaurerCircuit.ST.rdom)
            let rec prdom : (Pervasive.int -> (MaurerCircuit.CT.round -> (('a) MaurerCircuit.CT.prmap -> Pervasive.bool))) =
                                                                                                                               (MaurerCircuit.ST.prdom)
            let rec pprdom : (Pervasive.int -> (MaurerCircuit.CT.round -> (('a) MaurerCircuit.CT.pprmap -> Pervasive.bool))) =
                                                                                                                                 (MaurerCircuit.ST.pprdom)
            let rec rlist : (Pervasive.int -> (('a) List.list -> ('a) NextMsgArray.Array.array)) =
                                                                                                     (MaurerCircuit.ST.rlist)
            let rec prlist : (Pervasive.int -> ((MaurerCircuit.CT.pmsgs) List.list -> (MaurerCircuit.CT.msg) MaurerCircuit.CT.prmap)) =
                                                                                                                                          (MaurerCircuit.ST.prlist)
            let rec pcons : (('a) MaurerCircuit.CT.pmap -> ((('a) List.list) MaurerCircuit.CT.pmap -> (('a) List.list) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                       (MaurerCircuit.ST.pcons)
            let rec phead : ((('a) List.list) MaurerCircuit.CT.pmap -> ('a) MaurerCircuit.CT.P.arrayN) =
                                                                                                           (MaurerCircuit.ST.phead)
            let rec pbehead : ((('a) List.list) MaurerCircuit.CT.pmap -> (('a) List.list) MaurerCircuit.CT.P.arrayN) =
                                                                                                                         (MaurerCircuit.ST.pbehead)
            let rec prcons : ((('a) List.list) MaurerCircuit.CT.pmap -> (('a) MaurerCircuit.CT.pmap -> (('a) List.list) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                        (MaurerCircuit.ST.prcons)
            let rec pcat : ((('a) List.list) MaurerCircuit.CT.pmap -> ((('a) List.list) MaurerCircuit.CT.pmap -> (('a) List.list) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                                  (MaurerCircuit.ST.pcat)
            let rec ppcons : (('a) MaurerCircuit.CT.ppmap -> ((('a) List.list) MaurerCircuit.CT.ppmap -> ((('a) List.list) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                                                      (MaurerCircuit.ST.ppcons)
            let rec pprcons : ((('a) List.list) MaurerCircuit.CT.ppmap -> (('a) MaurerCircuit.CT.ppmap -> ((('a) List.list) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                                                       (MaurerCircuit.ST.pprcons)
            let rec ppcat : ((('a) List.list) MaurerCircuit.CT.ppmap -> ((('a) List.list) MaurerCircuit.CT.ppmap -> ((('a) List.list) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                                                                 (MaurerCircuit.ST.ppcat)
            let rec prmsgs_up_to : (MaurerCircuit.CT.round -> (MaurerCircuit.CT.prmsgs -> ((MaurerCircuit.CT.msg) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                                            (MaurerCircuit.ST.prmsgs_up_to)
            let rec pprmsgs_up_to : (MaurerCircuit.CT.round -> (MaurerCircuit.CT.pprmsgs -> (((MaurerCircuit.CT.msg) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                                                                          (MaurerCircuit.ST.pprmsgs_up_to)
            let rec get_trace_inputs : (MaurerCircuit.CT.trace -> (MaurerCircuit.CT.local_input) MaurerCircuit.CT.P.arrayN) =
                                                                                                                                (MaurerCircuit.ST.get_trace_inputs)
            let rec get_trace_in_msgs : (MaurerCircuit.CT.trace -> (MaurerCircuit.CT.in_msgs) MaurerCircuit.CT.P.arrayN) =
                                                                                                                             (MaurerCircuit.ST.get_trace_in_msgs)
            let rec get_trace_rands : (MaurerCircuit.CT.trace -> (MaurerCircuit.CT.local_rand) MaurerCircuit.CT.P.arrayN) =
                                                                                                                              (MaurerCircuit.ST.get_trace_rands)
            let rec get_view : (MaurerCircuit.CT.party -> (MaurerCircuit.CT.trace -> MaurerCircuit.CT.view)) =
                                                                                                                 (MaurerCircuit.ST.get_view)
            let rec get_trace_in_msgs_round : (MaurerCircuit.CT.round -> (MaurerCircuit.CT.trace -> ((MaurerCircuit.CT.msg) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                                                       (MaurerCircuit.ST.get_trace_in_msgs_round)
            let rec get_view_in_msgs_round : (MaurerCircuit.CT.round -> (MaurerCircuit.CT.view -> (MaurerCircuit.CT.msg) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                         (MaurerCircuit.ST.get_view_in_msgs_round)
            let rec add_view_in_msgs : (MaurerCircuit.CT.round -> (MaurerCircuit.CT.pmsgs -> (MaurerCircuit.CT.view -> (MaurerCircuit.CT.local_input * (((MaurerCircuit.CT.msg) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN * MaurerCircuit.CT.local_rand))))) =
                                                                                                                                                                                                                                                                           (MaurerCircuit.ST.add_view_in_msgs)
            let rec get_trace_in_msgs_up_to : (MaurerCircuit.CT.round -> (MaurerCircuit.CT.trace -> (((MaurerCircuit.CT.msg) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN) MaurerCircuit.CT.P.arrayN)) =
                                                                                                                                                                                                                  (MaurerCircuit.ST.get_trace_in_msgs_up_to)
            let rec add_trace_in_msgs : (MaurerCircuit.CT.round -> (MaurerCircuit.CT.ppmsgs -> (MaurerCircuit.CT.trace -> ((MaurerCircuit.CT.local_input * (((MaurerCircuit.CT.msg) NextMsgArray.Array.array) MaurerCircuit.CT.P.arrayN * MaurerCircuit.CT.local_rand))) MaurerCircuit.CT.P.arrayN))) =
                                                                                                                                                                                                                                                                                                          (MaurerCircuit.ST.add_trace_in_msgs)
            let rec valid_trace : (MaurerCircuit.CT.public_input -> (MaurerCircuit.CT.trace -> Pervasive.bool)) =
                                                                                                                    (MaurerCircuit.ST.valid_trace)
            let rec valid_view : (MaurerCircuit.CT.public_input -> (MaurerCircuit.CT.view -> Pervasive.bool)) =
                                                                                                                  (MaurerCircuit.ST.valid_view)
        end
        type local_messages = MaurerCircuit.local_messages
        type messages = MaurerCircuit.messages
        type local_out_messages = MaurerCircuit.local_out_messages
        type local_in_messages = MaurerCircuit.local_in_messages
        type out_messages = MaurerCircuit.out_messages
        type in_messages = MaurerCircuit.in_messages
        let rec from_local_messages : (MaurerCircuit.G.local_messages -> MaurerCircuit.G.ST.pmsgs) =
                                                                                                       (MaurerCircuit.from_local_messages)
        let rec to_local_messages : (MaurerCircuit.G.ST.pmsgs -> MaurerCircuit.G.local_messages) =
                                                                                                     (MaurerCircuit.to_local_messages)
        let rec send_messages : (MaurerCircuit.G.out_messages -> MaurerCircuit.G.in_messages) =
                                                                                                  (MaurerCircuit.send_messages)
        let rec from_messages : ((MaurerCircuit.local_messages) MaurerCircuit.ST.P.arrayN -> (MaurerCircuit.ST.pmsgs) MaurerCircuit.ST.P.arrayN) =
                                                                                                                                                     (MaurerCircuit.from_messages)
        let rec to_messages : ((MaurerCircuit.ST.pmsgs) MaurerCircuit.ST.P.arrayN -> (MaurerCircuit.local_messages) MaurerCircuit.ST.P.arrayN) =
                                                                                                                                                   (MaurerCircuit.to_messages)
        let rec valid_local_messages : ((MaurerCircuit.G.ST.public_input) List.list -> (Pervasive.int -> (MaurerCircuit.G.local_messages -> Pervasive.bool))) =
                                                                                                                                                                  (MaurerCircuit.valid_local_messages)
        let rec valid_messages : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.round -> (MaurerCircuit.messages -> Pervasive.bool))) =
                                                                                                                                               (MaurerCircuit.valid_messages)
        let rec valid_msg : ((MaurerCircuit.G.ST.public_input) List.list -> (Pervasive.int -> (MaurerCircuit.G.ST.msg -> Pervasive.bool))) =
                                                                                                                                               (MaurerCircuit.valid_msg)
        let rec valid_pmsgs : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.round -> (MaurerCircuit.ST.pmsgs -> Pervasive.bool))) =
                                                                                                                                            (MaurerCircuit.valid_pmsgs)
        let rec valid_ppmsgs : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.round -> (MaurerCircuit.ST.ppmsgs -> Pervasive.bool))) =
                                                                                                                                              (MaurerCircuit.valid_ppmsgs)
        type local_state = MaurerCircuit.local_state
        let rec init_local_state : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.CT.local_input -> (MaurerCircuit.ST.local_rand -> (MaurerCircuit.CT.local_input * MaurerCircuit.ST.local_rand))))) =
                                                                                                                                                                                                                                      (MaurerCircuit.init_local_state)
        let rec update_local_state : (MaurerCircuit.G.GT.party -> (MaurerCircuit.CT.round -> (MaurerCircuit.CT.public_input -> (MaurerCircuit.CT.local_input -> (MaurerCircuit.local_in_messages -> ((MaurerCircuit.G.share * MaurerCircuit.CT.local_rand) -> (MaurerCircuit.G.share * (MaurerCircuit.G.GT.local_rand) List.list))))))) =
                                                                                                                                                                                                                                                                                                                                            (MaurerCircuit.update_local_state)
        let rec get_local_state : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.round -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.ST.local_rand -> (MaurerCircuit.ST.in_msgs -> MaurerCircuit.local_state)))))) =
                                                                                                                                                                                                                                                            (MaurerCircuit.get_local_state)
        type state = MaurerCircuit.state
        let rec init_state : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> (MaurerCircuit.local_state) MaurerCircuit.ST.P.arrayN))) =
                                                                                                                                                                                                                                             (MaurerCircuit.init_state)
        let rec update_state : (MaurerCircuit.ST.round -> (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.local_in_messages) MaurerCircuit.ST.pmap -> (MaurerCircuit.state -> (MaurerCircuit.local_state) MaurerCircuit.ST.P.arrayN))))) =
                                                                                                                                                                                                                                                                                                        (MaurerCircuit.update_state)
        let rec get_state : (MaurerCircuit.ST.round -> (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap -> (MaurerCircuit.local_state) MaurerCircuit.ST.P.arrayN))))) =
                                                                                                                                                                                                                                                                                                                              (MaurerCircuit.get_state)
        let rec stateful_local_protocol_round : (MaurerCircuit.G.GT.party -> (MaurerCircuit.CT.round -> (MaurerCircuit.CT.public_input -> ((MaurerCircuit.G.share * MaurerCircuit.CT.local_rand) -> MaurerCircuit.G.local_out_msgs)))) =
                                                                                                                                                                                                                                           (MaurerCircuit.stateful_local_protocol_round)
        let rec stateful_local_protocol_end : (MaurerCircuit.CT.party -> (MaurerCircuit.CT.public_input -> ((MaurerCircuit.G.share * MaurerCircuit.CT.local_rand) -> MaurerCircuit.G.share))) =
                                                                                                                                                                                                  (MaurerCircuit.stateful_local_protocol_end)
        let rec stateful_local_protocol''' : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.local_state -> (MaurerCircuit.ST.in_msgs -> (Pervasive.int -> ((MaurerCircuit.ST.round) List.list -> (MaurerCircuit.local_state * MaurerCircuit.ST.out_msgs)))))))) =
                                                                                                                                                                                                                                                                                                                                  (MaurerCircuit.stateful_local_protocol''')
        let rec stateful_local_protocol'' : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.local_state -> (MaurerCircuit.ST.in_msgs -> (Pervasive.int -> (MaurerCircuit.ST.round -> (MaurerCircuit.local_state * MaurerCircuit.ST.out_msgs)))))))) =
                                                                                                                                                                                                                                                                                                                     (MaurerCircuit.stateful_local_protocol'')
        let rec stateful_local_protocol' : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.local_state -> (MaurerCircuit.ST.in_msgs -> (MaurerCircuit.local_state * MaurerCircuit.ST.out_msgs)))))) =
                                                                                                                                                                                                                                                                     (MaurerCircuit.stateful_local_protocol')
        let rec stateful_local_protocol : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.view -> (MaurerCircuit.ST.out_msgs * MaurerCircuit.ST.local_output)))) =
                                                                                                                                                                                                    (MaurerCircuit.stateful_local_protocol)
        let rec stateful_protocol_round : (MaurerCircuit.ST.round -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.state -> (MaurerCircuit.local_out_messages) MaurerCircuit.ST.P.arrayN))) =
                                                                                                                                                                                                   (MaurerCircuit.stateful_protocol_round)
        let rec stateful_protocol_end : (MaurerCircuit.ST.public_input -> (MaurerCircuit.state -> (MaurerCircuit.ST.local_output) MaurerCircuit.ST.P.arrayN)) =
                                                                                                                                                                  (MaurerCircuit.stateful_protocol_end)
        let rec stateful_protocol''' : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap -> (MaurerCircuit.state -> ((MaurerCircuit.ST.round) List.list -> ((MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap * MaurerCircuit.state)))))) =
                                                                                                                                                                                                                                                                                                                                        (MaurerCircuit.stateful_protocol''')
        let rec stateful_protocol'' : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap -> (MaurerCircuit.state -> (MaurerCircuit.ST.round -> ((MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap * MaurerCircuit.state)))))) =
                                                                                                                                                                                                                                                                                                                           (MaurerCircuit.stateful_protocol'')
        let rec stateful_protocol' : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap * MaurerCircuit.state)))) =
                                                                                                                                                                                                                                                                        (MaurerCircuit.stateful_protocol')
        let rec stateful_protocol : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> (((MaurerCircuit.ST.local_input * (MaurerCircuit.ST.in_msgs * MaurerCircuit.ST.local_rand))) MaurerCircuit.ST.P.arrayN * (MaurerCircuit.ST.local_output) MaurerCircuit.ST.P.arrayN)))) =
                                                                                                                                                                                                                                                                                                                                                                                  (MaurerCircuit.stateful_protocol)
        let rec stateful_protocol_sz' : (Pervasive.int -> (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap * MaurerCircuit.state))))) =
                                                                                                                                                                                                                                                                                              (MaurerCircuit.stateful_protocol_sz')
        let rec stateful_protocol_sz : (Pervasive.int -> (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> (((MaurerCircuit.ST.local_input * (MaurerCircuit.ST.in_msgs * MaurerCircuit.ST.local_rand))) MaurerCircuit.ST.P.arrayN * (MaurerCircuit.ST.local_output) MaurerCircuit.ST.P.arrayN))))) =
                                                                                                                                                                                                                                                                                                                                                                                                        (MaurerCircuit.stateful_protocol_sz)
        let rec local_protocol_round : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.round -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.ST.local_rand -> (MaurerCircuit.ST.in_msgs -> MaurerCircuit.ST.pmsgs)))))) =
                                                                                                                                                                                                                                                              (MaurerCircuit.local_protocol_round)
        let rec local_protocol_end : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.ST.local_rand -> (MaurerCircuit.ST.in_msgs -> MaurerCircuit.ST.local_output))))) =
                                                                                                                                                                                                                                       (MaurerCircuit.local_protocol_end)
        let rec local_protocol'' : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.ST.local_rand -> (MaurerCircuit.ST.in_msgs -> (Pervasive.int -> (MaurerCircuit.ST.round -> MaurerCircuit.ST.out_msgs))))))) =
                                                                                                                                                                                                                                                                                (MaurerCircuit.local_protocol'')
        let rec local_protocol' : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.view -> MaurerCircuit.ST.out_msgs))) =
                                                                                                                                                          (MaurerCircuit.local_protocol')
        let rec local_protocol : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.view -> (MaurerCircuit.ST.out_msgs * MaurerCircuit.ST.local_output)))) =
                                                                                                                                                                                           (MaurerCircuit.local_protocol)
        let rec protocol_round : (MaurerCircuit.ST.round -> (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap -> (MaurerCircuit.ST.pmsgs) MaurerCircuit.ST.P.arrayN))))) =
                                                                                                                                                                                                                                                                                                                                (MaurerCircuit.protocol_round)
        let rec protocol_end : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap -> (MaurerCircuit.ST.local_output) MaurerCircuit.ST.P.arrayN)))) =
                                                                                                                                                                                                                                                                                                         (MaurerCircuit.protocol_end)
        let rec protocol''' : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap -> (MaurerCircuit.ST.round -> (MaurerCircuit.ST.round -> (MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap)))))) =
                                                                                                                                                                                                                                                                                                                                                       (MaurerCircuit.protocol''')
        let rec protocol'' : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap -> (MaurerCircuit.ST.round -> (MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap))))) =
                                                                                                                                                                                                                                                                                                                          (MaurerCircuit.protocol'')
        let rec protocol' : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> (MaurerCircuit.ST.in_msgs) MaurerCircuit.ST.pmap))) =
                                                                                                                                                                                                                                       (MaurerCircuit.protocol')
        let rec protocol : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> (((MaurerCircuit.ST.local_input * (MaurerCircuit.ST.in_msgs * MaurerCircuit.ST.local_rand))) MaurerCircuit.ST.P.arrayN * (MaurerCircuit.ST.local_output) MaurerCircuit.ST.P.arrayN)))) =
                                                                                                                                                                                                                                                                                                                                                                         (MaurerCircuit.protocol)
        let rec get_view_in_msgs : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.view -> MaurerCircuit.ST.rmsgs)) =
                                                                                                                     (MaurerCircuit.get_view_in_msgs)
        let rec get_view_out_msgs : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.view -> MaurerCircuit.ST.rmsgs)))) =
                                                                                                                                                                                     (MaurerCircuit.get_view_out_msgs)
        let rec consistent_inputs : (MaurerCircuit.circuit -> (NextMsgMaurerAPI.MaurerAPI.pid -> (NextMsgMaurerAPI.MaurerAPI.pid -> ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) -> ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) -> Pervasive.bool))))) =
                                                                                                                                                                                                                                                                                                                      (MaurerCircuit.consistent_inputs)
        let rec consistent_rands : ((MaurerCircuit.G._Gate) List.list -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.party -> (MaurerCircuit.CT.local_rand -> (MaurerCircuit.CT.local_rand -> Pervasive.bool))))) =
                                                                                                                                                                                                                       (MaurerCircuit.consistent_rands)
        let rec valid_inputs : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_input) MaurerCircuit.ST.pmap -> Pervasive.bool)) =
                                                                                                                                               (MaurerCircuit.valid_inputs)
        let rec valid_rands : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.local_rand) MaurerCircuit.ST.pmap -> Pervasive.bool)) =
                                                                                                                                             (MaurerCircuit.valid_rands)
        let rec consistent_views : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.view -> (MaurerCircuit.ST.view -> Pervasive.bool))))) =
                                                                                                                                                                                                       (MaurerCircuit.consistent_views)
        let rec consistent_trace : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.trace -> Pervasive.bool)) =
                                                                                                                     (MaurerCircuit.consistent_trace)
        let rec pairwise_consistent_views : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.view -> (MaurerCircuit.ST.view -> Pervasive.bool))))) =
                                                                                                                                                                                                                (MaurerCircuit.pairwise_consistent_views)
        let rec pairwise_consistent_trace : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.trace -> Pervasive.bool)) =
                                                                                                                              (MaurerCircuit.pairwise_consistent_trace)
        let rec view_output : (MaurerCircuit.ST.party -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.view -> MaurerCircuit.ST.local_output))) =
                                                                                                                                                          (MaurerCircuit.view_output)
        let rec view_outputs : (MaurerCircuit.ST.public_input -> ((MaurerCircuit.ST.view) MaurerCircuit.ST.pmap -> (MaurerCircuit.ST.local_output) MaurerCircuit.ST.P.arrayN)) =
                                                                                                                                                                                   (MaurerCircuit.view_outputs)
        let rec stateful_consistent_outputs : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.local_output -> (MaurerCircuit.ST.local_output -> Pervasive.bool))))) =
                                                                                                                                                                                                                                  (MaurerCircuit.stateful_consistent_outputs)
        type local_state2 = MaurerCircuit.local_state2
        let rec stateful_consistent_views_outputs_round : (MaurerCircuit.ST.round -> (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.ST.in_msgs -> (MaurerCircuit.ST.in_msgs -> (MaurerCircuit.local_state2 -> ((MaurerCircuit.local_state * MaurerCircuit.local_state) * Pervasive.bool)))))))))) =
                                                                                                                                                                                                                                                                                                                                                                                                                                (MaurerCircuit.stateful_consistent_views_outputs_round)
        let rec stateful_consistent_views_outputs''' : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.ST.in_msgs -> (MaurerCircuit.ST.in_msgs -> (MaurerCircuit.local_state2 -> ((MaurerCircuit.ST.round) List.list -> (MaurerCircuit.local_state2 * Pervasive.bool)))))))))) =
                                                                                                                                                                                                                                                                                                                                                                                                            (MaurerCircuit.stateful_consistent_views_outputs''')
        let rec stateful_consistent_views_outputs'' : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.ST.local_input -> (MaurerCircuit.ST.in_msgs -> (MaurerCircuit.ST.in_msgs -> (MaurerCircuit.local_state2 -> (MaurerCircuit.local_state2 * Pervasive.bool))))))))) =
                                                                                                                                                                                                                                                                                                                                                                   (MaurerCircuit.stateful_consistent_views_outputs'')
        let rec stateful_consistent_views_outputs' : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.view -> (MaurerCircuit.ST.view -> (MaurerCircuit.local_state2 * Pervasive.bool)))))) =
                                                                                                                                                                                                                                                        (MaurerCircuit.stateful_consistent_views_outputs')
        let rec stateful_consistent_views_outputs : (MaurerCircuit.ST.public_input -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.party -> (MaurerCircuit.ST.view -> (MaurerCircuit.ST.view -> Pervasive.bool))))) =
                                                                                                                                                                                                                        (MaurerCircuit.stateful_consistent_views_outputs)
    end
    type pub_input = MaurerCircuit.circuit
    let pub_input_conv (x : pub_input) : pub_input =
                                                       x
    type final_output = NextMsgMaurerAPI.MaurerAPI._val
    let weak_rounds (x : pub_input) : Pervasive.int =
                                                        (M.ST.rounds (pub_input_conv x))
    let reveal_local_start (_ : pub_input) (ws : MaurerGate.share) : (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either =
                                                                                                                                      (Aux.R (NextMsgMaurerAPI.MaurerAPI.output_start (Int.minus (NextMsgMaurerAPI.MaurerAPI.get_wire_st_next (fst ws)) (Pervasive.mk_int 1)) (fst ws)))
    let reveal_local_end (_ : pub_input) (ins : MaurerGate.local_msgs) : NextMsgMaurerAPI.MaurerAPI._val =
                                                                                                             (NextMsgMaurerAPI.MaurerAPI.output_end (Aux.unR ins))
    let mpc_local_protocol_round (i : M.ST.party) (r : Pervasive.int) (x : pub_input) (st : (M.local_state, M.local_out_messages) Aux.either) : M.local_out_messages =
                                                                                                                                                                         if (Int.lt r (weak_rounds x)) then (M.stateful_local_protocol_round i r (pub_input_conv x) (Aux.unL st)) else (reveal_local_start x (M.stateful_local_protocol_end i (pub_input_conv x) (Aux.unL st)))
    let mpc_update_local_state (i : M.ST.party) (r : Pervasive.int) (x : pub_input) (wi : M.ST.local_input) (ins : M.local_in_messages) (st : (M.local_state, M.local_out_messages) Aux.either) : (M.local_state, M.local_in_messages) Aux.either =
                                                                                                                                                                                                                                                      if (Int.lt r (weak_rounds x)) then (Aux.L (M.update_local_state i r (pub_input_conv x) wi ins (Aux.unL st))) else (Aux.R ins)
    let mpc_local_protocol_end (_ : M.ST.party) (x : pub_input) (st : (M.local_state, M.local_out_messages) Aux.either) : final_output =
                                                                                                                                           (reveal_local_end x (Aux.unR st))
    let mpc_consistent_inputs : (MaurerCircuit.circuit -> (NextMsgMaurerAPI.MaurerAPI.pid -> (NextMsgMaurerAPI.MaurerAPI.pid -> ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) -> ((NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st) -> Pervasive.bool))))) =
                                                                                                                                                                                                                                                                                                                  (MaurerCircuit.consistent_inputs)
    let mpc_consistent_outputs (x : MaurerCircuit.circuit) (i : NextMsgMaurerAPI.MaurerAPI.pid) (j : NextMsgMaurerAPI.MaurerAPI.pid) (wi : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) (wj : (NextMsgMaurerAPI.MaurerAPI.wire_st * NextMsgMaurerAPI.MaurerAPI.pub_st)) : Pervasive.bool =
                                                                                                                                                                                                                                                                                                                          (Pervasive._and (MaurerCircuit.valid_circuit x (Int.minus (NextMsgMaurerAPI.MaurerAPI.get_wire_st_next (fst wi)) (List.size x)) (NextMsgISet.ISet.intersect (snd wi) (NextMsgISet.ISet.iset (Int.minus (NextMsgMaurerAPI.MaurerAPI.get_wire_st_next (fst wi)) (List.size x))))) (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.g_valid_share wi) (Pervasive._and (NextMsgMaurerAPI.MaurerAPI.g_valid_share wj) (NextMsgMaurerAPI.MaurerAPI.consistent_shares i j wi wj))))
    let final_valid_local_messages (_ : pub_input) (xs : (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msgs) Aux.either) : Pervasive.bool =
                                                                                                                                            (Aux.isR xs)
    let final_valid_msg (_ : pub_input) (xs : (Pervasive.unit, NextMsgMaurerAPI.MaurerAPI.msg) Aux.either) : Pervasive.bool =
                                                                                                                                (Aux.isR xs)
    module ST = struct
        type public_input = pub_input
        module P = struct
            let rec size : Pervasive.int =
                                             (M.ST.P.size)
            type ('a) arrayN = ('a) M.ST.P.arrayN
            let rec get : (('a) M.ST.P.arrayN -> (Pervasive.int -> 'a)) =
                                                                            (M.ST.P.get)
            let rec set : (('a) M.ST.P.arrayN -> (Pervasive.int -> ('a -> ('a) M.ST.P.arrayN))) =
                                                                                                    (M.ST.P.set)
            let rec init : ((Pervasive.int -> 'a) -> ('a) M.ST.P.arrayN) =
                                                                             (M.ST.P.init)
            let rec of_list : (('a) List.list -> ('a) M.ST.P.arrayN) =
                                                                         (M.ST.P.of_list)
            let rec to_list : (('a) M.ST.P.arrayN -> ('a) List.list) =
                                                                         (M.ST.P.to_list)
            let rec to_assoc : (('a) M.ST.P.arrayN -> ((Pervasive.int * 'a)) List.list) =
                                                                                            (M.ST.P.to_assoc)
            let rec create : ('a -> ('a) M.ST.P.arrayN) =
                                                            (M.ST.P.create)
            let rec singl : (Pervasive.int -> ('a -> ('a) M.ST.P.arrayN)) =
                                                                              (M.ST.P.singl)
            let rec imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) M.ST.P.arrayN -> ('b) M.ST.P.arrayN)) =
                                                                                                             (M.ST.P.imap)
            let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                          (imap (fun (_ : Pervasive.int) -> f) xs)
            let rec merge : (('a -> ('b -> 'c)) -> (('a) M.ST.P.arrayN -> (('b) M.ST.P.arrayN -> ('c) M.ST.P.arrayN))) =
                                                                                                                           (M.ST.P.merge)
            let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                                   (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
            let rec filter : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) M.ST.P.arrayN -> ('a) M.ST.P.arrayN)) =
                                                                                                                           (M.ST.P.filter)
            let rec all : ((Pervasive.int -> ('a -> Pervasive.bool)) -> (('a) M.ST.P.arrayN -> Pervasive.bool)) =
                                                                                                                    (M.ST.P.all)
            let rec allsame : (('a) M.ST.P.arrayN -> Pervasive.bool) =
                                                                         (M.ST.P.allsame)
            let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                              (zip xs (zip ys zs))
            let rec concat : ((('b) M.ST.P.arrayN) List.list -> (('b) List.list) M.ST.P.arrayN) =
                                                                                                    (M.ST.P.concat)
        end
        let parties : Pervasive.int =
                                        (P.size)
        type party = Pervasive.int
        let partyset : NextMsgISet.ISet.iset =
                                                 (NextMsgISet.ISet.iset (parties))
        type round = Pervasive.int
        let rec rounds (x : pub_input) : Pervasive.int =
                                                           (Int.plus (M.ST.rounds (pub_input_conv x)) (Pervasive.mk_int 1))
        let roundset (p : public_input) : NextMsgISet.ISet.iset =
                                                                    (NextMsgISet.ISet.iset (rounds p))
        type ('a) pmap = ('a) P.arrayN
        type ('a) rmap = ('a) NextMsgArray.Array.array
        type ('a) prmap = (('a) rmap) pmap
        type ('a) ppmap = (('a) pmap) pmap
        type ('a) pprmap = (('a) rmap) ppmap
        type local_input = M.ST.local_input
        type local_output = final_output
        type local_rand = M.ST.local_rand
        type msg = M.ST.msg
        type pmsgs = (msg) pmap
        type rmsgs = (msg) rmap
        type prmsgs = (rmsgs) pmap
        type ppmsgs = (pmsgs) pmap
        type pprmsgs = (prmsgs) pmap
        type in_msgs = prmsgs
        type out_msgs = prmsgs
        type view = (local_input * (in_msgs * local_rand))
        type trace = (view) pmap
        let rec eq_msg : (M.ST.msg -> (M.ST.msg -> Pervasive.bool)) =
                                                                        (M.ST.eq_msg)
        let eq_pmsgs (m1 : pmsgs) (m2 : pmsgs) : Pervasive.bool =
                                                                    (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (P.get m1 i) (P.get m2 i))) (P.size))
        let eq_rmsgs (m1 : rmsgs) (m2 : rmsgs) : Pervasive.bool =
                                                                    (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size m1) (NextMsgArray.Array.size m2)) (AuxList.all_iseq (fun (i : Pervasive.int) -> (eq_msg (NextMsgArray.Array.get m1 i) (NextMsgArray.Array.get m2 i))) (NextMsgArray.Array.size m1)))
        let pinit (f : (party -> 'a)) : ('a) P.arrayN =
                                                          (P.init f)
        let ppinit (f : (party -> (party -> 'a))) : (('a) P.arrayN) P.arrayN =
                                                                                 (pinit (fun (i : party) -> (pinit (f i))))
        let prempty (sz : Pervasive.int) (v : 'a) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                 (pinit (fun (_ : party) -> (NextMsgArray.Array.create sz v)))
        let pprempty (sz : Pervasive.int) (v : 'a) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                             (ppinit (fun (_ : party) (_ : party) -> (NextMsgArray.Array.create sz v)))
        let ppswap (m : ('a) ppmap) : (('a) P.arrayN) P.arrayN =
                                                                   (ppinit (fun (j : Pervasive.int) (i : Pervasive.int) -> (P.get (P.get m i) j)))
        let prget (xs : ('a) prmap) (r : round) : ('a) P.arrayN =
                                                                    (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.get (P.get xs i) r)))
        let pprget (xs : ('a) pprmap) (r : round) : (('a) P.arrayN) P.arrayN =
                                                                                 (ppinit (fun (i : Pervasive.int) (j : Pervasive.int) -> (NextMsgArray.Array.get (P.get (P.get xs i) j) r)))
        let prset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.merge (fun (x0 : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set x0 n y)) xs x)
        let prext (sz : Pervasive.int) (xs : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (pinit (fun (i : Pervasive.int) -> (NextMsgArray.Array.init sz (fun (j : Pervasive.int) -> if (Pervasive._and (Int.le (Pervasive.mk_int 0) j) (Int.lt j (NextMsgArray.Array.size (P.get xs i)))) then (NextMsgArray.Array.get (P.get xs i) j) else (Pervasive.witness)))))
        let prextset (xs : ('a) prmap) (n : Pervasive.int) (x : ('a) pmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                          (prset (prext (Int.plus n (Pervasive.mk_int 1)) xs) n x)
        let pprset (xs : ('a) pprmap) (n : round) (x : ('a) ppmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                             (P.merge (P.merge (fun (ys : ('a) NextMsgArray.Array.array) (y : 'a) -> (NextMsgArray.Array.set ys n y))) xs x)
        let prfilter (p : (round -> Pervasive.bool)) (ins : ('a) prmap) : (('a) NextMsgArray.Array.array) P.arrayN =
                                                                                                                       (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) ins)
        let pprfilter (p : (round -> Pervasive.bool)) (ins : ('a) pprmap) : ((('a) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                                    (P.map (fun (xs : (('a) NextMsgArray.Array.array) P.arrayN) -> (P.map (NextMsgArray.Array.filter (fun (r : round) (_ : 'a) -> (p r))) xs)) ins)
        let rdom (sz : Pervasive.int) (round : round) (xs : ('a) rmap) : Pervasive.bool =
                                                                                            (Pervasive._and (Pervasive.eq (NextMsgArray.Array.size xs) sz) (Pervasive.witness))
        let prdom (sz : Pervasive.int) (round : round) (xs : ('a) prmap) : Pervasive.bool =
                                                                                              (P.all (fun (_ : Pervasive.int) -> (rdom sz round)) xs)
        let pprdom (sz : Pervasive.int) (round : round) (xs : ('a) pprmap) : Pervasive.bool =
                                                                                                (P.all (fun (_ : Pervasive.int) -> (prdom sz round)) xs)
        let rlist (sz : Pervasive.int) (xs : ('a) List.list) : ('a) NextMsgArray.Array.array =
                                                                                                 (List.foldl (fun (rs : ('a) NextMsgArray.Array.array) (i : Pervasive.int) -> (NextMsgArray.Array.set rs i (List.nth (Pervasive.witness) xs i))) (NextMsgArray.Array.create sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let prlist (sz : Pervasive.int) (xs : (pmsgs) List.list) : (msg) prmap =
                                                                                   (List.foldl (fun (rs : (msg) prmap) (i : Pervasive.int) -> (prset rs i (List.nth (Pervasive.witness) xs i))) (prempty sz (Pervasive.witness)) (AuxList.iseq (List.size xs)))
        let pcons (x : ('a) pmap) (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                               (P.merge (fun (x0 : 'a) (xs0 : ('a) List.list) -> (AuxList.cons x0 xs0)) x xs)
        let phead (xs : (('a) List.list) pmap) : ('a) P.arrayN =
                                                                   (P.map (List.head (Pervasive.witness)) xs)
        let pbehead (xs : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                 (P.map (List.behead) xs)
        let prcons (xs : (('a) List.list) pmap) (x : ('a) pmap) : (('a) List.list) P.arrayN =
                                                                                                (P.merge (List.rcons) xs x)
        let pcat (xs : (('a) List.list) pmap) (ys : (('a) List.list) pmap) : (('a) List.list) P.arrayN =
                                                                                                           (P.merge (fun (x : ('a) List.list) (y : ('a) List.list) -> (AuxList.cat x y)) xs ys)
        let ppcons (x : ('a) ppmap) (xs : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                             (P.merge (pcons) x xs)
        let pprcons (xs : (('a) List.list) ppmap) (x : ('a) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                              (P.merge (prcons) xs x)
        let ppcat (xs : (('a) List.list) ppmap) (ys : (('a) List.list) ppmap) : ((('a) List.list) P.arrayN) P.arrayN =
                                                                                                                         (P.merge (pcat) xs ys)
        let prmsgs_up_to (round : round) (ins : prmsgs) : ((msg) NextMsgArray.Array.array) P.arrayN =
                                                                                                        (prfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let pprmsgs_up_to (round : round) (ins : pprmsgs) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                     (pprfilter (Logic.transpose (NextMsgISet.ISet.mem) (NextMsgISet.ISet.iset round)) ins)
        let get_trace_inputs (tr : trace) : (local_input) P.arrayN =
                                                                       (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.fst3 x)) tr)
        let get_trace_in_msgs (tr : trace) : (in_msgs) P.arrayN =
                                                                    (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.snd3 x)) tr)
        let get_trace_rands (tr : trace) : (local_rand) P.arrayN =
                                                                     (P.map (fun (x : (local_input * (in_msgs * local_rand))) -> (Aux.thr3 x)) tr)
        let get_view (i : party) (tr : trace) : view =
                                                         (P.get tr i)
        let get_trace_in_msgs_round (round : round) (tr : trace) : ((msg) P.arrayN) P.arrayN =
                                                                                                 (pprget (get_trace_in_msgs tr) round)
        let get_view_in_msgs_round (round : round) (v : view) : (msg) P.arrayN =
                                                                                   (prget (Aux.snd3 v) round)
        let add_view_in_msgs (r : round) (ins : pmsgs) (v : view) : (local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand)) =
                                                                                                                                                 ((Aux.fst3 v) , ((prset (Aux.snd3 v) r ins) , (Aux.thr3 v)))
        let get_trace_in_msgs_up_to (round : round) (tr : trace) : (((msg) NextMsgArray.Array.array) P.arrayN) P.arrayN =
                                                                                                                            (pprmsgs_up_to round (get_trace_in_msgs tr))
        let add_trace_in_msgs (r : round) (ins : ppmsgs) (tr : trace) : ((local_input * (((msg) NextMsgArray.Array.array) P.arrayN * local_rand))) P.arrayN =
                                                                                                                                                                (P.map (fun (ins_v : (pmsgs * view)) -> (add_view_in_msgs r (Aux.fst3 ins_v) (snd ins_v))) (P.zip ins tr))
        let valid_trace (x : public_input) (tr : trace) : Pervasive.bool =
                                                                             (pprdom (rounds x) (rounds x) (get_trace_in_msgs tr))
        let valid_view (x : public_input) (v : view) : Pervasive.bool =
                                                                          (prdom (rounds x) (rounds x) (Aux.snd3 v))
    end
    type local_messages = M.local_messages
    type messages = (local_messages) ST.pmap
    type local_out_messages = local_messages
    type local_in_messages = local_messages
    type out_messages = messages
    type in_messages = messages
    let rec from_local_messages : (M.local_messages -> M.ST.pmsgs) =
                                                                       (M.from_local_messages)
    let rec to_local_messages : (M.ST.pmsgs -> M.local_messages) =
                                                                     (M.to_local_messages)
    let rec send_messages : (M.out_messages -> M.in_messages) =
                                                                  (M.send_messages)
    let from_messages (xs : (local_messages) ST.P.arrayN) : (ST.pmsgs) ST.P.arrayN =
                                                                                       (ST.P.map (from_local_messages) xs)
    let to_messages (xs : (ST.pmsgs) ST.P.arrayN) : (local_messages) ST.P.arrayN =
                                                                                     (ST.P.map (to_local_messages) xs)
    let rec valid_local_messages (p : pub_input) (r : Pervasive.int) (xs : M.local_messages) : Pervasive.bool =
                                                                                                                  if (Int.lt r (weak_rounds p)) then (M.valid_local_messages (pub_input_conv p) r xs) else (final_valid_local_messages p xs)
    let valid_messages (p : ST.public_input) (r : ST.round) (ms : messages) : Pervasive.bool =
                                                                                                 (ST.P.all (fun (_ : Pervasive.int) -> (valid_local_messages p r)) ms)
    let rec valid_msg (p : pub_input) (r : Pervasive.int) (xs : M.ST.msg) : Pervasive.bool =
                                                                                               if (Int.lt r (weak_rounds p)) then (M.valid_msg (pub_input_conv p) r xs) else (final_valid_msg p xs)
    let valid_pmsgs (p : ST.public_input) (r : ST.round) (ms : ST.pmsgs) : Pervasive.bool =
                                                                                              (ST.P.all (fun (_ : Pervasive.int) -> (valid_msg p r)) ms)
    let valid_ppmsgs (p : ST.public_input) (r : ST.round) (ms : ST.ppmsgs) : Pervasive.bool =
                                                                                                (ST.P.all (fun (_ : Pervasive.int) -> (valid_pmsgs p r)) ms)
    type local_state = (M.local_state, M.local_out_messages) Aux.either
    let rec init_local_state (i : M.ST.party) (x : pub_input) (wi : M.ST.local_input) (ri : M.ST.local_rand) : (M.local_state, M.local_out_messages) Aux.either =
                                                                                                                                                                    (Aux.L (M.init_local_state i (pub_input_conv x) wi ri))
    let update_local_state : (M.ST.party -> (Pervasive.int -> (pub_input -> (M.ST.local_input -> (M.local_in_messages -> ((M.local_state, M.local_out_messages) Aux.either -> (M.local_state, M.local_in_messages) Aux.either)))))) =
                                                                                                                                                                                                                                        (mpc_update_local_state)
    let get_local_state (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : local_state =
                                                                                                                                                             (let (go) = (fun (st : local_state) (r0 : ST.round) -> (let (insr) = (ST.prget insi r0) in
                                                                                                                                                                                                                     (update_local_state i r0 x wi (to_local_messages insr) st))) in
                                                                                                                                                              (List.foldl go (init_local_state i x wi ri) (AuxList.iseq r)))
    type state = (local_state) ST.pmap
    let init_state (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                        (ST.P.imap (fun (i : ST.party) (wi_ri : (ST.local_input * ST.local_rand)) -> (init_local_state i x (fst wi_ri) (snd wi_ri))) (ST.P.zip ws rs))
    let update_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (local_in_messages) ST.pmap) (st : state) : (local_state) ST.P.arrayN =
                                                                                                                                                                               (ST.P.imap (fun (i : ST.party) (wsi_insi_sti : (ST.local_input * (local_in_messages * local_state))) -> (update_local_state i round x (Aux.fst3 wsi_insi_sti) (Aux.snd3 wsi_insi_sti) (Aux.thr3 wsi_insi_sti))) (ST.P.zip3 ws ins st))
    let get_state (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (local_state) ST.P.arrayN =
                                                                                                                                                                                       (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (get_local_state i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) (ST.P.zip3 ws rs ins))
    let stateful_local_protocol_round : (M.ST.party -> (Pervasive.int -> (pub_input -> ((M.local_state, M.local_out_messages) Aux.either -> M.local_out_messages)))) =
                                                                                                                                                                         (mpc_local_protocol_round)
    let stateful_local_protocol_end : (M.ST.party -> (pub_input -> ((M.local_state, M.local_out_messages) Aux.either -> final_output))) =
                                                                                                                                            (mpc_local_protocol_end)
    let stateful_local_protocol''' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : (ST.round) List.list) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                                            (List.foldl (fun (acc : (local_state * ST.out_msgs)) (round : ST.round) -> (let (outs') = (ST.prset (snd acc) round (from_local_messages (stateful_local_protocol_round i round x (Aux.fst3 acc)))) in
                                                                                                                                                                                                                                                                                                        (let (st') = (update_local_state i round x inp (to_local_messages (ST.prget ins round)) (Aux.fst3 acc)) in
                                                                                                                                                                                                                                                                                                         (st' , outs')))) (st , (ST.prempty sz (Pervasive.witness))) rounds)
    let stateful_local_protocol'' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : (local_state * ST.out_msgs) =
                                                                                                                                                                                                               (stateful_local_protocol''' i x inp st ins sz (AuxList.iseq rounds))
    let stateful_local_protocol' (i : ST.party) (x : ST.public_input) (inp : ST.local_input) (st : local_state) (ins : ST.in_msgs) : (local_state * ST.out_msgs) =
                                                                                                                                                                     (stateful_local_protocol'' i x inp st ins (ST.rounds x) (ST.rounds x))
    let stateful_local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                          (let (outs) = (stateful_local_protocol' i x (Aux.fst3 vi) (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) (Aux.snd3 vi)) in
                                                                                                                           (let (out) = (stateful_local_protocol_end i x (Aux.fst3 outs)) in
                                                                                                                            ((snd outs) , out)))
    let stateful_protocol_round (round : ST.round) (x : ST.public_input) (st : state) : (local_out_messages) ST.P.arrayN =
                                                                                                                             (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_round i round x sti)) st)
    let stateful_protocol_end (x : ST.public_input) (st : state) : (ST.local_output) ST.P.arrayN =
                                                                                                     (ST.P.imap (fun (i : ST.party) (sti : local_state) -> (stateful_local_protocol_end i x sti)) st)
    let stateful_protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : (ST.round) List.list) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                                  (List.foldl (fun (ins_st : ((ST.in_msgs) ST.pmap * state)) (round : ST.round) -> (let (ins0) = (Aux.fst3 ins_st) in
                                                                                                                                                                                                                                                                                    (let (st0) = (snd ins_st) in
                                                                                                                                                                                                                                                                                     (let (outs) = (send_messages (stateful_protocol_round round x st0)) in
                                                                                                                                                                                                                                                                                      ((ST.pprset ins0 round (from_messages outs)) , (update_state round x ws outs st0)))))) (ins , st) rounds)
    let stateful_protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (st : state) (rounds : ST.round) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                                     (stateful_protocol''' x ws ins st (AuxList.iseq rounds))
    let stateful_protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                     (stateful_protocol'' x ws (ST.pprempty (ST.rounds x) (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                     (let (ins_st') = (stateful_protocol' x ws rs) in
                                                                                                                                                                                                                      (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                       (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                        (tr , outs))))
    let stateful_protocol_sz' (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : ((ST.in_msgs) ST.pmap * state) =
                                                                                                                                                                             (stateful_protocol'' x ws (ST.pprempty sz (Pervasive.witness)) (init_state x ws rs) (ST.rounds x))
    let stateful_protocol_sz (sz : Pervasive.int) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                                                             (let (ins_st') = (stateful_protocol_sz' sz x ws rs) in
                                                                                                                                                                                                                                              (let (outs) = (stateful_protocol_end x (snd ins_st')) in
                                                                                                                                                                                                                                               (let (tr) = (ST.P.zip3 ws (Aux.fst3 ins_st') rs) in
                                                                                                                                                                                                                                                (tr , outs))))
    let local_protocol_round (i : ST.party) (r : ST.round) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.pmsgs =
                                                                                                                                                               (from_local_messages (stateful_local_protocol_round i r x (get_local_state i r x wi ri insi)))
    let local_protocol_end (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (insi : ST.in_msgs) : ST.local_output =
                                                                                                                                                     (stateful_local_protocol_end i x (get_local_state i (ST.rounds x) x wi ri insi))
    let local_protocol'' (i : ST.party) (x : ST.public_input) (wi : ST.local_input) (ri : ST.local_rand) (ins : ST.in_msgs) (sz : Pervasive.int) (rounds : ST.round) : ST.out_msgs =
                                                                                                                                                                                       (List.foldl (fun (outs : ST.out_msgs) (round : Pervasive.int) -> (ST.prset outs round (local_protocol_round i round x wi ri ins))) (ST.prempty sz (Pervasive.witness)) (AuxList.iseq rounds))
    let local_protocol' (i : ST.party) (x : ST.public_input) (vi : ST.view) : ST.out_msgs =
                                                                                              (local_protocol'' i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi) (ST.rounds x) (ST.rounds x))
    let local_protocol (i : ST.party) (x : ST.public_input) (vi : ST.view) : (ST.out_msgs * ST.local_output) =
                                                                                                                 (let (outs) = (local_protocol' i x vi) in
                                                                                                                  (let (out) = (local_protocol_end i x (Aux.fst3 vi) (Aux.thr3 vi) (Aux.snd3 vi)) in
                                                                                                                   (outs , out)))
    let protocol_round (round : ST.round) (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.pmsgs) ST.P.arrayN =
                                                                                                                                                                                         (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                                          (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_round i round x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol_end (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                                                                                           (let (xs) = (ST.P.zip3 ws rs ins) in
                                                                                                                                                                            (ST.P.imap (fun (i : ST.party) (wi_ri_insi : (ST.local_input * (ST.local_rand * ST.in_msgs))) -> (local_protocol_end i x (Aux.fst3 wi_ri_insi) (Aux.snd3 wi_ri_insi) (Aux.thr3 wi_ri_insi))) xs))
    let protocol''' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (round1 : ST.round) (d : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (List.Iota.iota_ round1 d))
    let protocol'' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) (ins : (ST.in_msgs) ST.pmap) (rounds : ST.round) : (ST.in_msgs) ST.pmap =
                                                                                                                                                                                    (List.foldl (fun (ins0 : (ST.in_msgs) ST.pmap) (round : ST.round) -> (ST.pprset ins0 round (ST.ppswap (protocol_round round x ws rs ins0)))) ins (AuxList.iseq rounds))
    let protocol' (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (ST.in_msgs) ST.pmap =
                                                                                                                                  (protocol'' x ws rs (ST.pprempty (ST.rounds x) (Pervasive.witness)) (ST.rounds x))
    let protocol (x : ST.public_input) (ws : (ST.local_input) ST.pmap) (rs : (ST.local_rand) ST.pmap) : (((ST.local_input * (ST.in_msgs * ST.local_rand))) ST.P.arrayN * (ST.local_output) ST.P.arrayN) =
                                                                                                                                                                                                            (let (ins) = (protocol' x ws rs) in
                                                                                                                                                                                                             (let (outs) = (protocol_end x ws rs ins) in
                                                                                                                                                                                                              (let (tr) = (ST.P.zip3 ws ins rs) in
                                                                                                                                                                                                               (tr , outs))))
    let get_view_in_msgs (j : ST.party) (vi : ST.view) : ST.rmsgs =
                                                                      (ST.P.get (Aux.snd3 vi) j)
    let get_view_out_msgs (i : ST.party) (j : ST.party) (x : ST.public_input) (vi : ST.view) : ST.rmsgs =
                                                                                                            (ST.P.get (local_protocol' i x vi) j)
    let consistent_inputs : (pub_input -> (M.ST.party -> (M.ST.party -> (M.ST.local_input -> (M.ST.local_input -> Pervasive.bool))))) =
                                                                                                                                          (mpc_consistent_inputs)
    let rec consistent_rands (x : pub_input) : (M.ST.party -> (M.ST.party -> (M.ST.local_rand -> (M.ST.local_rand -> Pervasive.bool)))) =
                                                                                                                                            (M.consistent_rands (pub_input_conv x))
    let valid_inputs (x : ST.public_input) (ws : (ST.local_input) ST.pmap) : Pervasive.bool =
                                                                                                (Pervasive.witness)
    let valid_rands (x : ST.public_input) (ws : (ST.local_rand) ST.pmap) : Pervasive.bool =
                                                                                              (Pervasive.witness)
    let consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                (Pervasive._and (ST.eq_rmsgs (get_view_in_msgs j vi) (get_view_out_msgs j i x vj)) (Pervasive._and (Pervasive.eq (get_view_in_msgs i vj) (get_view_out_msgs i j x vi)) (Pervasive._and (consistent_inputs x i j (Aux.fst3 vi) (Aux.fst3 vj)) (consistent_rands x i j (Aux.thr3 vi) (Aux.thr3 vj)))))
    let consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                    (Pervasive.witness)
    let pairwise_consistent_views (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                         (Pervasive._and (ST.valid_view x vi) (Pervasive._and (ST.valid_view x vj) (consistent_views x i j vi vj)))
    let pairwise_consistent_trace (x : ST.public_input) (tr : ST.trace) : Pervasive.bool =
                                                                                             (Pervasive.witness)
    let view_output (i : ST.party) (x : ST.public_input) (v : ST.view) : ST.local_output =
                                                                                             (local_protocol_end i x (Aux.fst3 v) (Aux.thr3 v) (Aux.snd3 v))
    let view_outputs (x : ST.public_input) (vs : (ST.view) ST.pmap) : (ST.local_output) ST.P.arrayN =
                                                                                                        (ST.P.imap (fun (i : ST.party) (v : ST.view) -> (view_output i x v)) vs)
    let stateful_consistent_outputs (_ : ST.public_input) (_ : ST.party) (_ : ST.party) (oi : NextMsgMaurerAPI.MaurerAPI._val) (oj : NextMsgMaurerAPI.MaurerAPI._val) : Pervasive.bool =
                                                                                                                                                                                           (NextMsgMaurerAPI.MaurerAPI.consistent_vals oi oj)
    type local_state2 = (local_state * local_state)
    let stateful_consistent_views_outputs_round (r : ST.round) (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : ((local_state * local_state) * Pervasive.bool) =
                                                                                                                                                                                                                                                                                     (let (outs1) = (from_local_messages (stateful_local_protocol_round i r x (fst sts))) in
                                                                                                                                                                                                                                                                                      (let (outs2) = (from_local_messages (stateful_local_protocol_round j r x (snd sts))) in
                                                                                                                                                                                                                                                                                       (let (in1) = (ST.prget ins1 r) in
                                                                                                                                                                                                                                                                                        (let (in2) = (ST.prget ins2 r) in
                                                                                                                                                                                                                                                                                         (let (sts1') = (update_local_state i r x inp1 (to_local_messages in1) (fst sts)) in
                                                                                                                                                                                                                                                                                          (let (sts2') = (update_local_state j r x inp2 (to_local_messages in2) (snd sts)) in
                                                                                                                                                                                                                                                                                           (let (b) = (Pervasive._and (ST.eq_msg (ST.P.get outs1 j) (ST.P.get in2 i)) (ST.eq_msg (ST.P.get outs2 i) (ST.P.get in1 j))) in
                                                                                                                                                                                                                                                                                            ((sts1' , sts2') , b))))))))
    let stateful_consistent_views_outputs''' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) (rounds : (ST.round) List.list) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                                                    (let (go) = (fun (stb : (local_state2 * Pervasive.bool)) (r : ST.round) -> (let (stb') = (stateful_consistent_views_outputs_round r x i j inp1 inp2 ins1 ins2 (fst stb)) in
                                                                                                                                                                                                                                                                                                                                                                ((fst stb') , (Pervasive._and (snd stb) (snd stb'))))) in
                                                                                                                                                                                                                                                                                     (List.foldl go (sts , (Pervasive._true)) rounds))
    let stateful_consistent_views_outputs'' (x : ST.public_input) (i : ST.party) (j : ST.party) (inp1 : ST.local_input) (inp2 : ST.local_input) (ins1 : ST.in_msgs) (ins2 : ST.in_msgs) (sts : local_state2) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                                                                                                   (stateful_consistent_views_outputs''' x i j inp1 inp2 ins1 ins2 sts (AuxList.iseq (ST.rounds x)))
    let stateful_consistent_views_outputs' (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : (local_state2 * Pervasive.bool) =
                                                                                                                                                                   (let (st1) = (init_local_state i x (Aux.fst3 vi) (Aux.thr3 vi)) in
                                                                                                                                                                    (let (st2) = (init_local_state j x (Aux.fst3 vj) (Aux.thr3 vj)) in
                                                                                                                                                                     (let (outsb) = (stateful_consistent_views_outputs'' x i j (Aux.fst3 vi) (Aux.fst3 vj) (Aux.snd3 vi) (Aux.snd3 vj) (st1 , st2)) in
                                                                                                                                                                      outsb)))
    let stateful_consistent_views_outputs (x : ST.public_input) (i : ST.party) (j : ST.party) (vi : ST.view) (vj : ST.view) : Pervasive.bool =
                                                                                                                                                 (let (outsb) = (stateful_consistent_views_outputs' x i j vi vj) in
                                                                                                                                                  (let (outs1) = (fst (fst outsb)) in
                                                                                                                                                   (let (outs2) = (snd (fst outsb)) in
                                                                                                                                                    (let (b) = (snd outsb) in
                                                                                                                                                     (let (out1) = (stateful_local_protocol_end i x outs1) in
                                                                                                                                                      (let (out2) = (stateful_local_protocol_end j x outs2) in
                                                                                                                                                       (Pervasive._and b (stateful_consistent_outputs x i j out1 out2))))))))
end
