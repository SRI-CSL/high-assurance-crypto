open NextMsgECCore
open NextMsgECPervasive
open NextMsgECList
module MaurerP = struct
    let size : Pervasive.int =
                                 (Pervasive.mk_int 5)
    type ('a) arrayN = ('a) Aux.array5
    let get : (('a) Aux.array5 -> (Pervasive.int -> 'a)) =
                                                             (Aux.nth_array5)
    let set : (('a) Aux.array5 -> (Pervasive.int -> ('a -> ('a * ('a * ('a * ('a) Aux.array2)))))) =
                                                                                                       (Aux.set_array5)
    let init : ((Pervasive.int -> 'a) -> ('a * ('a * ('a * ('a * 'a))))) =
                                                                             (Aux.init_array5)
    let of_list (l : ('a) List.list) : ('a) arrayN =
                                                       (init (fun (i : Pervasive.int) -> (List.nth (Pervasive.witness) l i)))
    let to_list (t : ('a) arrayN) : ('a) List.list =
                                                       (List.mkseq (fun (i : Pervasive.int) -> (get t i)) (size))
    let to_assoc (t : ('a) arrayN) : ((Pervasive.int * 'a)) List.list =
                                                                          (List.zip (AuxList.iseq (size)) (to_list t))
    let create (x : 'a) : ('a) arrayN =
                                          (init (fun (_ : Pervasive.int) -> x))
    let singl (i : Pervasive.int) (x : 'a) : ('a) arrayN =
                                                             (init (fun (j : Pervasive.int) -> if (Pervasive.eq j i) then x else (Pervasive.witness)))
    let imap (f : (Pervasive.int -> ('a -> 'b))) (xs : ('a) arrayN) : ('b) arrayN =
                                                                                      (init (fun (j : Pervasive.int) -> (f j (get xs j))))
    let map (f : ('a -> 'b)) (xs : ('a) arrayN) : ('b) arrayN =
                                                                  (imap (fun (_ : Pervasive.int) -> f) xs)
    let merge (f : ('a -> ('b -> 'c))) (xs : ('a) arrayN) (ys : ('b) arrayN) : ('c) arrayN =
                                                                                               (init (fun (i : Pervasive.int) -> (f (get xs i) (get ys i))))
    let zip (xs : ('a) arrayN) (ys : ('b) arrayN) : (('a * 'b)) arrayN =
                                                                           (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
    let filter (p : (Pervasive.int -> ('a -> Pervasive.bool))) (xs : ('a) arrayN) : ('a) arrayN =
                                                                                                    (init (fun (j : Pervasive.int) -> if (p j (get xs j)) then (get xs j) else (Pervasive.witness)))
    let rec all (f : (Pervasive.int -> ('a -> Pervasive.bool))) (t : ('a) arrayN) : Pervasive.bool =
                                                                                                       (List.all (fun (i : Pervasive.int) -> (f i (get t i))) (AuxList.iseq (size)))
    let allsame (xs : ('a) arrayN) : Pervasive.bool =
                                                        (List.all (fun (i : Pervasive.int) -> (List.all (fun (j : Pervasive.int) -> (Pervasive.eq (get xs i) (get xs j))) (AuxList.iseq (size)))) (AuxList.iseq (size)))
    let zip3 (xs : ('a) arrayN) (ys : ('b) arrayN) (zs : ('c) arrayN) : (('a * ('b * 'c))) arrayN =
                                                                                                      (zip xs (zip ys zs))
    let concat (xxs : (('b) arrayN) List.list) : (('b) List.list) arrayN =
                                                                             (List.foldl (fun (xs : (('b) List.list) arrayN) (b : ('b) arrayN) -> (merge (List.rcons) xs b)) (create List.Nil) xxs)
end
