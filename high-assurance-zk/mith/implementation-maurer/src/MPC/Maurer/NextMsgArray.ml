open NextMsgECPervasive
open NextMsgECInt
open NextMsgECList
open NextMsgECLogic
module Array = struct
    type ('a) array = 'a Array.t
    let get : (('a) array -> (Pervasive.int -> 'a)) = fun xs i ->
        Array.get xs (Z.to_int i)
    let set : (('a) array -> (Pervasive.int -> ('a -> ('a) array))) = fun xxs i x ->
        let _ = Array.set xxs (Z.to_int i) x in xxs
    let init : (Pervasive.int -> ((Pervasive.int -> 'a) -> ('a) array)) = fun size f ->
        (Array.init (Z.to_int size) (fun (i:int) -> f (Z.of_int i) ))
    let size : (('a) array -> Pervasive.int) = fun xs -> Z.of_int (Array.length xs)
    let of_list (l : ('a) List.list) : ('a) array =
                                                      (init (List.size l) (fun (i : Pervasive.int) -> (List.nth (Pervasive.witness) l i)))
    let to_list (t : ('a) array) : ('a) List.list =
                                                      (List.mkseq (fun (i : Pervasive.int) -> (get t i)) (size t))
    let to_assoc (t : ('a) array) : ((Pervasive.int * 'a)) List.list =
                                                                         (List.zip (AuxList.iseq (size t)) (to_list t))
    let create (sz : Pervasive.int) (x : 'a) : ('a) array =
                                                              (init sz (fun (_ : Pervasive.int) -> x))
    let singl (i : Pervasive.int) (x : 'a) : ('a) array =
                                                            (init (Pervasive.mk_int 1) (fun (j : Pervasive.int) -> if (Pervasive.eq j i) then x else (Pervasive.witness)))
    let imap (f : (Pervasive.int -> ('a -> 'b))) (xs : ('a) array) : ('b) array =
                                                                                    (init (size xs) (fun (j : Pervasive.int) -> (f j (get xs j))))
    let map (f : ('a -> 'b)) (xs : ('a) array) : ('b) array =
                                                                (imap (fun (_ : Pervasive.int) -> f) xs)
    let merge (f : ('a -> ('b -> 'c))) (xs : ('a) array) (ys : ('b) array) : ('c) array =
                                                                                            (init (Int.min (size xs) (size ys)) (fun (i : Pervasive.int) -> (f (get xs i) (get ys i))))
    let zip (xs : ('a) array) (ys : ('b) array) : (('a * 'b)) array =
                                                                        (merge (fun (x : 'a) (y : 'b) -> (x , y)) xs ys)
    let filter (p : (Pervasive.int -> ('a -> Pervasive.bool))) (xs : ('a) array) : ('a) array =
                                                                                                  (init (size xs) (fun (j : Pervasive.int) -> if (p j (get xs j)) then (get xs j) else (Pervasive.witness)))
    let all (f : (Pervasive.int -> ('a -> Pervasive.bool))) (t : ('a) array) : Pervasive.bool =
                                                                                                  (List.all (fun (i : Pervasive.int) -> (f i (get t i))) (AuxList.iseq (size t)))
    let allsame (xs : ('a) array) : Pervasive.bool =
                                                       (List.all (fun (i : Pervasive.int) -> (List.all (fun (j : Pervasive.int) -> (Pervasive.eq (get xs i) (get xs j))) (AuxList.iseq (size xs)))) (AuxList.iseq (size xs)))
    let zip3 (xs : ('a) array) (ys : ('b) array) (zs : ('c) array) : (('a * ('b * 'c))) array =
                                                                                                  (zip xs (zip ys zs))
    let eq_array (f:'a->'b->bool) (m1:'a array) (m2:'b array) : Pervasive.bool =
        Pervasive._and
            (Pervasive.eq (size m1) (size m2))
            (List.all (fun i -> f (get m1 i) (get m2 i) ) (AuxList.iseq (size m1)))
    let lsize (def : Pervasive.int) (xxs : (('b) array) List.list) : Pervasive.int =
                                                                                       (AuxList.foldl1 def (Int.min) (List.map (size) xxs))
    let concat (xxs : (('b) array) List.list) : (('b) List.list) array =
                                                                           (List.foldl (fun (xs : (('b) List.list) array) (b : ('b) array) -> (merge (List.rcons) xs b)) (create (lsize (Pervasive.mk_int 0) xxs) List.Nil) xxs)
end
