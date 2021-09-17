open NextMsgECPervasive
open NextMsgECList
open NextMsgECBindings

module ZSet = Set.Make(Z);;

module ISet = struct
    type iset = ZSet.t
    let oflist : ((Pervasive.int) List.list -> iset) = fun s ->
        ZSet.of_list (eclist_to_list s)
    let elems : (iset -> (Pervasive.int) List.list) = fun s ->
        list_to_eclist (ZSet.elements s)
    let mem : (Pervasive.int -> (iset -> Pervasive.bool)) = fun x s ->
        ZSet.mem x s
    let subset : (iset -> (iset -> Pervasive.bool)) = fun s1 s2 ->
        ZSet.subset s1 s2
    let card : (iset -> Pervasive.int) = fun s ->
        Z.of_int (ZSet.cardinal s)
    let union : (iset -> (iset -> iset)) = fun s1 s2 ->
        ZSet.union s1 s2
    let intersect : (iset -> (iset -> iset)) = fun s1 s2 ->
        ZSet.inter s1 s2
    let all : ((Pervasive.int -> Pervasive.bool) -> (iset -> Pervasive.bool)) = fun f xs ->
        ZSet.for_all f xs
    let set0 : iset = ZSet.empty
    let set1 : (Pervasive.int -> iset) = fun z -> ZSet.singleton z
    let iset : (Pervasive.int -> iset) = fun n ->
        ZSet.of_seq (eclist_to_seq (AuxList.iseq n))
    let add (s : iset) (x : Pervasive.int) : iset =
                                                      (union s (set1 x))
    let equal(s1 : iset) (s2 : iset) : bool = ZSet.equal s1 s2
end
