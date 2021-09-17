open NextMsgECPervasive
open NextMsgECList
open NextMsgECLogic
open NextMsgISet
open NextMsgECBindings

module ZMap = Map.Make(Z);;

module IMap = struct
    type ('a) imap = 'a ZMap.t 
    let get : (('a) imap -> (Pervasive.int -> ('a) Logic.option)) = fun m x ->
        match (ZMap.find_opt x m) with
        | None -> Logic.None
        | Some x -> Logic.Some x
    let set : (('a) imap -> (Pervasive.int -> ('a -> ('a) imap))) = fun m x v ->
        ZMap.add x v m
    let rem : (('a) imap -> (Pervasive.int -> ('a) imap)) = fun xs i ->
        ZMap.remove i xs
    let size : (('a) imap -> Pervasive.int) = fun xs ->
        Z.of_int (ZMap.cardinal xs)
    let ofset : ((Pervasive.int -> 'a) -> (NextMsgISet.ISet.iset -> ('a) imap)) = fun f xs ->
        ZMap.of_seq (eclist_to_seq (List.map (fun x -> (x,f x)) (ISet.elems xs)))
    let empty : ('a) imap = ZMap.empty 
    let imap : ((Pervasive.int -> ('a -> 'b)) -> (('a) imap -> ('b) imap)) = fun f xs ->
        ZMap.mapi f xs
    let map : (('a -> 'b) -> (('a) imap -> ('b) imap)) = fun f xs ->
        ZMap.map f xs
    let ofassoc : (((Pervasive.int * 'a)) List.list -> ('a) imap) = fun xs ->
        ZMap.of_seq (eclist_to_seq xs)
    let all : ((Pervasive.int -> ('b -> Pervasive.bool)) -> (('b) imap -> Pervasive.bool)) = fun f xs ->
        ZMap.for_all f xs
    let dom : (('a) imap -> NextMsgISet.ISet.iset) = fun m ->
        ISet.oflist (List.map fst (list_to_eclist (ZMap.bindings m)))
    let zip : (('b1) imap -> (('b2) imap -> (('b1 * 'b2)) imap)) = fun xs ys ->
        ofset (fun i -> (ZMap.find i xs,ZMap.find i ys) ) (ISet.intersect (dom xs) (dom ys))
    let merge : (('b1 -> ('b2 -> 'b3)) -> (('b1) imap -> (('b2) imap -> ('b3) imap))) = fun f xs ys ->
        ofset (fun i -> f (ZMap.find i xs) (ZMap.find i ys) ) (ISet.intersect (dom xs) (dom ys))
    let redom (cr : NextMsgISet.ISet.iset) (xs : ('b) imap) : ('b) imap =
                                                                           (ofset (fun (i : Pervasive.int) -> (Logic.oget (get xs i))) cr)
end
