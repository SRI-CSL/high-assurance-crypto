open NextMsgECPervasive
open NextMsgECLogic

module List = struct
    type 'a list = 'a ECList.list =
      | Nil
      | Cons of 'a * 'a ECList.list 
      
    let rec iota_' i j acc = 
        if Z.equal i j then Nil
        else Cons (i, iota_' (Z.add i Z.one) j acc)
      
    module Iota = struct
        let rec iota_ : Pervasive.int -> Pervasive.int -> Pervasive.int list = (fun i j -> iota_' i j Nil)
    end
    
    let rec onth : 'a . ('a list) -> (Pervasive.int) -> ('a Logic.option) =
      fun xs n ->
      begin match xs with
      | Nil -> None
      | Cons (y2, ys) ->
         if n = Z.zero then begin Some y2 end
         else
           begin
             onth ys (Z.sub n Z.one) end
      end
    let rec nth : 'a -> 'a list -> Pervasive.int -> 'a = fun x xs n ->
        begin match xs with
        | Nil -> x
        | Cons (y, ys) ->
           if n = Z.zero then begin y end else begin nth x ys (Z.sub n Z.one) end
        end
    let rec find : 'a . ('a -> (Pervasive.bool)) -> ('a list) -> (Pervasive.int) =
          fun p s ->
          begin match s with
          | Nil -> Z.zero
          | Cons (x1, sqt) ->
             if p x1 then begin Z.zero end else begin Z.add (find p sqt) Z.one end
          end

    let index (x1: 'a) : ('a list) -> (Pervasive.int) = find (pred1 x1)
    let rec zip : 'a list -> 'b list -> ('a * 'b) list = fun s t ->
        begin match s,t with
        | Cons (x, s'), Cons (y, t') -> Cons ((x,y), zip s' t')
        | Cons (_, _), Nil -> Nil
        | Nil, Cons (_, _) -> Nil
        | Nil, Nil -> Nil 
        end
    let rec all : ('a -> bool) -> 'a list -> Pervasive.bool = fun p xs ->
        begin match xs with
        | Nil -> true
        | Cons (y, ys) -> p y && all p ys
        end
    let rec foldl : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b = fun f z0 xs ->
        begin match xs with
        | Nil -> z0
        | Cons (y, ys) -> foldl f (f z0 y) ys
        end  
    let rec foldr : ('a -> ('b -> 'b)) -> 'b -> ('a list) -> 'b =
        fun f z0 xs ->
        begin match xs with
        | Nil -> z0
        | Cons (y, ys) -> (f y) (foldr f z0 ys)
        end    
    let rec catrev : 'a . ('a list) -> ('a list) -> ('a list) =
        fun s1 s2 ->
        begin match s1 with
        | Nil -> s2
        | Cons (x, s11) -> catrev s11 (Cons (x, s2))
        end
    let rev (s: 'a list) : 'a list = catrev s Nil
    let rec rcons : 'a list -> 'a -> 'a list = fun s z ->
        match s with
        | Nil -> Cons (z, Nil)
        | Cons (x, s') -> Cons (x, rcons s' z)
    let rec size : 'a list -> Pervasive.int = fun xs ->
        begin match xs with
        | Nil -> Z.zero
        | Cons (y2, ys) -> Z.add Z.one (size ys)
        end
    let rec map (f:'a->'b) (xs:'a list) : 'b list = 
        begin match xs with
        | Nil -> Nil
        | Cons (y, ys) -> Cons ((f y), (map f ys))
        end
    let head : 'a list -> 'a = fun s ->
        fun s -> begin match s with
                    | Nil -> Pervasive.witness
                    | Cons (x, s1) -> x
                    end
    let behead : 'a list -> 'a list = fun xs ->
        match xs with
        | Nil -> Nil
        | Cons (y, ys) -> ys
    let assoc (xs: ('a * 'b) list) (a: 'a) : 'b Logic.option =
          Logic.omap snd (onth xs ((index a) (map fst xs)))
    let unzip1 (s : ('a * 'b) list) : 'a list = map fst s
    let unzip2 (s : ('a * 'b) list) : 'bb list = map snd s
    let mkseq : (Pervasive.int -> 'a) -> Pervasive.int -> 'a list = fun f n -> map f (Iota.iota_ (Z.of_int 0) n)
    
end

module AuxList = struct
    let iseq : Pervasive.int -> Pervasive.int List.list = fun n -> List.Iota.iota_ Z.zero n
    let rec foldl_iseq' (f:'b -> Pervasive.int -> 'b) (z:'b) (n0:Pervasive.int) (n:Pervasive.int) : 'b = if Z.geq n0 n
        then z
        else foldl_iseq' f (f z n0) (Z.succ n0) n
    let rec foldl_iseq (f:'b -> Pervasive.int -> 'b) (z:'b) (n:Pervasive.int) : 'b =
        foldl_iseq' f z Z.zero n
    let all_iseq (p:Pervasive.int -> bool) (n:Pervasive.int) : bool =
        foldl_iseq (fun b i -> b && p i) true n
    let foldl1 (def:'a) (f:'a->'a->'a) (xs:'a List.list) : 'a = 
        match xs with
        | Nil -> def
        | Cons (y,ys) -> List.foldl f y ys
    let cons (x:'a) (xs:'a List.list) : 'a List.list = Cons(x,xs)
    let rec cat (s1:'a List.list) (s2:'a List.list) : 'a List.list = 
        begin match s1 with
        | Nil -> s2
        | Cons (x, s11) -> Cons (x, (cat s11 s2))
        end
    let lsame (p:'b->'c->Pervasive.bool) (xs:'b List.list) (ys:'c List.list) : Pervasive.bool =
        (List.size xs = List.size ys) &&
        List.all (fun xy -> p (fst xy) (snd xy)) (List.zip xs ys)
end