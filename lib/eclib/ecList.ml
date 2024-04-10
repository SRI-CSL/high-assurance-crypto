open EcCore
open EcOption

type 'a list =
  | Nil
  | Cons of 'a * 'a list

let rec iota_' i j acc = 
  if Z.equal i j then Nil
  else Cons (i, iota_' (Z.add i Z.one) j acc)

let iota_ i j = iota_' i j Nil

let rec size : 'a . ('a list) -> (Z.t) =
  fun xs ->
  begin match xs with
  | Nil -> Z.zero
  | Cons (y2, ys) -> Z.add Z.one (size ys)
  end

let rec map : 'a 'b . ('a -> 'b) -> ('a list) -> ('b list) =
  fun f xs ->
  begin match xs with
  | Nil -> Nil
  | Cons (y, ys) -> Cons ((f y), (map f ys))
  end

let rec nth : 'a . 'a -> ('a list) -> (Z.t) -> 'a =
  fun x xs n ->
  begin match xs with
  | Nil -> x
  | Cons (y, ys) ->
     if n = Z.zero then begin y end else begin nth x ys (Z.sub n Z.one) end
  end

let rec mem (s : 'a list) (z : 'a) =
  match s with
  | Nil -> false
  | Cons (x, s') -> z = x || mem s' z

let rec head : 'a . 'a -> ('a list) -> 'a =
  fun z0 s -> begin match s with
              | Nil -> z0
              | Cons (x, s1) -> x
              end

let rec concat : 'a . ('a list) -> ('a list) -> ('a list) =
  fun s1 s2 ->
  begin match s1 with
  | Nil -> s2
  | Cons (x, s11) -> Cons (x, (concat s11 s2))
  end
  
let rec catrev : 'a . ('a list) -> ('a list) -> ('a list) =
  fun s1 s2 ->
  begin match s1 with
  | Nil -> s2
  | Cons (x, s11) -> catrev s11 (Cons (x, s2))
  end

let rev (s: 'a list) : 'a list = catrev s Nil
                               
let rec foldr : 'a 'b . ('a -> ('b -> 'b)) -> 'b -> ('a list) -> 'b =
  fun f z0 xs ->
  begin match xs with
  | Nil -> z0
  | Cons (y, ys) -> (f y) (foldr f z0 ys)
  end

let rec onth : 'a . ('a list) -> (Z.t) -> ('a option) =
  fun xs n ->
  begin match xs with
  | Nil -> None
  | Cons (y2, ys) ->
     if n = Z.zero then begin Some y2 end
     else
       begin
         onth ys (Z.sub n Z.one) end
  end

let rec find : 'a . ('a -> (bool)) -> ('a list) -> (Z.t) =
  fun p s ->
  begin match s with
  | Nil -> Z.zero
  | Cons (x1, sqt) ->
     if p x1 then begin Z.zero end else begin Z.add (find p sqt) Z.one end
  end

let index (x1: 'a) : ('a list) -> (Z.t) = find (pred1 x1)

let assoc (xs: ('a * 'b) list) (a: 'a) : 'b option =
  omap snd (onth xs ((index a) (map fst xs)))

let rec zip : 'a 'b . ('a list) -> ('b list) -> (('a * 'b) list) =
  fun s t ->
  begin match s,t with
  | Cons (x, s'), Cons (y, t') -> Cons ((x,y), zip s' t')
  | Cons (_, _), Nil -> Nil
  | Nil, Cons (_, _) -> Nil
  | Nil, Nil -> Nil 
  end

let get_elems_n (ls : ('a list) list) : 'a -> Z.t -> 'a list =
  fun z n -> map (fun l -> nth z l n) ls

let rec transpose' (iss : (Z.t) list) (ls : ('a list) list) =
  begin match iss with
  | Nil -> Nil
  | Cons (i, is') -> Cons (get_elems_n ls (Obj.magic None) i, transpose' is' ls)
  end

let transpose (ls : ('a list) list) : ('a list) list =
  transpose' (iota_ Z.zero (size (head Nil ls))) ls

let rec init' : 'a . Z.t -> Z.t -> (Z.t -> 'a) -> 'a list -> 'a list =
  fun i j f l -> if Z.equal i j then l else init' (Z.add i (Z.of_string "1")) j f ((Cons (f i, l))) 
  
let init : 'a . Z.t -> (Z.t -> 'a) -> 'a list =
  fun n f -> init' (Z.zero) n f Nil
  
let dlist : 'a . Z.t -> (unit -> 'a) -> 'a list =
  fun n d -> init n (fun _ -> d ())

let rec dlist_uniq' : 'a . Z.t -> Z.t -> (unit -> 'a) -> 'a list -> 'a list =
  fun i n d l ->
  if Z.equal i n then l
  else
    let r = d () in
    if mem l r then dlist_uniq' i n d l
    else dlist_uniq' (Z.add i Z.one) n d (Cons (r, l))
           
let dlist_uniq : 'a . Z.t -> (unit -> 'a) -> 'a list =
  fun n d -> dlist_uniq' Z.zero n d Nil

let unzip1 (l : ('a * 'b) list) =
  map fst l

let unzip2 (l : ('a * 'b) list) =
  map snd l

let rec all : 'a . ('a -> bool) -> 'a list -> bool =
  fun p xs ->
  begin match xs with
  | Nil -> true
  | Cons (y, ys) -> p y && all p ys
  end

let mem_assoc (l : ('a * 'b) list) (x : 'a) = mem (unzip1 l) x
  
let unzip1_assoc (l : ('a * ('b * 'c)) list) : ('a * 'b) list =
  map (fun (x : 'a * ('b * 'c)) -> (fst x, fst (snd x))) l

let unzip2_assoc (l : ('a * ('b * 'c)) list) : ('a * 'c) list =
  map (fun (x : 'a * ('b * 'c)) -> (fst x, snd (snd x))) l

let rec filter : 'a . ('a -> bool) -> 'a list -> 'a list =
  fun p xs -> begin match xs with
              | Nil -> Nil
              | Cons (y, ys) -> if p y then Cons (y, filter p ys) else filter p ys
              end

let zip_assoc (l : ('a * 'b) list) (l' : ('a * 'c) list) : ('a * ('b * 'c)) list =
  map (fun (x : 'a * 'b) -> (fst x, (snd x, oget (assoc l' (fst x)))))
    (filter (fun (ab : 'a * 'b) -> mem_assoc l' (fst ab)) l)

let rec map2 (f : 'a -> 'b -> 'c) (l1 : 'a list) (l2 : 'b list) : 'c list =
  begin match (l1,l2) with
  | (Nil, Nil) -> Nil
  | (Cons (x, l1'), Nil) -> Nil
  | (Nil, Cons (y, l2')) -> Nil
  | (Cons (x, l1'), Cons (y, l2')) -> Cons (f x y, map2 f l1' l2')
  end

let rec rem : 'a . 'a -> 'a list -> 'a list =
  fun z s -> begin match s with
             | Nil -> Nil
             | Cons (x, s') -> if x = z then s' else Cons (x, rem z s')
             end

let sumt (l : EcPrimeField.t list) : EcPrimeField.t = foldr EcPrimeField.fadd EcPrimeField.zero l
