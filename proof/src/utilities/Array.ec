(**
  Formalization of arrays, without modifications. This interface can be extended to define 
  immutable arrays, but because it was needed for our use-case, we prefered not to define
  any **se** operation.
*)
require import AllCore List.

(** Array type *)
type 'a array.

(** Computes the size of an array *)
op size : 'a array -> int.

op empty : 'a array.
axiom size_empty ['a] : size empty<:'a array> = 0.

(** Gets a value from an array. If the lookup index is out of the array bounds, it returns the
    given default value. In summary, [get z xs i] returns [xs.[i]] if [0 <= i < size xs] and 
    returns [z] otherwise. *)
op get : 'a -> 'a array -> int -> 'a.

(** Defines the behavior of the [get] function: [get z xs i] returns [xs.[i]] if 
    [0 <= i < size xs] and returns [z] otherwise *)
axiom get_out_of_bounds (xs : 'a array) k z : 
  !(0 <= k < size xs) => get z xs k = z.

op set : 'a array -> int -> 'a -> 'a array.

(** [make k x] creates a fresh array of size [k], where all elements are [x] *)
op make : int -> 'a -> 'a array.

(** Establishes that arrays created via [make k x] will have a size of [k] *)
axiom size_make (k : int) (x : 'a) : size (make k x) = k.
(** Establishes that all elements of arrays created via [make k x] will be [x] *)
axiom get_make (k : int) (x : 'a) (i : int) z : 0 <= i < k => get z (make k x) i = x.

(** Converstion to list *)
op to_list : 'a array -> 'a List.list.
(** Converstion from list *)
op of_list : 'a list -> 'a array.

(** Cancelation property. It means that converting a list to an array and then converting back to
    a list yields the original list *)
axiom to_listK (xs : 'a list) : to_list (of_list xs) = xs.
(** Cancelation property. It means that converting an array to a list and then converting back to
    an array yields the original array *)
axiom of_listK (xs : 'a array) : of_list (to_list xs) = xs.

(** Establishes that converting an array to a list preserves its size *)
axiom size_to_list (xs : 'a array) : size (to_list xs) = size xs.
(** Establishes that converting an array to a list preserves its elements and their order *)
axiom nth_to_list (z : 'a) (xs : 'a array) k : 
  get z xs k = nth z (to_list xs) k.

(** Establishes that converting a list to an array preserves its size *)
axiom size_of_list (xs : 'a list) : size (of_list xs) = size xs.
(** Establishes that converting a list to an array preserves its elements and their order *)
axiom get_of_list (z : 'a) (xs : 'a list) k : 
  nth z xs k = get z (of_list xs) k.

(** [iota_array i j] *)
op iota_array : int -> int -> int array.

axiom iota_to_list (x y : int) : iota_array x y = of_list (List.Iota.iota_ x y).
axiom iota_of_list (x y : int) : List.Iota.iota_ x y = to_list (iota_array x y).

(** [map f xs] *)
op map : ('a -> 'b) -> 'a array -> 'b array.
axiom map_to_list (f : 'a -> 'b) (xs : 'a array) : map f xs = of_list (map f (to_list xs)).
axiom map_of_list (f : 'a -> 'b) (xs : 'a list) : of_list (map f xs) = map f (of_list xs).

abbrev unzip1 ['a, 'b] (s : ('a * 'b) array) : 'a array =
  map (fun (p : 'a * 'b) => p.`1) s.
abbrev unzip2 ['a, 'b] (s : ('a * 'b) array) : 'b array =
  map (fun (p : 'a * 'b) => p.`2) s.

lemma map_comp (f1 : 'b -> 'c) (f2 : 'a -> 'b) (s : 'a array) :
  map (f1 \o f2) s = map f1 (map f2 s) by smt.

axiom size_map (f : 'a -> 'b) (s : 'a array) : size (map f s) = size s.

axiom get_map (x1 : 'a) (x2 : 'b) (f : 'a -> 'b) (n : int) (s : 'a array) :
    0 <= n && n < size s => get x2 (map f s) n = f (get x1 s n).

(** [mkseq f n] *)
op mkseq (f : int -> 'a) (n : int) : 'a array = map f (iota_array 0 n).

(** [all p xs] *)
op all : ('a -> bool) -> 'a array -> bool.

axiom all_to_list (p : 'a -> bool) (xs : 'a array) : all p xs = all p (to_list xs).
axiom all_of_list (p : 'a -> bool) (xs : 'a list) : all p (of_list xs) = all p xs.
