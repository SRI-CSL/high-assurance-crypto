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

(** Gets a value from an array. If the lookup index is out of the array bounds, it returns the
    given default value. In summary, [get z xs i] returns [xs.[i]] if [0 <= i < size xs] and 
    returns [z] otherwise. *)
op get : 'a -> 'a array -> int -> 'a.

(** Defines the behavior of the [get] function: [get z xs i] returns [xs.[i]] if 
    [0 <= i < size xs] and returns [z] otherwise *)
axiom get_out_of_bounds (xs : 'a array) k z : 
  !(0 <= k < size xs) => get z xs k = z.

(** [make k x] creates a fresh array of size [k], where all elements are [x] *)
op make : int -> 'a -> 'a array.

(** Establishes that arrays created via [make k x] will have a size of [k] *)
axiom size_make (k : int) (x : 'a) : size (make k x) = k.
(** Establishes that all elements of arrays created via [make k x] will be [x] *)
axiom get_make (k : int) (x : 'a) (i : int) z : 0 <= i < k => get z (make k x) i = x.

(** Converstion to list *)
op to_list : 'a array -> 'a list.
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
