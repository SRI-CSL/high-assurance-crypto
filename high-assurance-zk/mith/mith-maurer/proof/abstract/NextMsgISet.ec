require import AllCore Int List.
require import Aux AuxList.

(* A dynamic size set *)
theory ISet.

  type iset.

  op oflist : int list -> iset.
  op elems : iset -> int list.
  op mem (x:int) (xs:iset) : bool.
  op subset (xs ys : iset) : bool.
  op card : iset -> int.
  op union (s1 s2 : iset) : iset.
  op intersect (s1 s2 : iset) : iset.
  op all (f:int -> bool) (m: iset) : bool.
  op set0 : iset.
  op set1 (x:int) : iset.
  op iset (n:int) : iset.
  abbrev add (s:iset) (x:int) : iset = union s (set1 x).
  op equal (s1 s2 : iset) : bool.

end ISet.
