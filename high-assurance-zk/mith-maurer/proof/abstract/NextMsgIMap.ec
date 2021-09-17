require import AllCore Int List.
require import Aux AuxList.
require import NextMsgISet.

(* A dynamic size map *)
theory IMap.

  import ISet.

  type 'a imap.
  op get  (xs:'a imap) (i:int) : 'a option.
  op set (xs:'a imap) (i:int) (x:'a) : 'a imap.
  op rem (xs:'a imap) (i:int) : 'a imap.
  op size (xs:'a imap) : int.

  op ofset : (int -> 'a) -> iset -> 'a imap.
  op empty :'a imap.
  op imap : (int -> 'a -> 'b) -> 'a imap -> 'b imap.
  op map (f:'a -> 'b) (xs:'a imap) : 'b imap.
  op ofassoc (xs:(int*'a) list) : 'a imap.

  op zip (m1 : 'b1 imap) (m2 : 'b2 imap) : ('b1*'b2) imap.
  op merge (f:'b1 -> 'b2 -> 'b3) (m1 : ('b1) imap) (m2 : ('b2) imap) : ('b3) imap.
  op all (f:int -> 'b -> bool) (m:('b) imap) : bool.

  op dom : 'a imap -> iset.

  op redom (cr:iset) (xs:('b) imap) : ('b) imap =
    ofset (fun i => oget (get xs i)) cr.

end IMap.
