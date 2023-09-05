(* manual code to link EC types with ML types *)

let rec eclist_to_list (xs:'a NextMsgECList.List.list) : 'a list =
    match xs with
    | NextMsgECList.List.Nil -> []
    | NextMsgECList.List.Cons (x,xs) -> x :: eclist_to_list xs
    
let rec list_to_eclist (xs: 'a list) : 'a NextMsgECList.List.list =
    match xs with
    | [] -> NextMsgECList.List.Nil
    | x::xs -> NextMsgECList.List.Cons(x,list_to_eclist xs)

let eclist_to_seq (xs: 'a NextMsgECList.List.list) : 'a Seq.t = 
    NextMsgECList.List.foldr (fun x xs -> fun _ -> Seq.Cons (x,xs)) (fun _ -> Seq.Nil) xs

let seq_to_eclist (xs:'a Seq.t) : 'a NextMsgECList.List.list = 
    NextMsgECList.List.rev (Seq.fold_left (fun xs x -> NextMsgECList.List.Cons (x,xs)) NextMsgECList.List.Nil xs)