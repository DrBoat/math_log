let nip str = String.sub str 1 ((String.length str) - 1);;

type var  = Var   of string
and  nnot = Nnot1 of nnot | Nnot2 of var | Nnot3 of expr
and  aand = And1  of nnot | And2  of aand * nnot
and  oor  = Or1   of aand | Or2   of oor * aand
and  expr = Exp1  of oor  | Exp2  of oor * expr;;

let rec print_expr expr = match expr with
    | Exp1 a      -> print_oor a
    | Exp2 (a, b) -> "(->," ^ (print_oor a) ^ "," ^ (print_expr b) ^ ")"
and print_oor expr = match expr with
    | Or1 a      -> print_aand a
    | Or2 (a, b) -> "(|," ^ (print_oor a) ^ "," ^ (print_aand b) ^ ")"
and print_aand expr = match expr with
    | And1 a      -> print_nnot a
    | And2 (a, b) -> "(&," ^ (print_aand a) ^ "," ^ (print_nnot b) ^ ")"
and print_nnot expr = match expr with
    | Nnot1 a -> "(!" ^ (print_nnot a) ^ ")"
    | Nnot2 a -> print_var a
    | Nnot3 a -> print_expr a
and print_var (Var a) = a;;

let strange = "'";;

let rec make_var str have = if String.length str == 0 
    then (Var have, str)
    else if String.length str >= String.length strange && String.sub str 0 (String.length strange) = strange
    then make_var (String.sub str (String.length strange) (String.length str - String.length strange)) (have ^ strange)
    else match str.[0] with
    | 'A'..'Z' | '0'..'9' -> make_var (nip str) (have ^ Char.escaped str.[0])
    | _                   -> (Var have, (String.trim str))

and make_nnot str = match str.[0] with
    | '!'      -> let (item, str) = make_nnot (String.trim (nip str)) in (Nnot1 item, str)
    | 'A'..'Z' -> let (item, str) = make_var  (nip str) (Char.escaped str.[0]) in (Nnot2 item, str)
    | _        -> let (item, str) = make_expr (String.trim (nip str)) in (Nnot3 item, (String.trim (nip str)))

and make_aand str = let (item, str) = make_nnot str in
    let rec make_aand_internal str have = 
        if String.length str == 0 then (have, str)
        else
        match str.[0] with
        | '&' -> let (item, str) = make_nnot (String.trim (nip str)) in make_aand_internal str (And2 (have, item))
        | ')' | '|' | '-' -> (have, str)
        | _   -> failwith "Error1"
    in make_aand_internal str (And1 item)

and make_oor str = let (item, str) = make_aand str in
    let rec make_oor_internal str have = 
        if String.length str == 0 then (have, str)
        else
        match str.[0] with
        | '|' -> let (item, str) = make_aand (String.trim (nip str)) in make_oor_internal str (Or2 (have, item))
        | ')' | '-' -> (have, str)
        | _   -> failwith "Error2"
    in make_oor_internal str (Or1 item)
        
and make_expr str = let (item, str) = make_oor str in
    if String.length str == 0
    then (Exp1 item, str)
    else match str.[0] with
        | '-' -> let (item2, str) = make_expr (String.trim (nip (nip str))) in (Exp2 (item, item2), str)
        | ')' -> (Exp1 item, str) 
        | _   -> failwith "Error3";;
        
let parse_expr str = let (a, b) = make_expr (String.trim str) in a;;

let original_expr = read_line ();;

print_string (print_expr (parse_expr original_expr));;
print_string "\n";;
