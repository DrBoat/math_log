let nip str = String.sub str 1 ((String.length str) - 1);;
 
type expr = Var of string | Not of expr | And of (expr * expr) | Or of (expr * expr) | Conj of (expr * expr);;
 
let rec print_expr expr = match expr with
    | Var a       -> a
    | Not a       -> "!" ^ (print_expr a) ^ ""
    | And  (a, b) -> "(" ^ (print_expr a) ^ "&" ^ (print_expr b) ^ ")"
    | Or   (a, b) -> "(" ^ (print_expr a) ^ "|" ^ (print_expr b) ^ ")"
    | Conj (a, b) -> "(" ^ (print_expr a) ^ "->" ^ (print_expr b) ^ ")";;
 
let strange = "'";;

let checkOnFence str = String.length str > 2 && str.[0] = '|' && str.[1] = '-';;
 
let rec make_var str have = if String.length str == 0
    then (Var have, str)
    else if String.length str >= String.length strange && String.sub str 0 (String.length strange) = strange
    then make_var (String.sub str (String.length strange) (String.length str - String.length strange)) (have ^ strange)
    else match str.[0] with
    | 'A'..'Z' | '0'..'9' -> make_var (nip str) (have ^ Char.escaped str.[0])
    | _                   -> (Var have, (String.trim str))
 
and make_nnot str = match str.[0] with
    | '!'      -> let (item, str) = make_nnot (String.trim (nip str)) in (Not item, str)
    | 'A'..'Z' -> let (item, str) = make_var  (nip str) (Char.escaped str.[0]) in (item, str)
    | '('      -> let (item, str) = make_expr (String.trim (nip str)) in (item, (String.trim (nip str)))
    | _        -> failwith "Error4"
 
and make_aand str = let (item, str) = make_nnot str in
    let rec make_aand_internal str have =
        if String.length str == 0 || checkOnFence str then (have, str)
        else
        match str.[0] with
        | '&' -> let (item, str) = make_nnot (String.trim (nip str)) in make_aand_internal str (And (have, item))
        | ')' | '|' | '-' | ',' -> (have, str)
        | _   -> failwith "Error1"
    in make_aand_internal str item
 
and make_oor str = let (item, str) = make_aand str in
    let rec make_oor_internal str have =
        if String.length str == 0 || checkOnFence str then (have, str)
        else
        match str.[0] with
        | '|' -> let (item, str) = make_aand (String.trim (nip str)) in make_oor_internal str (Or (have, item))
        | ')' | '-' | ',' -> (have, str)
        | _   -> failwith "Error2"
    in make_oor_internal str item
       
and make_expr str = let (item, str) = make_oor str in
    if String.length str == 0 || checkOnFence str
    then (item, str)
    else match str.[0] with
        | '-' -> let (item2, str) = make_expr (String.trim (nip (nip str))) in (Conj (item, item2), str)
        | ')' | ',' -> (item, str)
        | _   -> failwith "Error3";;
       
let parse_expr str = let (a, _) = make_expr (String.trim str) in a;;
 
let rec make_context str =
    let (first, str) = make_expr (String.trim str) in
    let str = String.trim str in
    match str.[0] with
        | ',' -> let (lst, str) = make_context (String.trim (nip str)) in (first :: lst, str)
        | _   -> ([first], str);;
 
type need = Need of expr list * expr;;
 
let make_first_expr str =
    let (context, str) = 
        if str.[0] = '|' then ([], str) else make_context str in
    let str = String.trim (nip (nip (String.trim str))) in
    let (expr, _) = make_expr str in Need (context, expr);;
   
let (>>=) x f = match x with
    | Some a -> f a
    | None   -> None;;
 
let takeMon x y = match x with
    | Some a -> a
    | None   -> y;;
 
let rNone x y = None;;
let rNone2 a b y = None;;
   
let checkExpr f1 f2 f3 f4 f5 expr = match expr with
    | Var a       -> f1 a
    | Not a       -> f2 a
    | And  (a, b) -> f3 a b
    | Or   (a, b) -> f4 a b
    | Conj (a, b) -> f5 a b;;
let checkVar (proj, setter) expr took = match proj took with
    | None   -> Some (setter took (Some expr))
    | Some a -> if a = expr then Some took else None;;
let checkNot  f = checkExpr rNone f rNone2 rNone2 rNone2;;
let checkAnd  f = checkExpr rNone rNone f rNone2 rNone2;;
let checkOr   f = checkExpr rNone rNone rNone2 f rNone2;;
let checkConj f = checkExpr rNone rNone rNone2 rNone2 f;;
   
let l1 = (fun (a, _, _) -> a), fun (_, b, c) a -> (a, b, c);;
let l2 = (fun (_, a, _) -> a), fun (a, _, c) b -> (a, b, c);;
let l3 = (fun (_, _, a) -> a), fun (a, b, _) c -> (a, b, c);;
                   
let rec print_expr_ expr = match expr with
    | Var a -> let linz = match a with
        | "A" -> l1
        | "B" -> l2
        | _   -> l3 in checkVar linz
    | Not a       -> checkNot  (print_expr_ a)
    | And  (a, b) -> checkAnd  (fun left right x -> print_expr_ a left x >>= (print_expr_ b right))
    | Or   (a, b) -> checkOr   (fun left right x -> print_expr_ a left x >>= (print_expr_ b right))
    | Conj (a, b) -> checkConj (fun left right x -> print_expr_ a left x >>= (print_expr_ b right))
 
let axioms = List.map (fun x -> print_expr_ (parse_expr x))
(       "A -> B -> A" ::
        "(A -> B) -> (A -> B -> C) -> (A -> C)" ::
        "A -> B -> A & B" ::
        "A & B -> A" ::
        "A & B -> B" ::
        "A -> A | B" ::
        "B -> A | B" ::
        "(A -> B) -> (C -> B) -> (A | C -> B)" ::
        "(A -> B) -> (A -> !B) -> !A" ::
        "!!A -> A" (*:: "A -> !A -> B"*) :: []);;

let last_ax = List.map (fun x -> parse_expr x)
(       "(A->(!!A->A))" ::
        "((A->(!!A->A))->(!(!!A->A)->(A->(!!A->A))))" ::
        "(!(!!A->A)->(A->(!!A->A)))" ::
        "(!(!!A->A)->(A->!(!!A->A)))" ::
        "(!(!!A->A)->(!(!!A->A)->!(!!A->A)))" ::
        "(!(!!A->A)->((!(!!A->A)->!(!!A->A))->!(!!A->A)))" ::
        "((!(!!A->A)->(!(!!A->A)->!(!!A->A)))->((!(!!A->A)->((!(!!A->A)->!(!!A->A))->!(!!A->A)))->(!(!!A->A)->!(!!A->A))))" ::
        "((!(!!A->A)->((!(!!A->A)->!(!!A->A))->!(!!A->A)))->(!(!!A->A)->!(!!A->A)))" ::
        "(!(!!A->A)->!(!!A->A))" ::
        "((A->(!!A->A))->((A->!(!!A->A))->!A))" ::
        "(((A->(!!A->A))->((A->!(!!A->A))->!A))->(!(!!A->A)->((A->(!!A->A))->((A->!(!!A->A))->!A))))" ::
        "(!(!!A->A)->((A->(!!A->A))->((A->!(!!A->A))->!A)))" ::
        "((!(!!A->A)->(A->(!!A->A)))->((!(!!A->A)->((A->(!!A->A))->((A->!(!!A->A))->!A)))->(!(!!A->A)->((A->!(!!A->A))->!A))))" ::
        "((!(!!A->A)->((A->(!!A->A))->((A->!(!!A->A))->!A)))->(!(!!A->A)->((A->!(!!A->A))->!A)))" ::
        "(!(!!A->A)->((A->!(!!A->A))->!A))" ::
        "((!(!!A->A)->(A->!(!!A->A)))->((!(!!A->A)->((A->!(!!A->A))->!A))->(!(!!A->A)->!A)))" ::
        "((!(!!A->A)->((A->!(!!A->A))->!A))->(!(!!A->A)->!A))" ::
        "(!(!!A->A)->!A)" ::
        "(!A->(!!A->A))" ::
        "((!A->(!!A->A))->(!(!!A->A)->(!A->(!!A->A))))" ::
        "(!(!!A->A)->(!A->(!!A->A)))" ::
        "((!(!!A->A)->!A)->((!(!!A->A)->(!A->(!!A->A)))->(!(!!A->A)->(!!A->A))))" ::
        "((!(!!A->A)->(!A->(!!A->A)))->(!(!!A->A)->(!!A->A)))" ::
        "(!(!!A->A)->(!!A->A))" ::
        "((!(!!A->A)->(!!A->A))->((!(!!A->A)->!(!!A->A))->!!(!!A->A)))" ::
        "((!(!!A->A)->!(!!A->A))->!!(!!A->A))" ::
        "!!(!!A->A)" :: []);;

let modus_ponens = List.map (fun x -> parse_expr x)
(       "(!B->((A->B)->!B))" ::
        "(!B->(A->!B))" ::
        "((!B->(A->!B))->(!B->(!B->(A->!B))))" :: 
        "(!B->(!B->(A->!B)))" :: 
        "((!B->(A->!B))->((A->B)->(!B->(A->!B))))" :: 
        "(((!B->(A->!B))->((A->B)->(!B->(A->!B))))->(!B->((!B->(A->!B))->((A->B)->(!B->(A->!B))))))" :: 
        "(!B->((!B->(A->!B))->((A->B)->(!B->(A->!B)))))" :: 
        "((!B->(!B->(A->!B)))->((!B->((!B->(A->!B))->((A->B)->(!B->(A->!B)))))->(!B->((A->B)->(!B->(A->!B))))))" :: 
        "((!B->((!B->(A->!B))->((A->B)->(!B->(A->!B)))))->(!B->((A->B)->(!B->(A->!B)))))" :: 
        "(!B->((A->B)->(!B->(A->!B))))" :: 
        "(((A->B)->!B)->(((A->B)->(!B->(A->!B)))->((A->B)->(A->!B))))" :: 
        "((((A->B)->!B)->(((A->B)->(!B->(A->!B)))->((A->B)->(A->!B))))->(!B->(((A->B)->!B)->(((A->B)->(!B->(A->!B)))->((A->B)->(A->!B))))))" :: 
        "(!B->(((A->B)->!B)->(((A->B)->(!B->(A->!B)))->((A->B)->(A->!B)))))" :: 
        "((!B->((A->B)->!B))->((!B->(((A->B)->!B)->(((A->B)->(!B->(A->!B)))->((A->B)->(A->!B)))))->(!B->(((A->B)->(!B->(A->!B)))->((A->B)->(A->!B))))))" :: 
        "((!B->(((A->B)->!B)->(((A->B)->(!B->(A->!B)))->((A->B)->(A->!B)))))->(!B->(((A->B)->(!B->(A->!B)))->((A->B)->(A->!B)))))" :: 
        "(!B->(((A->B)->(!B->(A->!B)))->((A->B)->(A->!B))))" :: 
        "((!B->((A->B)->(!B->(A->!B))))->((!B->(((A->B)->(!B->(A->!B)))->((A->B)->(A->!B))))->(!B->((A->B)->(A->!B)))))" :: 
        "((!B->(((A->B)->(!B->(A->!B)))->((A->B)->(A->!B))))->(!B->((A->B)->(A->!B))))" :: 
        "(!B->((A->B)->(A->!B)))" :: 
        "((A->B)->((A->!B)->!A))" :: 
        "(((A->B)->((A->!B)->!A))->(!B->((A->B)->((A->!B)->!A))))" :: 
        "(!B->((A->B)->((A->!B)->!A)))" :: 
        "(((A->B)->(A->!B))->(((A->B)->((A->!B)->!A))->((A->B)->!A)))" :: 
        "((((A->B)->(A->!B))->(((A->B)->((A->!B)->!A))->((A->B)->!A)))->(!B->(((A->B)->(A->!B))->(((A->B)->((A->!B)->!A))->((A->B)->!A)))))" :: 
        "(!B->(((A->B)->(A->!B))->(((A->B)->((A->!B)->!A))->((A->B)->!A))))" :: 
        "((!B->((A->B)->(A->!B)))->((!B->(((A->B)->(A->!B))->(((A->B)->((A->!B)->!A))->((A->B)->!A))))->(!B->(((A->B)->((A->!B)->!A))->((A->B)->!A)))))" :: 
        "((!B->(((A->B)->(A->!B))->(((A->B)->((A->!B)->!A))->((A->B)->!A))))->(!B->(((A->B)->((A->!B)->!A))->((A->B)->!A))))" :: 
        "(!B->(((A->B)->((A->!B)->!A))->((A->B)->!A)))" :: 
        "((!B->((A->B)->((A->!B)->!A)))->((!B->(((A->B)->((A->!B)->!A))->((A->B)->!A)))->(!B->((A->B)->!A))))" :: 
        "((!B->(((A->B)->((A->!B)->!A))->((A->B)->!A)))->(!B->((A->B)->!A)))" :: 
        "(!B->((A->B)->!A))" :: 
        "!!A" :: 
        "(!!A->(!B->!!A))" :: 
        "(!B->!!A)" :: 
        "(!!A->((A->B)->!!A))" :: 
        "((!!A->((A->B)->!!A))->(!B->(!!A->((A->B)->!!A))))" :: 
        "(!B->(!!A->((A->B)->!!A)))" :: 
        "((!B->!!A)->((!B->(!!A->((A->B)->!!A)))->(!B->((A->B)->!!A))))" :: 
        "((!B->(!!A->((A->B)->!!A)))->(!B->((A->B)->!!A)))" :: 
        "(!B->((A->B)->!!A))" :: 
        "(!A->(!!A->!(A->B)))" :: 
        "((!A->(!!A->!(A->B)))->(!B->(!A->(!!A->!(A->B)))))" :: 
        "(!B->(!A->(!!A->!(A->B))))" :: 
        "((!A->(!!A->!(A->B)))->((A->B)->(!A->(!!A->!(A->B)))))" :: 
        "(((!A->(!!A->!(A->B)))->((A->B)->(!A->(!!A->!(A->B)))))->(!B->((!A->(!!A->!(A->B)))->((A->B)->(!A->(!!A->!(A->B)))))))" :: 
        "(!B->((!A->(!!A->!(A->B)))->((A->B)->(!A->(!!A->!(A->B))))))" :: 
        "((!B->(!A->(!!A->!(A->B))))->((!B->((!A->(!!A->!(A->B)))->((A->B)->(!A->(!!A->!(A->B))))))->(!B->((A->B)->(!A->(!!A->!(A->B)))))))" :: 
        "((!B->((!A->(!!A->!(A->B)))->((A->B)->(!A->(!!A->!(A->B))))))->(!B->((A->B)->(!A->(!!A->!(A->B))))))" :: 
        "(!B->((A->B)->(!A->(!!A->!(A->B)))))" :: 
        "(((A->B)->!A)->(((A->B)->(!A->(!!A->!(A->B))))->((A->B)->(!!A->!(A->B)))))" :: 
        "((((A->B)->!A)->(((A->B)->(!A->(!!A->!(A->B))))->((A->B)->(!!A->!(A->B)))))->(!B->(((A->B)->!A)->(((A->B)->(!A->(!!A->!(A->B))))->((A->B)->(!!A->!(A->B)))))))" :: 
        "(!B->(((A->B)->!A)->(((A->B)->(!A->(!!A->!(A->B))))->((A->B)->(!!A->!(A->B))))))" :: 
        "((!B->((A->B)->!A))->((!B->(((A->B)->!A)->(((A->B)->(!A->(!!A->!(A->B))))->((A->B)->(!!A->!(A->B))))))->(!B->(((A->B)->(!A->(!!A->!(A->B))))->((A->B)->(!!A->!(A->B)))))))" :: 
        "((!B->(((A->B)->!A)->(((A->B)->(!A->(!!A->!(A->B))))->((A->B)->(!!A->!(A->B))))))->(!B->(((A->B)->(!A->(!!A->!(A->B))))->((A->B)->(!!A->!(A->B))))))" :: 
        "(!B->(((A->B)->(!A->(!!A->!(A->B))))->((A->B)->(!!A->!(A->B)))))" :: 
        "((!B->((A->B)->(!A->(!!A->!(A->B)))))->((!B->(((A->B)->(!A->(!!A->!(A->B))))->((A->B)->(!!A->!(A->B)))))->(!B->((A->B)->(!!A->!(A->B))))))" :: 
        "((!B->(((A->B)->(!A->(!!A->!(A->B))))->((A->B)->(!!A->!(A->B)))))->(!B->((A->B)->(!!A->!(A->B)))))" :: 
        "(!B->((A->B)->(!!A->!(A->B))))" :: 
        "(((A->B)->!!A)->(((A->B)->(!!A->!(A->B)))->((A->B)->!(A->B))))" :: 
        "((((A->B)->!!A)->(((A->B)->(!!A->!(A->B)))->((A->B)->!(A->B))))->(!B->(((A->B)->!!A)->(((A->B)->(!!A->!(A->B)))->((A->B)->!(A->B))))))" :: 
        "(!B->(((A->B)->!!A)->(((A->B)->(!!A->!(A->B)))->((A->B)->!(A->B)))))" :: 
        "((!B->((A->B)->!!A))->((!B->(((A->B)->!!A)->(((A->B)->(!!A->!(A->B)))->((A->B)->!(A->B)))))->(!B->(((A->B)->(!!A->!(A->B)))->((A->B)->!(A->B))))))" :: 
        "((!B->(((A->B)->!!A)->(((A->B)->(!!A->!(A->B)))->((A->B)->!(A->B)))))->(!B->(((A->B)->(!!A->!(A->B)))->((A->B)->!(A->B)))))" :: 
        "(!B->(((A->B)->(!!A->!(A->B)))->((A->B)->!(A->B))))" :: 
        "((!B->((A->B)->(!!A->!(A->B))))->((!B->(((A->B)->(!!A->!(A->B)))->((A->B)->!(A->B))))->(!B->((A->B)->!(A->B)))))" :: 
        "((!B->(((A->B)->(!!A->!(A->B)))->((A->B)->!(A->B))))->(!B->((A->B)->!(A->B))))" :: 
        "(!B->((A->B)->!(A->B)))" :: 
        "!!(A->B)" :: 
        "(!!(A->B)->(!B->!!(A->B)))" :: 
        "(!B->!!(A->B))" :: 
        "(!!(A->B)->((A->B)->!!(A->B)))" :: 
        "((!!(A->B)->((A->B)->!!(A->B)))->(!B->(!!(A->B)->((A->B)->!!(A->B)))))" :: 
        "(!B->(!!(A->B)->((A->B)->!!(A->B))))" :: 
        "((!B->!!(A->B))->((!B->(!!(A->B)->((A->B)->!!(A->B))))->(!B->((A->B)->!!(A->B)))))" :: 
        "((!B->(!!(A->B)->((A->B)->!!(A->B))))->(!B->((A->B)->!!(A->B))))" :: 
        "(!B->((A->B)->!!(A->B)))" :: 
        "(((A->B)->!(A->B))->(((A->B)->!!(A->B))->!(A->B)))" :: 
        "((((A->B)->!(A->B))->(((A->B)->!!(A->B))->!(A->B)))->(!B->(((A->B)->!(A->B))->(((A->B)->!!(A->B))->!(A->B)))))" :: 
        "(!B->(((A->B)->!(A->B))->(((A->B)->!!(A->B))->!(A->B))))" :: 
        "((!B->((A->B)->!(A->B)))->((!B->(((A->B)->!(A->B))->(((A->B)->!!(A->B))->!(A->B))))->(!B->(((A->B)->!!(A->B))->!(A->B)))))" :: 
        "((!B->(((A->B)->!(A->B))->(((A->B)->!!(A->B))->!(A->B))))->(!B->(((A->B)->!!(A->B))->!(A->B))))" :: 
        "(!B->(((A->B)->!!(A->B))->!(A->B)))" :: 
        "((!B->((A->B)->!!(A->B)))->((!B->(((A->B)->!!(A->B))->!(A->B)))->(!B->!(A->B))))" :: 
        "((!B->(((A->B)->!!(A->B))->!(A->B)))->(!B->!(A->B)))" :: 
        "(!B->!(A->B))" :: 
        "(!(A->B)->(!!(A->B)->!A))" :: 
        "((!(A->B)->(!!(A->B)->!A))->(!B->(!(A->B)->(!!(A->B)->!A))))" :: 
        "(!B->(!(A->B)->(!!(A->B)->!A)))" :: 
        "((!B->!(A->B))->((!B->(!(A->B)->(!!(A->B)->!A)))->(!B->(!!(A->B)->!A))))" :: 
        "((!B->(!(A->B)->(!!(A->B)->!A)))->(!B->(!!(A->B)->!A)))" :: 
        "(!B->(!!(A->B)->!A))" :: 
        "((!B->!!(A->B))->((!B->(!!(A->B)->!A))->(!B->!A)))" :: 
        "((!B->(!!(A->B)->!A))->(!B->!A))" :: 
        "(!B->!A)" :: 
        "((!B->!A)->((!B->!!A)->!!B))" :: 
        "((!B->!!A)->!!B)" :: 
        "!!B" :: []);;

let ax = List.map (fun x -> parse_expr x)
(       "A" ::
        "(A -> (!A -> A))" ::
        "(!A -> A)" ::
        "(!A -> (!A -> !A))" ::
        "((!A -> (!A -> !A)) -> ((!A -> ((!A -> !A) -> !A)) -> (!A -> !A)))" ::
        "((!A -> ((!A -> !A) -> !A)) -> (!A -> !A))" ::
        "(!A -> ((!A -> !A) -> !A))" ::
        "(!A -> !A)" ::
        "((!A -> A) -> ((!A -> !A) -> !!A))" ::
        "((!A -> !A) -> !!A)" ::
        "!!A" :: []);;
        
module ExprMap = Map.Make(struct type t = expr let compare = compare end);;
module ExprSet = Set.Make(struct type t = expr let compare = compare end);;
module StringMap = Map.Make(String);;

let rec substitute expr map = match expr with
    | Var a -> StringMap.find a map
    | Not a -> Not (substitute a map)
    | And  (a, b) -> And  (substitute a map, substitute b map)
    | Or   (a, b) -> Or   (substitute a map, substitute b map)
    | Conj (a, b) -> Conj (substitute a map, substitute b map);;
        
let list_find_opt f l = try Some (List   .find f l) with _ -> None;;
let map_find_opt  k m = try Some (ExprMap.find k m) with _ -> None;;
 
let checkAxioms to_check = let rec func lst = match lst with
    | None :: rem_ -> func rem_
    | Some a :: _  -> Some a
    | _            -> None in
    func (List.mapi (fun ind chain -> chain to_check (None, None, None) >>= (fun _ -> Some ind)) axioms);;
 
type node = Axiom of (expr * int) | MP of (expr * node * node) | Context of (expr * int);;

let add_nonexisting key value mp = if ExprMap.mem key mp then mp else ExprMap.add key value mp;;
 
let checkEverything context need evidence =
    let contextMap = List.fold_left (fun mp (x, ind) -> add_nonexisting x ind mp) ExprMap.empty (List.mapi (fun ind x -> (x, ind)) context) in
    let rec checkStepByStep alreadyHadMap possibleMap evidenceMap lst =
        match lst with
            | [] -> None
            | now :: rem_list ->
        let the_node = match map_find_opt now possibleMap with
        | Some the_node -> Some the_node
        | None -> match checkAxioms now with
        | Some ind -> Some (Axiom (now, ind)) 
        | None -> match map_find_opt now contextMap with
        | Some ind -> Some (Context (now, ind))
        | None -> None in
        if now = need && (List.length rem_list = 0)
        then the_node
        else
        the_node >>= fun the_node ->
            let to_add = ExprMap.fold (fun _expr _node have -> (_expr, MP(_expr, _node, the_node)) :: have) (takeMon (map_find_opt now evidenceMap) ExprMap.empty) [] in
            let evidenceMap = ExprMap.remove now evidenceMap in
            let (smth_to_add, new_evidenceMap) = match now with
                | Conj (a, b) -> (match map_find_opt a alreadyHadMap with
                    | Some the_node1 -> ([(b, MP (b, the_node, the_node1))], evidenceMap)
                    | _ -> ([], ExprMap.add a (add_nonexisting b the_node (takeMon (map_find_opt a evidenceMap) ExprMap.empty)) evidenceMap))
                | _ -> ([], evidenceMap) in
            let new_list = (now, the_node) :: List.concat (smth_to_add :: to_add :: []) in
            let new_possibleMap = List.fold_right (fun (x, y) mp -> add_nonexisting x y mp) new_list possibleMap in
            let new_alreadyHadMap = add_nonexisting now the_node alreadyHadMap in
            checkStepByStep new_alreadyHadMap new_possibleMap new_evidenceMap rem_list in
    checkStepByStep ExprMap.empty ExprMap.empty ExprMap.empty evidence;;
        
let rec generateNodeList node st = match node with
    | Axiom   (expr_, _) | Context (expr_, _) -> if ExprSet.mem expr_ st then ([], st) else ([node], ExprSet.add expr_ st)
    | MP (expr_, node1, node2) -> 
        if ExprSet.mem expr_ st 
        then ([], st)
        else
        let (result1, st) = generateNodeList node1 st in
        let (result2, st) = generateNodeList node2 st in
        (node :: List.concat (result1 :: result2 :: []), ExprSet.add expr_ st);;
        
let extractExpr node = match node with
    | Axiom (expr_, _) | Context (expr_, _) | MP (expr_, _, _) -> expr_;;
        
let printNode the_node toSort = 
    let (init_list, _) = generateNodeList the_node ExprSet.empty in
    let lst = List.sort (fun x y -> ExprMap.find (extractExpr x) toSort - ExprMap.find (extractExpr y) toSort) init_list in
    let mp  = List.fold_left (fun mp (num, x) -> add_nonexisting (extractExpr x) num mp) ExprMap.empty (List.mapi (fun num x -> (num + 1, x)) lst) in 
    let strings = List.map (fun x -> match x with
    | Axiom   (expr_, num) -> 
        if num != 9 
        then
            let map = StringMap.add "A" expr_ StringMap.empty in
                String.concat "\n" (List.map (fun y -> print_expr (substitute y map)) ax)
        else
            (match expr_ with
            | Conj (_, b) -> 
                let map = StringMap.add "A" b StringMap.empty in
                    String.concat "\n" (List.map (fun y -> print_expr (substitute y map)) last_ax)
            | _ -> failwith "It is not 10 axiom!")
    | Context (expr_, num) -> 
        let map = StringMap.add "A" expr_ StringMap.empty in
            String.concat "\n" (List.map (fun y -> print_expr (substitute y map)) ax)
    | MP (expr_, node1, node2) -> 
        let map = StringMap.add "B" expr_ (StringMap.add "A" (extractExpr node2) StringMap.empty) in
            String.concat "\n" (List.map (fun y -> print_expr (substitute y map)) modus_ponens)
        ) lst in
    String.concat "\n" strings;;
        
let make_evidence lines = match lines with
    | []                        -> failwith "Error blyat!"
    | first_line :: other_lines ->
        let Need (context, expr) = make_first_expr first_line in
        let other_expr = List.map parse_expr other_lines in
        let toSort = List.fold_left (fun mp (num, x) -> add_nonexisting x num mp) ExprMap.empty (List.mapi (fun num x -> (num, x)) other_expr) in
        match checkEverything context expr other_expr with
            | None   -> "Proof is incorrect"
            | Some a -> String.concat ", " (List.map print_expr context) ^ "|- " ^ (print_expr (Not (Not expr))) ^ "\n" ^ printNode a toSort;;
        
let rec mainImpl () =
    try let cur = input_line stdin in cur :: mainImpl () with _ -> [];;
    
print_string (make_evidence (mainImpl ()));;