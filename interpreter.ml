
(* PARSING INPUT *)
let pop_first_char input = String.sub input 1 ((String.length input) - 1)

let list_to_string f xs = 
    let rec stringify = function 
      |  []         -> ""
      |  [x]        -> (f x)
      |  (x::xs)    -> (f x) ^ ", " ^ stringify xs
    in "[" ^ stringify xs ^ "]"

exception Not_Found of string
exception Ill_Typed of string 
exception Mismatch_Lengths
exception Shadowing of string
exception KindError of string
exception Pattern_Matching_Not_Exhaustive of string 
exception Pattern_Matching_Excessive of string
exception Ill_Pattern of string 
(* 
    Returns the value of a key in an association list
   'a -> ('a * 'b) list -> 'b
*)
let rec lookup k = function 
            | [] -> raise (Not_Found ("Could not find variable '" ^ k ^ "'"))
            | ((k', v)::rest) -> if k' = k then v else lookup k rest

let rec zip xs ys = match xs, ys with
    | [], [] -> []
    | k::ks, v::vs -> (k, v)::zip ks vs
    | _ ,      _       -> raise Mismatch_Lengths

let fst = function (a, b) -> a
let snd = function (a, b) -> b
(* 
   parse takes in string input and returns a list of tokens,
   which is any keyword or string deliminated by a space
*)
let rec parse input = 
    let queue = Queue.create () in
    let rec parse_string input = match input.[0] with 
        | '"' -> ("", pop_first_char input)
        | c -> match parse_string (pop_first_char input) with 
                    | (str, leftover) -> ((String.make 1 c) ^ str, leftover) in
    let rec extract input str = match input with 
        | "" -> ()
        | _  -> match input.[0] with 
                | ' ' | ';' | '(' | ')' | '[' | ']' | ',' | '"' | '{' | '}' -> 
                    let _ = if str <> "" then Queue.add str queue else () in 
                    let _ = if input.[0] <> ' ' then Queue.add (String.make 1 input.[0]) queue else () in 
                    if input.[0] = '"' 
                    then let (str, leftover) = parse_string (pop_first_char input) in
                            let () = Queue.add str queue in 
                            let () = Queue.add (String.make 1 '"') queue in
                            extract leftover ""
                    else extract (pop_first_char input) ""
                | c  ->  if String.length input == 1
                        then Queue.add (str ^ String.make 1 c) queue (* to handle case where last char is not a delimeter *)
                        else extract (pop_first_char input) (str ^ String.make 1 c) 
    in let _ = (extract input "") in 
    queue
    

(* Patterns *)

type exp = LITERAL of value
         | VAR of string 
         | IF of exp * exp * exp
         | APPLY of exp * exp list 
         | LAMBDA of string list * exp
         | LET of def list * exp
         | MATCH of exp list * (pattern * exp) list
         | TUPLE of (exp list)
and value =    STRING of string 
            |  NUMBER of int
            |  BOOLV  of bool
            |  NIL
            |  PAIR of value * value
            |  CLOSURE of exp * (string * value) list
            |  PRIMITIVE of (value list -> value)
            |  TUPLEV of (value list)
            |  TYPECONS of (value list -> value)
            |  PATTERNV of pattern
and def =  LETDEF of string * exp
         | LETREC of string * exp 
         | EXP of exp
and pattern = GENERIC of string
         |  VALUE of value 
         |  PATTERN of string * (pattern list)

(* Types! *)
type ty = TYCON of string | TYVAR of string | CONAPP of ty * ty list
let intty = TYCON "int"
let boolty = TYCON "bool"
let strty = TYCON "string"
let listty t = CONAPP(TYCON "list", [t])
let tuple list = CONAPP (TYCON "tuple", list)
let funtype (args, result) =
  CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result])

type tyscheme = FORALL of string list * ty

let degentype tau = FORALL ([], tau)

let rec def_to_string = function 
         | (LETDEF (x, e)) -> "LETDEF(" ^ x ^ ", " ^ exp_to_string e ^ ")"
         | (LETREC (x, e)) -> "LETREC(" ^ x ^ ", " ^ exp_to_string e ^ ")"
         | (EXP e) -> "EXP(it, " ^ exp_to_string e ^ ")"
    and exp_to_string = function 
        | (LITERAL v) -> value_to_string v
        | (VAR s) -> "VAR(" ^ s ^ ")"
        | (IF (e, e2, e3)) -> "IF(" ^ exp_to_string e ^ ", " ^ exp_to_string e2 ^ ", " ^ exp_to_string e3 ^ ")"
        | (APPLY (f, args)) -> "APPLY(" ^ exp_to_string f ^ ", " ^ list_to_string exp_to_string args ^")"
        | (LAMBDA (xs, e))  -> "LAMBDA(" ^ list_to_string (fun a -> a) xs ^ ", " ^ exp_to_string e ^ ")"
        | (LET (ds, e)) -> "LET(" ^ list_to_string def_to_string ds ^ ", " ^ exp_to_string e ^ ")"
        | (MATCH (exps, cases)) -> "MATCH(" ^ (list_to_string exp_to_string exps) ^ ", " ^ 
                                    (list_to_string 
                                        (fun (p, e) -> "(" ^ (pattern_to_string p) ^ ", " ^ exp_to_string e ^ ")")
                                         cases)
                                    ^ ")"
        | (TUPLE exps) -> "TUPLE(" ^ (list_to_string exp_to_string exps) ^ ")"
    and value_to_string = function 
        | (STRING s) -> "STRING(" ^ s ^ ")"
        | (NUMBER n) -> "NUMBER(" ^ string_of_int n ^ ")"
        | (BOOLV false) -> "BOOLV(false)"
        | (BOOLV true) -> "BOOLV(true)"
        | NIL -> "NIL"
        | (PAIR (e, v)) -> "PAIR(" ^ value_to_string e ^ ", " ^ value_to_string v ^ ")"
        | (CLOSURE (LAMBDA (args, e), rho))  -> "CLOSURE(" ^ exp_to_string (LAMBDA (args, e)) ^ ", rho)"
        | (PRIMITIVE f) -> "PRIM"
        | (TUPLEV l) -> "TUPLEV(" ^ (list_to_string value_to_string l) ^ ")"
        | (TYPECONS f) -> "TYPECONS"
        | (PATTERNV v) -> "PATTERNV(" ^ pattern_to_string v ^ ")"
        | _ -> "ERROR"
and pattern_list_to_string = function 
        | [] -> ""
        | [x] -> pattern_to_string x
        | (x::xs) -> (pattern_to_string x) ^ ", " ^ pattern_list_to_string xs
and pattern_to_string = function 
        | (GENERIC x) -> x
        | PATTERN (name, list) -> 
            (match list with 
            | [] ->  name
            | _  ->  name ^ "(" ^ pattern_list_to_string list ^ ")")
        | VALUE s -> value_to_string s
let list_pattern_pair_string xs = list_to_string (fun (a, b) -> "(" ^ pattern_to_string a ^ ", " ^ pattern_to_string b ^ ")") xs 


(* 
    
    --- Patterns!  ---
    
*)
let get_fun_result = function 
    | CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result]) -> 
        result
    | _ -> raise (Ill_Typed "get_fun_result")

let tuple_pattern list = PATTERN ("TUPLE", list)
let list_patterns = [(PATTERN ("NIL", [])); (PATTERN ("CONS", [tuple_pattern [(GENERIC "_"); (GENERIC "_")]]))]
let val_patterns = [(GENERIC "_")]

let cons a b = PATTERN ("CONS",[(tuple_pattern [a;b])])
let nil = PATTERN ("NIL", [])
let parameters list = PATTERN ("PARAMETERS", list)

(* 
   Given a value, converts it into a pattern

   value -> pattern
*)
let rec value_to_pattern = function 
    | TUPLEV (values) -> tuple_pattern (List.map value_to_pattern values)
    | NIL             -> nil
    | PAIR (v, vs)    -> cons (value_to_pattern v) (value_to_pattern vs)
    | PATTERNV p      -> p
    | (CLOSURE _) 
    | (PRIMITIVE _)   -> raise (Ill_Pattern ("Cannot pattern match on a function."))
    | (TYPECONS s)    -> raise (Ill_Pattern ("Pattern matching on constructor requires application '()'. "))
    | v               -> (VALUE v)

let rec pattern_to_value = function 
    | (VALUE v)   -> v
    | (GENERIC c) -> raise (Ill_Pattern ("Cannot transform a generic" ^ c ^ " to a value"))
    | (PATTERN ("NIL", [])) -> NIL
    | (PATTERN ("TUPLE", ps)) -> TUPLEV (List.map pattern_to_value ps) 
    | (PATTERN ("CONS", ps)) -> 
        (match ps with 
            | [p] -> (match pattern_to_value p with 
                    | (TUPLEV [v; vs]) -> PAIR (v, vs)
                    | _                ->  raise (Ill_Pattern ("Ill formed CONS application.")))
            |  _  -> raise (Ill_Pattern ("Ill formed CONS application.")))
    |  p  -> (PATTERNV p)

(* let _ = print_endline (pattern_to_string (value_to_pattern (PAIR (NUMBER 3, PAIR (NUMBER 1, NIL))))) *)
(* 
  Environment association list of names to list of constructors
*)
let datatypes = [("list", list_patterns); ("int", val_patterns);("bool", val_patterns);
                ("string", val_patterns);("tuple", []); ("parameters", [])]


let gamma = [("NIL", FORALL (["'a"], (funtype ([], listty (TYVAR "'a")))));
            ("CONS",  FORALL (["'a"], (funtype ([(TYVAR "'a"); (listty (TYVAR "'a"))], (listty (TYVAR "'a"))))));
            ("INT", degentype (funtype ([TYCON "int"], TYCON "int")));
            ("STRING", degentype (funtype ([TYCON "string"], TYCON "string")));
            ("TUPLE", degentype (funtype ([], TYCON "tuple")));
            ("PARAMETERS", degentype (funtype ([], TYCON "parameters")))]

let rec double_list_all p list list' =
    match list, list' with 
        | [], [] -> true 
        | (x::xs), (y::ys) -> (p x y) && double_list_all p xs ys
        | _   -> raise (Ill_Pattern ("ill formed constructors when comparing " ^ 
                            (list_to_string pattern_to_string list) ^ " " ^  
                            (list_to_string pattern_to_string list')))

let rec pattern_covers m m' = match m, m' with
            | (GENERIC _), _       -> true
            | (PATTERN (name, list)), (PATTERN (name', list')) ->
                name = name' && (double_list_all pattern_covers list list')
            | (VALUE s), (VALUE s')   -> s = s'
            | _  -> false 
(* 
   Given a list of lists, compute the cartesian product

    ('a list) list -> ('a list) list

*)
let rec cartesian_product input current_list result = 
    match input with 
        | []    -> current_list::result 
        (* val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a list -> 'acc *)
        | x::xs -> List.fold_left 
                    (fun acc a -> cartesian_product xs (a::current_list) acc)
                    result
                    x

let get_name = function 
    | (PATTERN (name, _)) -> name
    | _ -> raise (Ill_Pattern "Tried to get name of generic/value")
(* 
    Given an ideal pattern and a user pattern, splits
    the ideal pattern into more ideal patterns.
   
    pattern -> pattern -> (pattern list) list

    x :: ys covering {x :: y :: zs}
    
*)
let rec equal_pattern p p' = 
    match p, p' with 
        | (GENERIC _), (GENERIC _) -> true
        | (PATTERN (name, list), PATTERN (name', list')) -> 
            name = name' && double_list_all equal_pattern list list'
        | (VALUE s), (VALUE s') -> s = s'
        | _ -> false
(* 
    Given a pattern and a list of patterns,
    returns the duplicated pattern
*)
let rec duplicate_pattern = function 
    | []    -> []
    | x::xs -> if (List.exists (equal_pattern x) xs)
               then [x]
               else  duplicate_pattern xs
(* 
   Given a pattern x and a list of user patterns,
   return the first occurrence of a pattern that covers x
   and the rest of the list.

   'a find_pattern : ('a -> bool) -> ('a list) -> 'a * ('a list)
*)
let list_find f xs = 
    let rec find = function 
        | []    -> raise (Ill_Pattern "Find pattern Issue")
        | y::ys -> if f y
                   then (y, ys)
                   else let (matched, rest) = find ys 
                        in  (matched, y::rest)
    in find xs 
(* 
   Given an ideal and user patterns, returns a list of tuples
    of matched ideal patterns to user patterns,
   and the rest of the user_matches left over.
*)
let find_pairs ideals user_matches = 
    List.fold_left
        (fun (pairs, users, left_over_ideals) i -> 
            if (not (List.exists (pattern_covers i) users)) 
            then (pairs, users, i::left_over_ideals)
            else let (matched, rest) = list_find (pattern_covers i) users in 
                    ((i, matched)::pairs, rest, left_over_ideals)) 
        ([], user_matches, [])
        ideals


(* 
   Given user patterns and the current datatype environment,
   return true if the user patterns are exhaustive, and 
   throw an error otherwise.
*)
(* 
    Algorithm:
    pattern_exhaust ideal user_patterns : pattern list -> pattern list -> pattern list
    *ideal begins as [GENERIC]
    - Match each ideal[i] with the set of user patterns that ideal[i] covers. 
            E.g, create a list of tuples <ideal, patterns>.
    - Take first ideal and first user_pattern, and split by comparing each component of the pattern
      until we see something that is more generic. Take this section of the pattern, compute
      all patterns of the same generality, and rebuild pattern. 
    - Remove equals
    - Recurse on possible patterns and rest of user pattterns
*)
let validate_patterns user_patterns datatypes gamma = 
(* 
    Receives constructor names of the type with a constructor name
    string -> (pattern list)
*)
let rec get_constructors name =
    match lookup name gamma with 
        | FORALL (_, tau) -> 
            (let name = 
                (match (get_fun_result tau) with 
                    | (CONAPP (TYCON n, list)) -> n
                    | TYCON n -> n
                    | _          -> raise (Ill_Typed "Tried to get constructor name of a tyvar"))
            in lookup name datatypes)
in
let rec all_possible_patterns = function 
    | PATTERN (name, list) -> 
        let constructors = List.filter (fun cons -> 
                                            match cons with 
                                                | (PATTERN (name', _)) -> not (name = name')
                                                | _ -> true)
                                    (get_constructors name) in 
        let product = cartesian_product (List.map all_possible_patterns list) [] [] in 
        List.append (List.map (fun list' -> PATTERN (name, List.rev list')) product) constructors
    | VALUE s        -> [(VALUE s); (GENERIC "_");]
    | x              -> [x]
in
(* 
   Splitting the ideal pattern into the generality 
   of the user pattern, by breaking down the ideal 
   pattern into a list of ideal patterns.

   pattern -> pattern -> pattern list

*)
let rec splitting ideal user = (match ideal, user with  
    | (GENERIC _), (PATTERN _) ->  all_possible_patterns user
    | (PATTERN (name, list), PATTERN (name', list')) -> 
        let ideals = map_ideals list list' in 
        let product = cartesian_product ideals [] [] in
        List.map (fun list -> (PATTERN (name, List.rev list))) product
    | (GENERIC _), (GENERIC _) -> [GENERIC "_"]
    | (GENERIC _), (VALUE s)   -> [(VALUE s); (GENERIC "_");]
    | (VALUE _), (VALUE _)     -> []
    | _, _             -> raise (Ill_Pattern ((pattern_to_string ideal) ^ " is more specific than " ^ (pattern_to_string user))))
and
(* Helper function for splitting *)
map_ideals ideal_list user_list = (match ideal_list, user_list with 
    | [], []           -> []
    | (i::is), (u::us) -> splitting i u::(map_ideals is us)
    | _, _             -> raise (Ill_Pattern "Mismatch constructor lists"))
in 

(* 
   Given a list of ideal patterns and user patterns, 
   returns true if the user patterns exhaust the ideal patterns,
   and throws an error otheriwse.

   pattern_exhaust [G] [nil; nil; (cons g g)]
   pairs = [(G, [nil; nil; (cons g g)])]
   left_over_users = []
   left_over_ideals = []

   filtered_pairs = [(G, [nil; nil; (cons g g)])]
   exhuast_pairs = [ ([(cons g g); nil], [nil; nil; (cons g g)])  ]

   pattern_exhaust ([(cons g g); nil], [nil; nil; (cons g g)]) && true
   pairs = [ ((cons g g), (cons g g))  (nil, [nil; nil]) ]
   filtered_pairs = [(nil, [nil; nil])]


*)
let rec pattern_exhaust ideals user_matches = (match (ideals, user_matches) with 
    | (i::is), [(GENERIC _)] -> true
    | [], []       -> true 
    | [], (x::xs) -> raise (Pattern_Matching_Excessive ((pattern_to_string x) ^ " will never be reached."))
    | (x::xs), [] -> raise (Pattern_Matching_Not_Exhaustive ((pattern_to_string x) ^ " is not matched in your patterns."))
    | _, _ -> 
        let (pairs, left_over_users, left_over_ideals) = find_pairs ideals user_matches in
        let left_over_ideals = List.rev left_over_ideals in
        let filtered_non_equals = List.filter (fun (a, b) -> not (equal_pattern a b)) pairs in
        let first_ideal_instances = List.map (fun (a, b) -> b) filtered_non_equals in
        let splitted = List.fold_left (fun acc (i, p) -> List.append (splitting i p) acc) [] filtered_non_equals in
        let new_ideals = List.append left_over_ideals splitted in 
        let new_users = List.append first_ideal_instances left_over_users in
        pattern_exhaust new_ideals new_users)

in match duplicate_pattern user_patterns with 
    | [x] -> raise (Pattern_Matching_Excessive ((pattern_to_string x) ^ " is repeated in your patterns."))
    |  _ -> pattern_exhaust [GENERIC "_"] user_patterns


(* 
  Takes in a queue of strings, and then tokenizes the result

  string queue -> def
*)

let tokenize queue = 
    let tokenWhileDelim delim f = 
        let rec tokenWhile () = 
            let curr = Queue.pop queue in 
            if curr = delim 
                then []
                else 
                    let exp = f curr in 
                    exp::(tokenWhile ())
        in tokenWhile ()
    in 
    let rec tokenList = function
            | "]" -> NIL
            |  x  -> match token x with
                     | (LITERAL v) -> let rest = tokenList (Queue.pop queue) in 
                                      PAIR (v, rest)
                     | _  -> (raise (Ill_Typed "Cannot have non-values in list"))
    and tokenPattern = function 
            | "(" -> let name = Queue.pop queue in 
                    let cons_params = tokenWhileDelim ")" tokenPattern in 
                    let param = PATTERN (name, cons_params) in 
                    param
            | "{" -> tuple_pattern (tokenWhileDelim "}" tokenPattern)
            | "false" -> VALUE (BOOLV false)
            | "true"  -> VALUE (BOOLV true)
            | "\"" -> let p = VALUE (STRING (Queue.pop queue)) in 
                let _   = Queue.pop queue in p
            | x    ->  if (Str.string_match (Str.regexp "[0-9]+") x 0) 
                       then VALUE (NUMBER (int_of_string x))
                       else (GENERIC x)
    and tokenMatchCases () = 
            if (Queue.length queue) <> 0 && (Queue.peek queue) = "|"
            then let _ = Queue.pop queue in (* popping "|" *)
                 let patterns = tokenWhileDelim "=" tokenPattern in
                 let exp  = token (Queue.pop queue) in
                 (parameters patterns, exp)::(tokenMatchCases ())
            else []
    and token = function 
            | "fn"  ->  let names = tokenWhileDelim "->" (fun s -> s) in 
                        let exp  =  token (Queue.pop queue) in 
                        LAMBDA (names, exp)
            | "let" -> let bindings = tokenWhileDelim "in" tokenDef in 
                        let exp = token (Queue.pop queue) in 
                        LET (bindings, exp)
            | "if"  -> let cond = token (Queue.pop queue) in 
                        let exp1 = token (Queue.pop queue) in 
                        let exp2 = token (Queue.pop queue) in 
                        IF (cond, exp1, exp2)
            | "["  -> LITERAL (tokenList (Queue.pop queue))
            | "("  -> let exp = token (Queue.pop queue) in 
                            (match exp with
                                | (VAR _) | (APPLY _) | (LAMBDA _) -> 
                                    (let args = tokenWhileDelim ")" token
                                     in APPLY (exp, args))
                                |  _      -> let _ = Queue.pop queue in exp)
            | "match" -> let exps = tokenWhileDelim "with" token in 
                         MATCH (exps, tokenMatchCases ())
            | "false" -> LITERAL (BOOLV false)
            | "true"  -> LITERAL (BOOLV true)
            | "\"" -> let exp = LITERAL (STRING (Queue.pop queue)) in 
                let _   = Queue.pop queue in exp
            | "{" -> TUPLE (tokenWhileDelim "}" token)
            |  str ->  if (Str.string_match (Str.regexp "[0-9]+") str 0)
                            then LITERAL (NUMBER (int_of_string str))
                            else VAR str 
    and tokenDef = function 
          | "val" -> tokenDef (Queue.pop queue)
          | "rec" -> let name = Queue.pop queue in 
                     let _ = Queue.pop queue in 
                     let keyword = Queue.pop queue in
                     LETREC (name, token keyword)
          |  name -> let _ = Queue.pop queue in LETDEF (name, token (Queue.pop queue))
      in if (Queue.peek queue) = "val" 
         then tokenDef (Queue.pop queue)
         else EXP (token (Queue.pop queue))

(* 
    Given a matched pattern and argument, return 
    an association list of the parameters mapped to 
    their corresponding value

    pattern -> pattern -> (string * value)
*)
let rec extract_parameters p arg = match p, arg with 
    | (VALUE _),   (VALUE _)   -> []
    | (GENERIC x), _ -> [(x, pattern_to_value arg)]
    | (PATTERN (_, ps)), (PATTERN (_, ps')) -> 
        List.fold_left2 (fun acc p p' -> List.append (extract_parameters p p') acc) [] ps ps'
    | _   -> raise (Ill_Pattern "Incorrectly matched patterns")

(* 
   Given an expression and rho, compute the value it returns

   exp -> (string * value) list -> value
*)
let rec eval_exp exp rho = 
    let rec eval = function 
        | (LITERAL v) -> v
        | (VAR x) -> lookup x rho
        | (IF (e1, e2, e3)) -> 
            let bool = eval e1 in 
                (match bool with 
                    | (BOOLV v) -> if v then eval e2 else eval e3
                    | _ -> raise (Ill_Typed "Condition is not a boolean."))
        | (APPLY (f, args)) -> 
            let closure = eval f in
            let values = List.map (fun a -> eval a) args in
                (match closure with 
                    | (CLOSURE (LAMBDA (names, body), copy_rho)) -> 
                        let rho' = List.append (zip names values) copy_rho in 
                        eval_exp body rho'
                    | (PRIMITIVE f) -> f values
                    | (TYPECONS f) -> f values
                    | _ -> raise (Ill_Typed "Cannot apply non-function."))
        | (LAMBDA (names, body)) -> 
            let rho_names = List.map fst rho in 
            let exists = List.exists (fun a -> List.mem a rho_names) names in 
            if exists then raise (Shadowing "LAMBDA") else (CLOSURE (LAMBDA (names, body), rho))
        | (LET (defs, body)) -> 
            let final_rho = List.fold_right (fun d rho' -> snd (eval_def d rho')) defs rho in 
            eval_exp body final_rho
        | (TUPLE exps) -> TUPLEV (List.map eval exps)
        | (MATCH (exps, ps)) -> 
            let valid_lengths = List.for_all (fun (p, e) -> 
                                match p with 
                                | (PATTERN ("PARAMETERS", l)) -> (List.length l) = (List.length exps)
                                | _ -> raise (Ill_Pattern ("Ill formed pattern parameters"))) 
                            ps
            in 
            if (not valid_lengths)
            then raise (Ill_Pattern ("Mismatched lengths in expressions and patterns in match expression."))
            else 
            let values = List.map eval exps in 
            let args = parameters (List.map value_to_pattern values) in 
            let (p, case) = List.find (fun (p, case) -> pattern_covers p args) ps in 
            let env = extract_parameters p args in
            eval_exp case (List.append env rho)
    in eval exp  
(* 
   def -> (string * value) list -> (value * rho)
*)
and eval_def def rho = 
        match def with 
        | LETDEF (name, exp) -> 
            if name <> "it" && List.exists (fun n -> n = name) (List.map fst rho) 
            then raise (Shadowing  "LETDEF")
            else let value = eval_exp exp rho in 
                (value, (name, value)::rho)
        | LETREC (name, exp) ->
            if List.exists (fun n -> n = name) (List.map fst rho) 
            then raise (Shadowing "LETREC")
            else let closure = eval_exp exp rho 
                  in (match closure with 
                        | (CLOSURE (LAMBDA (args, e), c)) -> 
                            let rec rho' = (name, (CLOSURE (LAMBDA (args, e), rho')))::rho in 
                            ((CLOSURE (LAMBDA (args, e), rho')), rho')
                        |  _ -> raise (Ill_Typed "Expression in letrec is not a lambda"))
        | EXP e -> eval_def (LETDEF ("it", e)) rho

let math_primop fn = PRIMITIVE (fun xs -> match xs with
                                    ((NUMBER a)::(NUMBER b)::[]) -> NUMBER (fn a b)
                                    | _ -> raise (Ill_Typed "Cannot apply math operation to non-numbers."))

let bin_primop fn = PRIMITIVE (fun xs -> match xs with 
                                    ((BOOLV a)::(BOOLV b)::[]) -> BOOLV (fn a b)
                                    | _ -> raise (Ill_Typed "Cannot apply boolean operation to non-booleans."))
let initial_rho = 
    [
    ("<", PRIMITIVE (fun xs -> match xs with
                            ((NUMBER a)::(NUMBER b)::[]) -> BOOLV (a < b)
                            | _ -> raise (Ill_Typed "Cannot apply < to non-numbers.")));
    (">", PRIMITIVE (fun xs -> match xs with
                            ((NUMBER a)::(NUMBER b)::[]) -> BOOLV (a > b)
                            | _ -> raise (Ill_Typed "Cannot apply > to non-numbers.")));
    ("=", PRIMITIVE (fun xs -> match xs with 
                                   ((NUMBER a)::(NUMBER b)::[]) -> BOOLV (a = b)
                                 | ((BOOLV a)::(BOOLV b)::[])   -> BOOLV (a = b)
                                 | ((STRING a)::(STRING b)::[]) -> BOOLV (a = b)
                                 | _        -> raise (Ill_Typed "Cannot apply = to non-primitives.")));
    ("-", math_primop (-));
    ("+", math_primop (+));
    ("/", math_primop (/));
    ("*", math_primop ( * ) );
    ("mod", math_primop (mod));
    ("car", PRIMITIVE (fun xs -> match xs with [(PAIR (v, v'))] -> v | _ -> raise (Ill_Typed "Cannot apply car to non-lists")));
    ("cdr", PRIMITIVE (fun xs -> match xs with [(PAIR (v, v'))] -> v' | _ -> raise (Ill_Typed "Cannot apply car to non-lists")));
    ("null?", PRIMITIVE (fun xs -> match xs with [NIL] -> BOOLV true | _ -> BOOLV false));
    ("CONS", TYPECONS (fun arg -> match arg with 
                                | [TUPLEV [v; vs]] -> PAIR (v, vs)
                                | _ -> raise (Ill_Pattern "CONS applied to non-tuple")));
    ("NIL", TYPECONS (fun arg -> match arg with [] -> NIL
                                | _ -> raise (Ill_Pattern "NIL applied to args")))
    ]

let standard_lib = List.fold_left 
                        (fun acc a -> (snd (eval_def (tokenize (parse a)) acc)) ) 
                        initial_rho
                        [
                            "val && = fn a b -> if a b false"; 
                            "val || = fn a b -> if a true b";
                            "val rec exists? = fn f xs -> if (null? xs) false (|| (f (car xs)) (exists? f (cdr xs)))";
                            "val rec all? = fn f xs -> if (null? xs) true (&& (f (car xs)) (all? f (cdr xs)))";
                        ] 

(* 
    interpret_lines runs indefintely, 
   accepting input from stdin and parsing it 
*)
let rec interpret_lines rho = 
    let _ = print_string "> " in 
    let tokens = (parse (read_line ())) in 
    let def = tokenize tokens in 
    let (value, rho') = eval_def def rho in
    let () = print_endline (value_to_string value) in 
    interpret_lines rho'

let () = interpret_lines standard_lib

    