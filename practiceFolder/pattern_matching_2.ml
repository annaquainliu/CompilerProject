exception Pattern_Matching_Not_Exhaustive 
exception Pattern_Matching_Excessive 
exception Ill_Pattern of string
exception Ill_Typed of string
exception Not_Found of string

let rec lookup k = function 
            | [] -> raise (Not_Found ("Could not find variable '" ^ k ^ "'"))
            | ((k', v)::rest) -> if k' = k then v else lookup k rest

type exp = LITERAL of value
         | VAR of string 
         | IF of exp * exp * exp
         | APPLY of exp * exp list 
         | LAMBDA of string list * exp
         | LET of def list * exp
and value =    STRING of string 
            |  NUMBER of int
            |  BOOLV  of bool
            |  NIL
            |  PAIR of value * value
            |  CLOSURE of exp * (string * value) list
            |  PRIMITIVE of (value list -> value)
            | CONSTRUCTOR
and def =  LETDEF of string * exp
         | LETREC of string * exp 
         | EXP of exp


type ty = TYCON of string | TYVAR of string | CONAPP of ty * ty list
let intty = TYCON "int"
let boolty = TYCON "bool"
let strty = TYCON "string"
let listty t = CONAPP(TYCON "list", [t])
let tuple list = CONAPP (TYCON "tuple", list)
let funtype (args, result) =
  CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result])


let get_fun_args = function 
    | CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result]) -> 
        args
    | _ -> raise (Ill_Typed "get_fun_args")

let get_fun_result = function 
    | CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result]) -> 
        result
    | _ -> raise (Ill_Typed "get_fun_result")

let list_to_string f xs = 
  let rec stringify = function 
    |  []         -> ""
    |  [x]        -> (f x)
    |  (x::xs)    -> (f x) ^ ", " ^ stringify xs
  in "[" ^ stringify xs ^ "]"

type pattern = GENERIC
            |  PATTERN of string * (pattern list)


let rec pattern_to_string = function 
            | GENERIC -> "GENERIC"
            | PATTERN (name, list) -> name ^ "(" ^ list_to_string pattern_to_string list ^ ")"

let get_tycon_name = function 
    | (TYCON name) -> name 
    | _ -> raise (Ill_Typed "get_tycon_name")

let is_generic = function 
            | GENERIC -> true 
            | _ -> false


let matched_pattern p p' = match p, p' with 
  | (PATTERN (name, _)), (PATTERN (name', _)) -> name = name' 
  |  _, GENERIC -> false
  | _ -> raise (Ill_Pattern "to matched pattern p cannot be generic")

let cons a b = PATTERN ("CONS", [a;b])
let nil = PATTERN ("NIL", [])
let list_patterns = [(PATTERN ("NIL", [])); (PATTERN ("CONS", [GENERIC; GENERIC]))]
let int_patterns = [GENERIC]
let bool_patterns = [GENERIC]
let string_patterns = [GENERIC]
let excrement_patterns = [(PATTERN ("POO", [])); (PATTERN ("PEE", []))]
let toilet_patterns = [(PATTERN ("TOILET", [GENERIC; GENERIC;]))]
let hello_patterns = [(PATTERN ("GREET", [GENERIC; GENERIC])); (PATTERN ("BYE", [GENERIC]))]

let datatypes = [("list", list_patterns); ("int", int_patterns);("bool", bool_patterns);("string", string_patterns); 
                    ("toilet", toilet_patterns); ("excrement", excrement_patterns); ("hello", hello_patterns)]

let gamma = [("TOILET", (funtype ([tuple [TYCON "excrement"; TYCON "excrement"]], TYCON "toilet"))); 
                ("PEE", (funtype ([], TYCON "excrement"))); 
                ("POO", (funtype ([], TYCON "excrement"))); 
                ("GREET", (funtype ([tuple [TYCON "hello"; TYCON "hello"]], TYCON "hello")));
                ("BYE", (funtype ([TYCON "int"], TYCON "hello")));
                ("NIL", (funtype ([], TYCON "list")));
                ("CONS", (funtype ([TYVAR "'a"], TYCON "list")));
                ("INT", (funtype ([TYCON "int"], TYCON "int")))]
(* 
    val hello = TOILET (POO, PEE, POO)
    Gamma{ hello |--> TYCON ("toilet")}
*)
let rho = [("TOILET", CONSTRUCTOR)]

let get_list = function 
        | PATTERN (name, list) -> list 
        | _  -> raise (Ill_Pattern "Cannot get list of a non-pattern")

let rec double_list_all p list list' =
    match list, list' with 
        | [], [] -> true 
        | (x::xs), (y::ys) -> (p x y) && double_list_all p xs ys
        | _   -> raise (Ill_Pattern "ill formed constructors")

let rec double_list_exists p list list' =
    match list, list' with 
        | [], [] -> false
        | (x::xs), (y::ys) -> (p x y) || double_list_all p xs ys
        | _   -> raise (Ill_Pattern "ill formed constructors")
(* 
    returns true if m covers m' (or is more general than m'), and false otherwise

    Returns true if m encompasses m'
*)
let rec pattern_covers m m' = match m, m' with
            | GENERIC, _       -> true
            | (PATTERN (name, list)), (PATTERN (name', list')) ->
                name = name' && (double_list_all pattern_covers list list')
            | _   -> false
(*
   Given two patterns, determines if m is more specific than m'

    E.g. If m is more nested than m'.

*)
let rec more_specific m m' = match m, m' with 
            | (PATTERN _, GENERIC) -> true
            | (PATTERN (name, list)), (PATTERN (name', list')) ->
                (* if (name = name')
                then double_list_all more_specific list list'
                else  *)
                (match (list, list') with 
                    | [], [] -> false (* equal specificness *)
                    | [], _ -> (not (List.exists (fun a -> (not (is_generic a))) list'))
                    | _, [] -> (not (List.exists (fun a -> (not (is_generic a))) list')) (* equal specificness *)
                    | _     -> double_list_exists more_specific list list')
            | _, _ -> false

(* let _ = print_endline (string_of_bool (more_specific nil (cons nil nil))) *)
(* let _ = print_endline (string_of_bool (more_specific (cons GENERIC GENERIC) nil)) *)
(* let _ = print_endline (string_of_bool (more_specific (cons (cons GENERIC GENERIC) nil) nil)) *)
(* let _ = print_endline (string_of_bool (more_specific (cons GENERIC nil) nil)) *)
(* let _ = print_endline (string_of_bool (more_specific (cons (PATTERN ("INT", [])) GENERIC) (cons GENERIC GENERIC))) *)
(* let _ = print_endline (string_of_bool (more_specific (cons (PATTERN ("INT", [])) GENERIC) nil)) *)
(* let _ = print_endline (string_of_bool (more_specific GENERIC (cons GENERIC GENERIC))) *)

let rec equal_pattern p p' = 
    match p, p' with 
        | GENERIC, GENERIC -> true
        | (PATTERN (name, list), PATTERN (name', list')) -> name = name' && double_list_all equal_pattern list list'
        | _ -> false
(* 
   Given a list of user patterns, and the cartesian product to_match 
   (exhaustive set)
   the most specific pattern, returns true if ps exhuasts the
   product, and false otherwise
*)
let rec pattern_exhaust user_patterns to_match =
        match exhausted_patterns user_patterns to_match with 
            |  [],    [] -> true 
            |  x::xs, [] -> raise Pattern_Matching_Excessive 
            |  [], x::xs -> raise Pattern_Matching_Not_Exhaustive
            |  _         -> raise Pattern_Matching_Excessive 
(* 
   Returns a tuple of the remaining user_patterns and to_match patterns
*)
and exhausted_patterns user_patterns to_match = match user_patterns with
    | []    -> ([], to_match) 
    (* if there are no more remaining patterns to match, but there are still user patterns, 
        then excessive pattern matching *)
    | p::ps -> if (to_match = []) 
                then raise Pattern_Matching_Excessive  
                else  let remaining = (break_down_patterns to_match p) in
                       if (List.length remaining) = (List.length to_match)
                       then 
                       let (user_p, matches) = exhausted_patterns ps remaining in 
                            (p::user_p, matches)
                        else exhausted_patterns ps remaining

(* 
   Runs pattern_exhaust between one pattern and every pattern in 
   to compute the remaining set

    pattern -> (pattern list) -> (pattern list)
*)
and break_down_patterns to_match pattern =
    let rec break_down = function 
        | [] -> []
        | (p::ps) ->  
            if (pattern_covers pattern p)
            then break_down ps
            else p::break_down ps
    in break_down to_match 
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
(* 
    Receives constructor names of the type with a constructor name
    string -> (pattern list)
*)
let rec get_constructors name =
    let tau = lookup name gamma in 
    lookup (get_tycon_name (get_fun_result tau)) datatypes 

(* 

    Given a pattern, compute all the possible patterns
    that would exhaust the type on the same level
    of generality.
    
    pattern -> (pattern list)
*)
let rec all_possible_patterns = function 
    | PATTERN (name, list) -> 
        let constructors = List.filter (fun cons -> 
                                            match cons with 
                                                | GENERIC -> true 
                                                | (PATTERN (name', _)) -> not (name = name'))
                                    (get_constructors name) in 
        let product = cartesian_product (List.map all_possible_patterns list) [] [] in 

        List.append (List.map (fun list' -> PATTERN (name, List.rev list')) product) constructors
    | GENERIC              -> [GENERIC]

(* 
    Given a list of user_patterns, throws a runtime error if 
    they are not exhaustive.
 *)
let validate_patterns user_patterns = 
    let most_specific = List.fold_left (fun acc p -> (if (more_specific p acc) then p else acc)) (List.hd user_patterns) (List.tl user_patterns) in 
    let product = all_possible_patterns most_specific in
    let _ = print_endline ("most specific " ^ pattern_to_string most_specific) in
    let _ = print_endline ("product from most specific: " ^ list_to_string pattern_to_string product) in
    pattern_exhaust user_patterns product

(* let _ = print_endline (string_of_bool (validate_patterns [PATTERN ("CONS", [GENERIC; GENERIC]); PATTERN ("NIL", [])]))  *)
(* let _ = print_endline (string_of_bool (validate_patterns [PATTERN ("CONS", [GENERIC; GENERIC])])) *)
(* 
   x::(y::ys)
   x::[]
   []
*)
(* let _ = print_endline (string_of_bool (validate_patterns [nil; (cons GENERIC (cons GENERIC GENERIC)); (cons GENERIC nil)])) *)

(* 
   []
   x::[]
   x::xs

*)
(* let _ = print_endline (string_of_bool (validate_patterns [nil; (cons GENERIC nil); (cons GENERIC GENERIC)])) *)

(* 
   x::xs
   x::[]
   []

   should be excessive!
*)
(* let _ = print_endline (string_of_bool (validate_patterns [(cons GENERIC GENERIC); (cons GENERIC nil); nil])) *)

(* 
    []::[]
    x::xs
    []
*)
(* let _ = print_endline (string_of_bool (validate_patterns [(cons nil nil); (cons GENERIC GENERIC); nil])) *)

(* 
   TOILET (POO, GENERIC)
   TOILET (PEE, GENERIC)
*)
(* let _ = print_endline (string_of_bool (validate_patterns 
                                        [(PATTERN ("TOILET", [PATTERN ("POO", []); GENERIC])); 
                                            (PATTERN ("TOILET", [PATTERN ("PEE", []); GENERIC]));])) *)
(* let _ = print_endline (string_of_bool (validate_patterns
                                        [(PATTERN ("TOILET", [PATTERN ("POO", []);PATTERN ("PEE", [])]));
                                         (PATTERN ("TOILET", [PATTERN ("PEE", []);PATTERN ("PEE", [])]));
                                         (PATTERN ("TOILET", [PATTERN ("PEE", []);PATTERN ("POO", [])]));
                                         (PATTERN ("TOILET", [PATTERN ("POO", []);PATTERN ("POO", [])]))])) *)
(* 
   
(x::xs)::(y::ys)
[]::[]
[]::xs
(x::xs)::[]
[]
*)
(* let _ = print_endline (string_of_bool (validate_patterns 
                                        [(cons (cons GENERIC GENERIC) (cons GENERIC GENERIC));
                                         (cons nil nil);
                                         (cons nil (cons GENERIC GENERIC));
                                         (cons (cons GENERIC GENERIC) nil);
                                         nil])) *)
(* 
   3::xs
   []
   Should NOT be exhaustive
*)
(* let _ = print_endline (string_of_bool (validate_patterns
                                        [(cons (PATTERN ("INT", [])) GENERIC);
                                         nil])) *)
(* 
   Should NOT be exhaustive
*)
(* let _ = print_endline (string_of_bool (validate_patterns
                                         [(cons (PATTERN ("TOILET", [PATTERN ("POO", []); PATTERN ("PEE", [])])) GENERIC);
                                          nil])) *)
(* TESTING FOR ALL_POSSIBLE PATTERNS! *)
(* let _ = print_endline (list_to_string pattern_to_string (all_possible_patterns (PATTERN ("TOILET", [PATTERN ("PEE", []); PATTERN ("POO", [])])))) *)
(* let _ = print_endline (list_to_string pattern_to_string 
                        (all_possible_patterns 
                            (PATTERN ("GREET", [PATTERN ("GREET", [PATTERN ("BYE", [GENERIC]); PATTERN ("BYE", [GENERIC])]); PATTERN ("BYE", [GENERIC])])))) *)
(* let _ = print_endline (list_to_string pattern_to_string 
                        (all_possible_patterns 
                            (PATTERN ("GREET", [(PATTERN ("BYE", [GENERIC])); GENERIC])))) *)
(* 
   []::ys
*)
(* let _ = print_endline (list_to_string pattern_to_string
                        (all_possible_patterns
                            (PATTERN ("CONS", [(PATTERN ("NIL", [])); GENERIC])))) *)
(* 
   y::[]
   -->
   x::(y::ys)
   y::[]
   []
*)
(* let _ = print_endline (list_to_string pattern_to_string
                        (all_possible_patterns
                            (PATTERN ("CONS", [GENERIC; (PATTERN ("NIL", []))])))) *)
(* 
   3::xs
    -->
    INT::xs
    y::ys
    []
*)
(* let _ = print_endline (list_to_string pattern_to_string
                        (all_possible_patterns
                            (PATTERN ("CONS", [(PATTERN ("INT", [])); GENERIC])))) *)
(* 
    3::x::y
    -->
    
    []::y
    3::y
    []
*)
(* let _ = print_endline (list_to_string pattern_to_string
                        (all_possible_patterns 
                            (PATTERN ("CONS", [(PATTERN ("CONS", [(PATTERN ("INT", [])); GENERIC])); GENERIC])))) *)

(* let _ = print_endline (list_to_string pattern_to_string
                        (all_possible_patterns
                            (PATTERN ("CONS", [GENERIC; GENERIC])))) *)
(*  UNIT TESTS *)
(* tests that SHOULD pass: *)

(* let user_patterns = [(cons GENERIC GENERIC); nil]
let product =  [(cons GENERIC GENERIC); nil] *)

(* let user_patterns = [nil; (cons GENERIC GENERIC)]
let product = [(cons GENERIC GENERIC); nil] *)

(* let user_patterns = [nil; GENERIC]
let product = [(cons GENERIC GENERIC); nil] *)

(* let user_patterns = [(cons GENERIC nil); (cons GENERIC GENERIC); nil]
let product = [nil; (cons GENERIC GENERIC);]  *)

(* 
   []
   []::ys
   ys::[]
   xs
*)
(* let user_patterns = [PATTERN ("NIL", []); PATTERN ("CONS", [PATTERN ("NIL", []); GENERIC]); PATTERN ("CONS", [GENERIC; PATTERN ("NIL", [])]); GENERIC]

[]
[]::(x::xs)
(x::xs)::[]
[]::[]
(x::xs)::(y::ys)

let product = [nil; (cons nil (cons GENERIC GENERIC)); (cons (cons GENERIC GENERIC) nil); (cons (cons GENERIC GENERIC) (cons GENERIC GENERIC)); (cons nil nil)]  *)

(* let user_patterns = [PATTERN ("TOILET", [PATTERN ("POO", []); PATTERN ("POO", [])]); PATTERN ("TOILET", [PATTERN ("PEE", []); PATTERN ("PEE", [])]); PATTERN ("TOILET", [PATTERN ("PEE", []); PATTERN ("POO", [])]); PATTERN ("TOILET", [PATTERN ("POO", []); PATTERN ("PEE", [])]);]
let product = [PATTERN ("TOILET", [PATTERN ("POO", []); PATTERN ("POO", [])]); PATTERN ("TOILET", [PATTERN ("PEE", []); PATTERN ("PEE", [])]); PATTERN ("TOILET", [PATTERN ("PEE", []); PATTERN ("POO", [])]); PATTERN ("TOILET", [PATTERN ("POO", []); PATTERN ("PEE", [])]);] *)
(* tests that should fail: *)

(* let user_patterns = [PATTERN ("NIL", [])]
let product = [nil; (cons GENERIC GENERIC)] *)

(* let user_patterns = [GENERIC; nil]
let product = [(cons GENERIC GENERIC); nil] *)

(* let user_patterns = [(cons GENERIC GENERIC); (cons GENERIC nil); nil]
let product = [(cons GENERIC GENERIC); nil] *)

(* let user_patterns = [(cons GENERIC GENERIC)]
let product = [nil; (cons GENERIC GENERIC)] *)

(* 
   []
   []::ys
   ys::[]
*)
(* let user_patterns = [PATTERN ("NIL", []); PATTERN ("CONS", [PATTERN ("NIL", []); GENERIC]); PATTERN ("CONS", [GENERIC; PATTERN ("NIL", [])])]
let product = [nil; (cons nil (cons GENERIC GENERIC)); (cons (cons GENERIC GENERIC) nil); (cons (cons GENERIC GENERIC) (cons GENERIC GENERIC)); (cons nil nil)]  *)

(* 
   TOILET (XS, YS)  ->
   TOILET (POO, PEE) ->

    excessive
*)
(* let user_patterns = [PATTERN ("TOILET", [GENERIC; GENERIC]); PATTERN ("TOILET", [PATTERN ("POO", []); PATTERN ("PEE", [])])]
let product = [PATTERN ("TOILET", [PATTERN ("POO", []); PATTERN ("POO", [])]); PATTERN ("TOILET", [PATTERN ("PEE", []); PATTERN ("PEE", [])]); PATTERN ("TOILET", [PATTERN ("PEE", []); PATTERN ("POO", [])]); PATTERN ("TOILET", [PATTERN ("POO", []); PATTERN ("PEE", [])]);] *)
(* let _ = print_endline (list_to_string pattern_to_string (simplify_user_patterns user_patterns)) *)
(* 
let _ = print_endline (string_of_bool (pattern_covers (cons GENERIC nil) (cons GENERIC GENERIC))) *)
(* let _ = print_endline (string_of_bool (pattern_exhaust user_patterns product)) *)
