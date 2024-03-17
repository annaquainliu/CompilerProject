exception Pattern_Matching_Not_Exhaustive of string 
exception Pattern_Matching_Excessive of string
exception Ill_Pattern of string 
exception Not_Found of string
exception Ill_Typed of string

let list_to_string f xs = 
    let rec stringify = function 
      |  []         -> ""
      |  [x]        -> (f x)
      |  (x::xs)    -> (f x) ^ ", " ^ stringify xs
    in "[" ^ stringify xs ^ "]"


type exp = LITERAL of value
        | VAR of string 
        | IF of exp * exp * exp
        | APPLY of exp * exp list 
        | LAMBDA of string list * exp
        | LET of def list * exp
        | MATCH of exp list * ((pattern list) * exp) list
and value =    STRING of string 
       |  NUMBER of int
       |  BOOLV  of bool
       |  NIL
       |  PAIR of value * value
       |  CLOSURE of exp * (string * value) list
       |  PRIMITIVE of (value list -> value)
and def =  LETDEF of string * exp
       | LETREC of string * exp 
       | EXP of exp
and pattern = GENERIC of string
        |  VALUE of value 
        |  PATTERN of string * (pattern list)


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

let get_tycon_name = function 
    | (TYCON name) -> name 
    | _ -> raise (Ill_Typed "get_tycon_name")


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
                                   (fun (ps, e) -> "(" ^ (list_to_string pattern_to_string ps) ^ ", " ^ exp_to_string e ^ ")")
                                    cases)
                               ^ ")"
and value_to_string = function 
   | (STRING s) -> "STRING(" ^ s ^ ")"
   | (NUMBER n) -> "NUMBER(" ^ string_of_int n ^ ")"
   | (BOOLV false) -> "BOOLV(false)"
   | (BOOLV true) -> "BOOLV(true)"
   | NIL -> "NIL"
   | (PAIR (e, v)) -> "PAIR(" ^ value_to_string e ^ ", " ^ value_to_string v ^ ")"
   | (CLOSURE (LAMBDA (args, e), rho))  -> "CLOSURE(" ^ exp_to_string (LAMBDA (args, e)) ^ ", rho)"
   | (PRIMITIVE f) -> "PRIM"
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

let tuple_pattern list = PATTERN ("TUPLE", list)
let list_patterns = [(PATTERN ("NIL", [])); (PATTERN ("CONS", [tuple_pattern [(GENERIC "_"); (GENERIC "_")]]))]
let int_patterns = [(GENERIC "_")]
let bool_patterns = [(GENERIC "_")]
let string_patterns = [(GENERIC "_")]
let excrement_patterns = [(PATTERN ("POO", [])); (PATTERN ("PEE", []))]
let toilet_patterns = [(PATTERN ("TOILET", [tuple_pattern [(GENERIC "_"); (GENERIC "_");]]))]
let hello_patterns = [(PATTERN ("GREET", [tuple_pattern [(GENERIC "_"); (GENERIC "_")]])); (PATTERN ("BYE", [(GENERIC "_")]))]

let get_fun_result = function 
    | CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result]) -> 
        result
    | _ -> raise (Ill_Typed "get_fun_result")

let toilet a b = PATTERN ("TOILET", [tuple_pattern [a;b]])
let poo = PATTERN ("POO", [])
let pee = PATTERN ("PEE", [])
let cons a b = PATTERN ("CONS",[(tuple_pattern [a;b])])
let nil = PATTERN ("NIL", [])
let parameters list = PATTERN ("PARAMETERS", list)

let bye a = PATTERN ("BYE", [a])
let greet a b = PATTERN ("GREET", [tuple_pattern [a;b]])

(* 
  Environment association list of names to list of constructors
*)
let datatypes = [("list", list_patterns); 
                    ("toilet", toilet_patterns); ("excrement", excrement_patterns); ("hello", hello_patterns);
                    ("tuple", []); ("parameters", [])]

let gamma = [
            ("TOILET", degentype (funtype ([tuple [TYCON "excrement"; TYCON "excrement"]], TYCON "toilet"))); 
            ("PEE", degentype (funtype ([], TYCON "excrement"))); 
            ("POO", degentype (funtype ([], TYCON "excrement"))); 
            ("GREET", degentype (funtype ([tuple [TYCON "hello"; TYCON "hello"]], TYCON "hello")));
            ("BYE", degentype (funtype ([TYCON "toilet"], TYCON "hello")));
            ("NIL", FORALL (["'a"], (funtype ([], listty (TYVAR "'a")))));
            ("CONS",  FORALL (["'a"], (funtype ([(TYVAR "'a"); (listty (TYVAR "'a"))], (listty (TYVAR "'a"))))));
            ("TUPLE", degentype (funtype ([], TYCON "tuple")));
            ("PARAMETERS", degentype (funtype ([], TYCON "parameters")))]

let rec lookup k = function 
            | [] -> raise (Not_Found ("Could not find variable '" ^ k ^ "'"))
            | ((k', v)::rest) -> if k' = k then v else lookup k rest

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
        | (PATTERN (name, list), PATTERN (name', list')) -> name = name' && double_list_all equal_pattern list list'
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
   Given the parameters of a function in every case, and the
   type of the function
   determine if the cases are exhaustive.

    (pattern list) list -> bool
*)

let validate_parameters cases = 
    let patterns = List.map (fun list -> (parameters list)) cases in  
    validate_patterns patterns datatypes gamma
    

(*
    UNIT TESTS!
*)


(* should be not exhaustive *)
(* 
   []
   x::(y::ys)
*)
(* let user_patterns = [nil; (cons (GENERIC "_") (cons (GENERIC "_") (GENERIC "_")));] *)
(* let user_patterns =  [nil; (cons (GENERIC "_") (GENERIC "_"))] *)

(* should be excessive *)
(* let user_patterns = [(GENERIC "_"); nil] *)

(* should be exessive *)
(* let user_patterns = [nil; (cons (GENERIC "_") (GENERIC "_")); (cons (GENERIC "_") (cons (GENERIC "_") (GENERIC "_")))] *)
(* 
   x::y::zs
   z::[]
   []

   should pass
*)
(* let user_patterns = [(cons (GENERIC "_") (cons (GENERIC "_") (GENERIC "_"))); (cons (GENERIC "_") nil); nil] *)

(* 
   Should pass!
*)
(* let user_patterns  =
[
    (bye (toilet poo pee));
    (bye (toilet pee poo));
    (bye (toilet poo poo));
    (bye (toilet pee pee));
    (greet (bye (toilet (GENERIC "_") (GENERIC "_"))) (GENERIC "_"));
    (greet (greet (GENERIC "_") (GENERIC "_")) (GENERIC "_"))
] *)

(* 
   should pass
*)
(* let user_patterns = [nil; (cons nil (cons (GENERIC "_") (GENERIC "_"))); (cons (cons (GENERIC "_") (GENERIC "_")) nil); (cons (cons (GENERIC "_") (GENERIC "_")) (cons (GENERIC "_") (GENERIC "_"))); (cons nil nil)] *)
(* 
   []
   []::(x::ys)
   (x::ys)::[]
   (x::xs)::(y::ys)
   []::[]
*)
(* let user_patterns = [nil; 
                    (cons nil (cons (GENERIC "_") (GENERIC "_"))); 
                    (cons (cons (GENERIC "_") (GENERIC "_")) nil); 
                    (cons (cons (GENERIC "_") (GENERIC "_")) (cons (GENERIC "_") (GENERIC "_")));
                     (cons nil nil)] *)

(* shouldnt be exhaustive *)
(* let user_patterns = [(toilet (GENERIC "_") (GENERIC "_")); (toilet poo pee)] *)
(* let user_patterns = [nil; (GENERIC "_")] *)

(* let user_patterns = [(cons (VALUE (NUMBER 57)) (GENERIC "_")); (cons (GENERIC "_") (GENERIC "_")); nil] *)

(* let user_patterns = 
[
   (greet (bye (toilet (GENERIC "_") (GENERIC "_"))) (GENERIC "_"));
   (bye (toilet poo pee));
   (GENERIC "_")
] *)

(* let user_patterns =  [(PATTERN ("TOILET", [tuple_pattern [PATTERN ("POO", []);PATTERN ("PEE", [])]]));
(PATTERN ("TOILET",  [tuple_pattern [PATTERN ("PEE", []);PATTERN ("PEE", [])]]));
(PATTERN ("TOILET", [tuple_pattern [PATTERN ("PEE", []);PATTERN ("POO", [])]]));
(PATTERN ("TOILET", [tuple_pattern [PATTERN ("POO", []);PATTERN ("POO", [])]]))] *)
(* let user_patterns = [(cons (GENERIC "_") (GENERIC "_")); nil] *)
(* let user_patterns = [VALUE (NUMBER 3); GENERIC "x"] *)
(* let user_patterns = [(cons (VALUE (STRING "890")) (GENERIC "xs")); (cons (GENERIC "x") (GENERIC "xs")); nil] *)

(* Pattern matchign excessive: "890"::x *)
(* 
    pattern_exhaust [G] ["890"::x, "890"::x, x::xs, []]
        pairs = [(G, "890"::x)]
        left_over_users = [ "890"::x, x::xs, []]
        left_over_ideals = []
        non_equals = [(G, "890"::x)]
        splitted = ["890"::x, x::xs, nil]
        new_ideals = ["890"::x, x::xs, nil] @ []
        new_users = ["890"::x, "890"::x, x::xs, []]

    pattern_exhaust ["890"::x, x::xs, nil] ["890"::x, "890"::x, x::xs, []]
        pairs = [("890"::x, "890"::x); ( x::xs, "890"::x); ([], [])]
        left_over_users = [x::xs]
        left_over_ideals = []
        non_equals = [(x::xs, "890"::x)]
        splitted = [x::xs, "890"::x, []]
        new_ideals = [x::xs, "890"::x, []]
        left_over_users = [x::xs, "890"::x, []]
*)
(* let user_patterns = [(cons (VALUE (STRING "890")) (GENERIC "xs")); (cons (VALUE (STRING "890")) (GENERIC "xs")); (cons (GENERIC "x") (GENERIC "xs")); nil] *)

(* Pattern matching excessive: nil will never be reached! *)

(* 
    pattern_exhaust [G] [[], [], x::xs]
        pairs = [(G, [])]
        left_over_users = [[], x::xs]
        left_over_ideals = []
        non_equals = [(G, [])]
        splitted = [x::xs, []]
        new_ideals = [x::xs, []]
        new_users = [[], [], x::xs]

    pattern_exhasut [x::xs, []] [[], [], x::xs]
        pairs = [(x::xs, x::xs), ([], [])]
        left_over_users = [[]]
        left_over_ideals = []
        non_eqials = []
        splitted = []
        new_ideals = []
        new_users = [[]]
*)
(* let user_patterns = [nil; nil; (cons (GENERIC "_") (GENERIC "_"))] *)
(* let user_patterns = [tuple_pattern [VALUE (NUMBER 34); VALUE (NUMBER 56)]] *)
(* let user_patterns = [VALUE (NUMBER 34)] *)
(* let _ = print_endline (string_of_bool (validate_patterns user_patterns datatypes gamma)) *)

(* 

    fun hello x::xs [] = 
            | []    x::xs =
            | x::xs x::xs =
            | []    [] =
*)

(* let parameters = [[(cons (GENERIC "_") (GENERIC "_")); nil];
                    [nil; (cons (GENERIC "_") (GENERIC "_"))];
                    [(cons (GENERIC "_") (GENERIC "_")); (cons (GENERIC "_") (GENERIC "_"))];
                    [nil; nil]] *)
(* 
   fun hello x::xs = ..
    | hello [] = ...
*)

(* let parameters = [[(cons (GENERIC "_") (GENERIC "_"))];[nil]] *)
(* Excessive *)
(* let parameters = [[(cons (GENERIC "_") (GENERIC "_"))]; [(cons nil nil)]; [nil]] *)
(* let parameters = [[(GENERIC "_")]]  *)
(* let parameters = [[(GENERIC "_"); (GENERIC "_")]] *)
(* let _ = print_endline (string_of_bool (validate_parameters parameters)) *)

(* let _ = print_endline (string_of_bool (pattern_covers (cons (VALUE (NUMBER 3)) nil) (cons (VALUE (NUMBER 3)) nil)) ) *)