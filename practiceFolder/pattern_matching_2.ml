exception Pattern_Matching_Not_Exhaustive 
exception Pattern_Matching_Excessive 
exception Ill_Pattern of string
exception Ill_Typed


let list_to_string f xs = 
  let rec stringify = function 
    |  []         -> ""
    |  [x]        -> (f x)
    |  (x::xs)    -> (f x) ^ ", " ^ stringify xs
  in "[" ^ stringify xs ^ "]"

type pattern = GENERIC
            |  PATTERN of string * (pattern list)

let is_generic = function 
            | GENERIC -> true 
            | _ -> false

let rec pattern_to_string = function 
  | GENERIC -> "GENERIC"
  | PATTERN (name, list) -> name ^ "(" ^ list_to_string pattern_to_string list ^ ")"

let matched_pattern p p' = match p, p' with 
  | (PATTERN (name, _)), (PATTERN (name', _)) -> name = name' 
  |  _, GENERIC -> false
  | _ -> raise (Ill_Pattern "to matched pattern p cannot be generic")

let cons a b = PATTERN ("CONS", [a;b])
let nil = PATTERN ("NIL", [])
let list_patterns = [(PATTERN ("NIL", [])); (PATTERN ("CONS", [GENERIC; GENERIC]))]
let int_patterns = [(PATTERN ("INT", [])); GENERIC]
let bool_patterns = [(PATTERN ("BOOL", [])); GENERIC]
let string_patterns = [(PATTERN ("STRING", [])); GENERIC]


let datatypes = [("list", list_patterns); ("int", int_patterns);("bool", bool_patterns);("string", string_patterns)]

let get_list = function 
        | PATTERN (name, list) -> list 
        | _  -> raise (Ill_Pattern "Cannot get list of a non-pattern")

let rec  pattern_covers m m' = match m, m' with
            | GENERIC, _       -> true
            | (PATTERN (name, list)), (PATTERN (name', list')) ->
                name = name' && (double_list_all list list')
            | _   -> false
and double_list_all list list' =
    match list, list' with 
        | [], [] -> true 
        | (x::xs), (y::ys) -> (pattern_covers x y) && double_list_all xs ys
        | _   -> raise (Ill_Pattern "ill formed constructors")
(* 
    returns true if m covers m', and false otherwise
*)
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
   Runs pattern_exhaust on one pattern and every pattern in 
   to compute the remaining set

    pattern -> (pattern list) -> (pattern list)
*)
and break_down_patterns to_match pattern =
    match pattern with 
        (* List.fold_left: ('acc -> 'a -> 'acc) -> 'acc -> 'a list -> 'acc *)
        | (PATTERN _) -> 
            let rec break_down = function 
                | [] -> []
                | (p::ps) ->  
                    if (pattern_covers pattern p)
                    then break_down ps
                    else p::break_down ps
            in break_down to_match 
        | GENERIC -> [] 

(*  UNIT TESTS *)
(* tests that SHOULD pass: *)

(* let user_patterns = [PATTERN ("NIL", []); PATTERN ("CONS", [PATTERN ("NIL", []); GENERIC]); PATTERN ("CONS", [GENERIC; PATTERN ("NIL", [])])]
let product = [nil; (cons nil (cons GENERIC GENERIC)); (cons (cons GENERIC GENERIC) nil); (cons (cons GENERIC GENERIC) (cons GENERIC GENERIC)); (cons nil nil)] *)

(* let user_patterns = [PATTERN ("NIL", [])]
let product = [nil; (cons GENERIC GENERIC)] *)

(* let user_patterns = [(cons GENERIC GENERIC)]
let product = [nil; (cons GENERIC GENERIC)] *)

(* let user_patterns = [(cons GENERIC GENERIC); nil]
let product =  [(cons GENERIC GENERIC); nil] *)

(* let user_patterns = [nil; (cons GENERIC GENERIC)]
let product = [(cons GENERIC GENERIC); nil] *)

(* let user_patterns = [nil; GENERIC]
let product = [(cons GENERIC GENERIC); nil] *)

(* let user_patterns = [(cons GENERIC nil); (cons GENERIC GENERIC); nil]
let product = [nil; (cons GENERIC GENERIC);] *)

(* tests that should fail: *)

(* let user_patterns = [GENERIC; nil]
let product = [(cons GENERIC GENERIC); nil] *)

let user_patterns = [(cons GENERIC nil); nil]
let product = [nil]


(* let _ = print_endline (string_of_bool (pattern_covers (cons GENERIC nil) nil)) *)
let _ = print_endline (string_of_bool (pattern_exhaust user_patterns product))
