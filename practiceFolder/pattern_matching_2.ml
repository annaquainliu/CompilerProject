exception Pattern_Matching_Not_Exhaustive of string 
exception Pattern_Matching_Excessive of string
exception Ill_Pattern of string

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

(* 
   Given a list of user patterns, and the cartesian product to_match 
   (exhaustive set)
   the most specific pattern, returns true if ps exhuasts the
   product, and false otherwise
*)
let rec pattern_exhaust user_patterns to_match = match user_patterns, to_match with
    | [GENERIC], m::ms  -> true
    | GENERIC::xs, _    -> false
    | [], []            -> true 
    | x::xs, []         -> false  
    | [], x::xs         -> false 
    | _, _              ->  (List.fold_left break_down_patterns to_match user_patterns) = []
(* 
   Runs pattern_exhaust on one pattern and every pattern in 
   to compute the remaining set

    pattern -> (pattern list) -> (pattern list)
*)
and break_down_patterns to_match pattern =
    match pattern with 
        | (PATTERN (name, list)) -> 
                let rec break_down = function 
                    | [] -> []
                    | (PATTERN (name', list')::ps) ->  
                        if (name' = name) && (pattern_exhaust list list')
                        then break_down ps
                        else PATTERN (name', list')::break_down ps
                    | _                      -> raise (Ill_Pattern "Cannot break down generic")
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

(* tests that should fail: *)

(* let user_patterns = [GENERIC; nil]
let product = [(cons GENERIC GENERIC); nil] *)

(* let user_patterns = [(cons GENERIC GENERIC); (cons GENERIC nil); nil]
let product = [(cons GENERIC GENERIC); nil] *)


let _ = print_endline (string_of_bool (pattern_exhaust user_patterns product))
