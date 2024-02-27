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

let list_patterns = [(PATTERN ("NIL", [])); (PATTERN ("CONS", [GENERIC; GENERIC]))]
let int_patterns = [(PATTERN ("INT", [])); GENERIC]
let bool_patterns = [(PATTERN ("BOOL", [])); GENERIC]
let string_patterns = [(PATTERN ("STRING", [])); GENERIC]
let poo_patterns = [PATTERN ("TOILET", [GENERIC])]
let poo_other_patterns = [PATTERN ("PEE", []); PATTERN ("POO", []); PATTERN ("DIHREAH")]

exception Pattern_Matching_Not_Exhaustive of string 
exception Pattern_Matching_Excessive of string
exception Ill_Pattern of string 
(* 
  Environment association list of names to list of constructors
*)
let datatypes = [("list", list_patterns); ("int", int_patterns);("bool", bool_patterns);("string", string_patterns)]

let matched_pattern p p' = match p, p' with 
   | (PATTERN (name, _)), (PATTERN (name', _)) -> name = name' 
   |  _, GENERIC -> false
   | _ -> raise (Ill_Pattern "to matched pattern p cannot be generic")

let is_generic = function 
        | GENERIC -> true 
        | _ -> false
    
let all_generic_matches = function  
         | PATTERN (name, list) -> List.for_all is_generic list
         | _ -> false

let get_list = function 
        | PATTERN (name, list) -> list 
        | _  -> raise (Ill_Pattern "Cannot get list of a non-pattern")
(*
     Determines whether a list's first element is generic
*)
let starts_generic list = match list with 
     | []          -> true
     | GENERIC::ps -> true 
     | _           -> false
(* 
     [
       [GENERIC, PATTERN("CONS", [GENERIC, GENERIC])],
       [GENERIC, PATTERN("NIL", [])]
     ]
      Takes in (pattern list) list -> bool
   *)
let rec break_down_patterns user_list = match user_list with  
    | []     -> true 
    | p::ps  -> if List.for_all (fun l -> (List.length l) = 0) user_list 
                then true 
                else if List.for_all starts_generic user_list
                    then break_down_patterns (List.map List.tl user_list)
                    else let _ = validate_patterns (List.map List.hd user_list) in 
                                break_down_patterns (List.map List.tl user_list)

(* 
   Determines if the list of user_patterns is exhaustive, excessive, or good
*)
and validate_patterns ps = match ps with 
    | []                       -> true 
    | [GENERIC]                -> true 
    |  GENERIC::xs -> raise (Pattern_Matching_Excessive "Generic case before other cases")
    | (PATTERN (name, _))::_  -> 
            let rec find_pattern env = match env with 
                | [] -> raise (Ill_Pattern "validate_patterns base case")
                | (_, constructors)::rest -> if List.exists 
                                            (fun p -> match p with 
                                                | (PATTERN (name', _)) -> name = name'
                                                | _ -> false) 
                                            constructors
                                        then constructors  
                                        else find_pattern rest
            in pattern_exhaust ps (find_pattern datatypes)

and pattern_exhaust user_patterns to_match = 
    match user_patterns, to_match with 
        | [GENERIC], x::xs -> true
        | x::xs, [] -> raise (Pattern_Matching_Excessive "base case 1")
        | [], x::xs -> raise (Pattern_Matching_Not_Exhaustive "base case 2")
        | [], [] -> true
        | (m::ms, _) -> match List.filter (matched_pattern m) to_match with 
            | []      -> raise (Pattern_Matching_Excessive "base case 3")
            | [pattern] -> 
                let matches = List.filter (matched_pattern pattern) user_patterns in 
                if (List.length matches) > 1 && (List.for_all all_generic_matches matches)
                then raise (Pattern_Matching_Excessive "base case 4")
                else 
                let _ = break_down_patterns (List.map get_list matches) 
                in pattern_exhaust 
                    (List.filter (fun p -> (not (matched_pattern pattern p))) user_patterns) 
                    (List.filter (fun p -> (not (matched_pattern pattern p))) to_match)
            | _  -> raise (Ill_Pattern "Constructors are not distinct names")
(*
    UNIT TESTS!
*)

(* let user_patterns = [PATTERN ("CONS", [GENERIC; GENERIC]); PATTERN ("NIL", [])] *)
(* 
   x::y::zs
   z::[]
   []

   should pass
*)
(* let user_patterns = [PATTERN ("CONS", [GENERIC; PATTERN ("CONS", [GENERIC; GENERIC])]); PATTERN("CONS", [GENERIC; PATTERN("NIL", [])]); PATTERN ("NIL", []);] *)

(* 
   same as above but diff order, so should pass
*)
(* let user_patterns = [PATTERN("CONS", [GENERIC; PATTERN("NIL", [])]);  PATTERN ("CONS", [GENERIC; PATTERN ("CONS", [GENERIC; GENERIC])]); PATTERN ("NIL", []);] *)
(* let user_patterns = [PATTERN ("NIL", []); PATTERN("CONS", [GENERIC; PATTERN("NIL", [])]);  PATTERN ("CONS", [GENERIC; PATTERN ("CONS", [GENERIC; GENERIC])]); ] *)

(* let user_patterns = [PATTERN ("CONS", [GENERIC; GENERIC]); PATTERN ("NIL", []); PATTERN ("CONS", [GENERIC;GENERIC])] *)
(* let user_patterns = [PATTERN ("CONS", [GENERIC;GENERIC])] *)
(* let user_patterns = [PATTERN ("NIL", []); PATTERN ("CONS", [GENERIC;GENERIC]); PATTERN("NIL", [])] *)
(* let user_patterns = [PATTERN ("NIL", [])] *)

(* 
   X::Y::YS
   Y::YS
   []

   should pass
*)
(* let user_patterns = [PATTERN ("CONS", [GENERIC; PATTERN ("CONS", [GENERIC; GENERIC])]); PATTERN ("CONS", [GENERIC; GENERIC]); PATTERN("NIL", [])] *)

(*
   
    Y::YS
    X::Y::YS
    []

    should not pass
*)
(* let user_patterns = [PATTERN ("CONS", [GENERIC; GENERIC]); PATTERN ("CONS", [GENERIC; PATTERN ("CONS", [GENERIC; GENERIC])]);  PATTERN("NIL", [])] *)

(* let user_patterns = [PATTERN ("NIL", []); GENERIC] *)

(* let user_patterns = [PATTERN ("CONS", [GENERIC; GENERIC]); GENERIC] *)
(* 
   x::[]
   x::xs
   []
*)
(* let user_patterns = [PATTERN ("CONS", [GENERIC; PATTERN ("NIL", [])]); PATTERN ("CONS", [GENERIC; GENERIC]); PATTERN ("NIL", [])] *)
(* 
   x::ys
   ys
*)
(* let user_patterns = [PATTERN ("CONS", [GENERIC;GENERIC]); GENERIC] *)

(* 
   "hi"::xs
   x::xs
   []

   pass
*)
(* let user_patterns = [PATTERN ("CONS", [PATTERN ("STRING", []); GENERIC]); PATTERN ("CONS", [GENERIC;GENERIC]); PATTERN ("NIL", [])] *)

(* 
    X::XS
   "hi"::xs
   []

   fail
*)
(* let user_patterns = [PATTERN ("CONS", [GENERIC;GENERIC]); PATTERN ("CONS", [PATTERN ("STRING", []); GENERIC]); PATTERN ("NIL", [])] *)




let _ = validate_patterns user_patterns