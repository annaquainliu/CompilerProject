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
let int_patterns = [(PATTERN ("VAR", [GENERIC])); (PATTERN ("VAL", []))]
exception Pattern_Matching_Not_Exhaustive of string 
exception Pattern_Matching_Excessive of string
exception Ill_Pattern
(* 
  Environment association list of names to list of constructors
*)
let datatypes = [("list", list_patterns); ("int", int_patterns)]

(* 
   Determines if the list of user_patterns is exhaustive, excessive, or good
*)
   let matched_pattern p p' = match p, p' with 
   | (PATTERN (name, _)), (PATTERN (name', _)) -> name = name' 
   | _ -> raise Ill_Pattern

let all_generic_matches = 
     (fun p -> match p with  
         | PATTERN (name, list) -> 
               List.for_all 
                 (fun p -> match p with  
                     | GENERIC -> true 
                     | _ -> false) 
                 list
         | _ -> false)
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
                    else let _ = print_endline ("validating with patterns " ^ (list_to_string pattern_to_string (List.map List.hd user_list))) in 
                        let _ = validate_patterns (List.map List.hd user_list) in 
                                break_down_patterns (List.map List.tl user_list)

and validate_patterns ps = match ps with 
    | []                       -> true 
    | (PATTERN (name, _))::_  -> 
            let rec find_pattern env = match env with 
                | [] -> raise Ill_Pattern
                | (_, constructors)::rest -> if List.exists 
                                            (fun p -> match p with 
                                                | (PATTERN (name', _)) -> name = name'
                                                | _ -> false) 
                                            constructors
                                        then constructors  
                                        else find_pattern rest
            in pattern_exhaust ps (find_pattern datatypes)
        | _ -> raise Ill_Pattern

and pattern_exhaust user_patterns to_match = 
    match user_patterns, to_match with 
        | x::xs, [] -> raise (Pattern_Matching_Excessive "base case 1")
        | [], x::xs -> raise (Pattern_Matching_Not_Exhaustive "base case 2")
        | [], [] -> true
        | (_, m::ms) -> 
        match List.filter (matched_pattern m) user_patterns with 
            | []      -> raise (Pattern_Matching_Not_Exhaustive "base case 3")
            | matches -> 
                if (List.length matches) > 1 && List.for_all all_generic_matches matches
                then raise (Pattern_Matching_Excessive "base case 4")
                else 
                let list_patterns = (List.map
                                        (fun p -> match p with 
                                                | PATTERN (name, list) -> list 
                                                | _ -> raise Ill_Pattern)
                                        matches) 
                in
                let _ = print_endline ("to match: " ^ list_to_string pattern_to_string to_match) in
                let _ = print_endline ("breaking down matches: " ^ list_to_string pattern_to_string matches) in 
                let _ = break_down_patterns list_patterns
                in pattern_exhaust 
                    (List.filter (fun p -> (not (matched_pattern m p))) user_patterns) 
                    ms 
                            
(* let user_patterns = [PATTERN ("CONS", [GENERIC; GENERIC]); PATTERN ("NIL", [])] *)
let user_patterns = [PATTERN ("CONS", [GENERIC; PATTERN ("CONS", [GENERIC; GENERIC])]); PATTERN("CONS", [GENERIC; PATTERN("NIL", [])]); PATTERN ("NIL", []);]
let _ = validate_patterns user_patterns