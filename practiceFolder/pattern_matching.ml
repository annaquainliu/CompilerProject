type pattern = GENERIC
            |  PATTERN of string * (pattern list)

let list_patterns = [(PATTERN ("NIL", [])); (PATTERN ("CONS", [GENERIC; GENERIC]))]
let int_patterns = [(PATTERN ("VAR", [GENERIC])); (PATTERN ("VAL", []))]
exception Pattern_Matching_Not_Exhaustive
exception Pattern_Matching_Excessive
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
                    else let _ = validate_patterns (List.map List.hd user_list) in 
                        break_down_patterns ps

and validate_patterns ps = match ps with 
    | []                       -> true 
    | (PATTERN (name, _))::_  -> 
            let rec find_pattern env = match env with 
                | [] -> raise Ill_Pattern
                | (_, constructors)::rest ->  if List.exists 
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
        | x::xs, [] -> raise Pattern_Matching_Excessive
        | [], x::xs -> raise Pattern_Matching_Not_Exhaustive
        | [], [] -> true
        | (_, m::ms) -> 
        match List.filter (matched_pattern m) user_patterns with 
            | []      -> raise Pattern_Matching_Not_Exhaustive
            | matches -> 
                if (List.length matches) > 1 && List.for_all all_generic_matches matches
                then raise Pattern_Matching_Excessive
                else 
                let _ = break_down_patterns 
                        (List.map
                        (fun p -> match p with 
                                | PATTERN (name, list) -> list 
                                | _ -> raise Ill_Pattern)
                        matches)
                in pattern_exhaust 
                    (List.filter (fun p -> (not (matched_pattern m p))) user_patterns) 
                    ms 
                            
let user_patterns = [PATTERN ("CONS", [GENERIC; GENERIC]); PATTERN ("NIL", [])]
let _ = validate_patterns user_patterns