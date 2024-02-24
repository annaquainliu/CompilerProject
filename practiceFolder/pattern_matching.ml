type pattern = GENERIC
            |  CONPATTERN string * (pattern list)

let list_patterns = [(CONPATTERN "NIL", []); (CONPATTERN "CONS", [GENERIC; GENERIC])]
let int_patterns = [(CONPATTERN ("VAR", [GENERIC])); (CONPATTERN ("VAL", []))]
exception Pattern_Matching_Not_Exhaustive
exception Pattern_Matching_Excessive
exception Ill_Pattern
(* 
  Environment association list of names to list of constructors
*)
let datatypes = [("list", list_patterns); ("int", int_patterns)]


let validate_pattern user_patterns = 
    
(* 
   Determines if the list of user_patterns is exhaustive, excessive, or good
*)
let pattern_exhaust user_patterns to_match = 
    let matched_pattern p p' = match p, p' with 
      | (CONPATTERN (name, _)), (CONPATTERN (name', _)) -> name = name' 
      | _ -> raise Ill_Pattern
    match user_patterns, to_match with 
      | x::xs, [] -> raise Pattern_Matching_Excessive
      | [], x::xs -> raise Pattern_Matching_Not_Exhaustive
      | (p::ps, _) -> 
        match List.filter (matched_pattern p) to_match with 
          | []  -> raise Pattern_Matching_Excessive
          | matches -> 
      


  
