type pattern = GENERIC
            |  CONPATTERN string * (pattern list)

let list_patterns = [(CONPATTERN ("NIL", [])); (CONPATTERN ("CONS", [GENERIC; GENERIC]))]
let int_patterns = [(CONPATTERN ("VAR", [GENERIC])); (CONPATTERN ("VAL", []))]
exception Pattern_Matching_Not_Exhaustive
exception Pattern_Matching_Excessive
exception Ill_Pattern
(* 
  Environment association list of names to list of constructors
*)
let datatypes = [("list", list_patterns); ("int", int_patterns)]



let validate_patterns ps = match ps with 
  | []      -> true 
  | ((CONPATTERN (name, _))::ps) -> 
    let find_pattern env = match env with 
      | [] -> raise Ill_Pattern
      | (_, constructors)::rest ->  if List.exists 
                                (fun p -> match p with 
                                      | (CONPATTERN (name', _)) -> name = name'
                                      | _ -> false) 
                                  constructors
                              then constructors 
                              else find_pattern rest
    in pattern_exhaust ps (find_pattern datatypes)
(* 
   Determines if the list of user_patterns is exhaustive, excessive, or good
*)
let matched_pattern p p' = match p, p' with 
    | (CONPATTERN (name, _)), (CONPATTERN (name', _)) -> name = name' 
    | _ -> raise Ill_Pattern

let all_generic_matches = 
      (fun -> function 
          | CONPATTERN (name, list) -> 
                List.all 
                  (fun -> function 
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
let break_down_patterns = function 
    | []        -> true 
    | user_list -> 
        let starts_gen = List.all starts_generic user_list in 
            if starts_gen
            then break_down_patterns (List.map List.tl user_list)
            else validate_patterns user_list 

let pattern_exhaust user_patterns to_match = 
    match user_patterns, to_match with 
        | x::xs, [] -> raise Pattern_Matching_Excessive
        | [], x::xs -> raise Pattern_Matching_Not_Exhaustive
        | [], [] -> true
        | (_, m::ms) -> 
        match List.filter (matched_pattern m) user_patterns with 
            | []      -> raise Pattern_Matching_Not_Exhaustive
            | matches -> 
                if (List.length matches) > 1 && List.all all_generic_matches matches
                then raise Pattern_Matching_Excessive
                else 
                let _ = break_down_patterns 
                        (fun -> function 
                                | CONPATTERN (name, list) -> list 
                                | _ -> raise Ill_Pattern)
                        matches
                in pattern_exhaust 
                    (List.filter (fun p -> (not (matched_pattern m p))) user_patterns) 
                    ms
                            
