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

type pattern = GENERIC
            |  PATTERN of string * (pattern list)

type ty = TYCON of string | TYVAR of string | CONAPP of ty * ty list
let intty = TYCON "int"
let boolty = TYCON "bool"
let strty = TYCON "string"
let listty t = CONAPP(TYCON "list", [t])
let tuple list = CONAPP (TYCON "tuple", list)
let funtype (args, result) =
    CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result])

let get_tycon_name = function 
    | (TYCON name) -> name 
    | _ -> raise (Ill_Typed "get_tycon_name")

let rec pattern_to_string = function 
    | GENERIC -> "GENERIC"
    | PATTERN (name, list) -> name ^ "(" ^ list_to_string pattern_to_string list ^ ")"

let list_patterns = [(PATTERN ("NIL", [])); (PATTERN ("CONS", [GENERIC; GENERIC]))]
let int_patterns = [(PATTERN ("INT", [])); GENERIC]
let bool_patterns = [(PATTERN ("BOOL", [])); GENERIC]
let string_patterns = [(PATTERN ("STRING", [])); GENERIC]
let toilet_patterns = [PATTERN ("TOILET", [GENERIC; GENERIC;])]
let excrement_patterns = [PATTERN ("PEE", []); PATTERN ("POO", []);]

let get_fun_result = function 
    | CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result]) -> 
        result
    | _ -> raise (Ill_Typed "get_fun_result")

(* 
  Environment association list of names to list of constructors
*)
let datatypes = [("list", list_patterns); ("int", int_patterns);("bool", bool_patterns);("string", string_patterns);
                 ("excrement", excrement_patterns); ("toilet", toilet_patterns)]

let gamma = [("TOILET", (funtype ([tuple [TYCON "excrement"; TYCON "excrement"]], TYCON "toilet"))); 
                 ("PEE", (funtype ([], TYCON "excrement"))); 
                 ("POO", (funtype ([], TYCON "excrement"))); 
                 ("GREET", (funtype ([tuple [TYCON "hello"; TYCON "hello"]], TYCON "hello")));
                 ("BYE", (funtype ([TYCON "toilet"], TYCON "hello")));
                 ("NIL", (funtype ([], TYCON "list")));
                 ("CONS", (funtype ([TYVAR "'a"], TYCON "list")));
                 ("INT", (funtype ([TYCON "int"], TYCON "int")));]

let toilet a b = PATTERN ("TOILET", [a;b])
let poo = PATTERN ("POO", [])
let pee = PATTERN ("PEE", [])
let cons a b = PATTERN ("CONS", [a;b])
let nil = PATTERN ("NIL", [])
(* 
    Not exhaustive:

    xs covering  {[], x :: y :: zs}
    and we have [xs := []] making the first pattern an instance of the ideal. So we split xs, getting

    [] covering {[]}
    x :: ys covering {x :: y :: zs}

    The first of these is justified by the empty injective renaming, so is ok. 
    The second takes [x := x, ys := y :: zs], so we're away again, splitting ys, getting.

    x :: [] covering {}
    x :: y :: zs covering {x :: y :: zs} 
    ------

    Excessive: 

    xs covering {[], x::ys, x::y::zs}

    Split xs

    [] covering {[]}
    x::xs covering {x::ys, x::y::zs}

    Take first. Same generality, so don't split.

    Remove equals.

    nothing covers {x::y::zs}

    ----

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

let rec lookup k = function 
            | [] -> raise (Not_Found ("Could not find variable '" ^ k ^ "'"))
            | ((k', v)::rest) -> if k' = k then v else lookup k rest

let rec double_list_all p list list' =
    match list, list' with 
        | [], [] -> true 
        | (x::xs), (y::ys) -> (p x y) && double_list_all p xs ys
        | _   -> raise (Ill_Pattern ("ill formed constructors when comparing " ^ (list_to_string pattern_to_string list) ^ " " ^  (list_to_string pattern_to_string list')))

let rec pattern_covers m m' = match m, m' with
            | GENERIC, _       -> true
            | (PATTERN (name, list)), (PATTERN (name', list')) ->
                name = name' && (double_list_all pattern_covers list list')
            | _   -> false
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

let get_name = function 
    | (PATTERN (name, _)) -> name
    | _ -> raise (Ill_Pattern "Tried to get name of generic")
(* 
    Given an ideal pattern and a user pattern, splits
    the ideal pattern into more ideal patterns.
   
    pattern -> pattern -> (pattern list) list

    x :: ys covering {x :: y :: zs}
    
*)
let rec equal_pattern p p' = 
    match p, p' with 
        | GENERIC, GENERIC -> true
        | (PATTERN (name, list), PATTERN (name', list')) -> name = name' && double_list_all equal_pattern list list'
        | _ -> false
(* 
   Given an ideal and user patterns, returns a list of tuples
    of matched ideal patterns to user patterns,
   and the rest of the user_matches left over.
*)
let find_pairs ideals user_matches = 
    List.fold_left 
        (fun (pairs, users) i -> 
            if (not (List.exists (pattern_covers i) users)) 
            then raise (Pattern_Matching_Not_Exhaustive ((pattern_to_string i) ^ " is not matched in your patterns."))
            else let matched = List.find (pattern_covers i) users in 
                    ((i, matched)::pairs, List.filter (fun p -> (not (equal_pattern p matched))) users)) 
        ([], user_matches)
        ideals
(* 
   Splitting the ideal pattern into the generality 
   of the user pattern, by breaking down the ideal 
   pattern into a list of ideal patterns.

   pattern -> pattern -> pattern list
*)
let rec splitting ideal user = match ideal, user with  
    | GENERIC, (PATTERN _) ->  all_possible_patterns user
    | (PATTERN (name, list), PATTERN (name', list')) -> 
        let ideals = map_ideals list list' in 
        (* let _ = print_endline (list_to_string (list_to_string pattern_to_string) ideals) in *)
        let product = cartesian_product ideals [] [] in
        (* let _ = print_endline (list_to_string (list_to_string pattern_to_string) product) in *)
        List.map (fun list -> (PATTERN (name, List.rev list))) product
    | GENERIC, GENERIC -> [GENERIC]
    | _, _             -> raise (Ill_Pattern "ideal pattern is more specific than user's, can't be split")
and
(* Helper function for splitting *)
map_ideals ideal_list user_list = match ideal_list, user_list with 
    | [], []           -> []
    | (i::is), (u::us) -> splitting i u::(map_ideals is us)
    | _, _             -> raise (Ill_Pattern "Mismatch constructor lists")

(* 
   Given a list of ideal patterns and user patterns, 
   returns true if the user patterns exhaust the ideal patterns,
   and throws an error otheriwse.
*)
let rec pattern_exhaust ideals user_matches = match ideals, user_matches with 
    | [], []      -> true 
    | [], (x::xs) -> false
    | (x::xs), [] -> false
    | _, _ -> 
        let (pairs, left_over_users) = find_pairs ideals user_matches in
        let filtered_non_equals = List.filter (fun (a, b) -> not (equal_pattern a b)) pairs in
        let first_ideal_instances = List.map (fun (a, b) -> b) filtered_non_equals in
        let splitted = List.fold_left (fun acc (i, p) -> List.append (splitting i p) acc) [] filtered_non_equals in 
        let _ = print_endline ("recursing on: " ^ (list_to_string pattern_to_string splitted) ^ " and " ^ (list_to_string pattern_to_string (List.append left_over_users first_ideal_instances))) in
        pattern_exhaust splitted (List.append left_over_users first_ideal_instances)

let validate_patterns user_patterns = pattern_exhaust [GENERIC] user_patterns

let _ = print_endline (string_of_bool (validate_patterns [nil; (cons GENERIC (cons GENERIC GENERIC));]))
(* let _ = print_endline (list_to_string pattern_to_string (splitting GENERIC nil)) *)
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




(* let _ = validate_patterns user_patterns *)