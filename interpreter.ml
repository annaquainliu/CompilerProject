(* 
   -----------------------------------------
        
    -------    MISCELLANEOUS    -------  

   -----------------------------------------
*)
let pop_first_char input = String.sub input 1 ((String.length input) - 1)

let list_to_string f xs = 
    let rec stringify = function 
      |  []         -> ""
      |  [x]        -> (f x)
      |  (x::xs)    -> (f x) ^ ", " ^ stringify xs
    in "[" ^ stringify xs ^ "]"

exception Ill_Typed of string 
exception Runtime_Error of string 
exception Pattern_Matching of string 
exception Cringe of string
let typeInferenceBug = Cringe("The problem with pissing on my grave is eventually you'll run out of piss. -Margaret Thatcher")
let usefulError x = Cringe x (*for debugging*)

let e_to_string = function
    | (Ill_Typed s)        -> ("Type Error", s)
    | (Runtime_Error s)    -> ("Runtime Error", s)
    | (Pattern_Matching s) -> ("Pattern Error", s)
    | (Cringe s)           -> ("Cringe", s)
    | e                    -> ("Error", "error")

let print_error ex = 
    let reset_ppf = Spectrum.prepare_ppf Format.std_formatter in
    let (ex_type, message) = e_to_string ex in 
    let _ = Format.printf "@{<red>%s@}\n" (ex_type ^ ": ") in
    let _ = reset_ppf () in 
    print_string (message ^ "\n")
(* 
    Returns the value of a key in an association list
   'a -> ('a * 'b) list -> 'b
*)
let rec lookup k = function 
            | [] -> raise (Runtime_Error ("Could not find variable '" ^ k ^ "'"))
            | ((k', v)::rest) -> if k' = k then v else lookup k rest

let rec zip xs ys = match xs, ys with
    | [], [] -> []
    | k::ks, v::vs -> (k, v)::zip ks vs
    | _ ,      _       -> raise (Runtime_Error "Mismatched lengths of lists")

let fst = function (a, b) -> a
let snd = function (a, b) -> b
(* 
   -----------------------------------------
        
    -------    PARSING    -------  

   -----------------------------------------
*)
(* 
   parse takes in string input and returns a list of tokens,
   which is any keyword or string deliminated by a space
*)
let rec parse input = 
    let queue = Queue.create () in
    let rec parse_string input = match input.[0] with 
        | '"' -> ("", pop_first_char input)
        | c -> match parse_string (pop_first_char input) with 
                    | (str, leftover) -> ((String.make 1 c) ^ str, leftover) in
    let rec extract input str = match input with 
        | "" -> ()
        | _  -> match input.[0] with 
                | ' ' | ';' | '(' | ')' | '[' | ']' | ',' | '"' | '{' | '}' -> 
                    let _ = if str <> "" then Queue.add str queue else () in 
                    let _ = if input.[0] <> ' ' then Queue.add (String.make 1 input.[0]) queue else () in 
                    if input.[0] = '"' 
                    then let (str, leftover) = parse_string (pop_first_char input) in
                            let () = Queue.add str queue in 
                            let () = Queue.add (String.make 1 '"') queue in
                            extract leftover ""
                    else extract (pop_first_char input) ""
                | c  ->  if String.length input == 1
                        then Queue.add (str ^ String.make 1 c) queue (* to handle case where last char is not a delimeter *)
                        else extract (pop_first_char input) (str ^ String.make 1 c) 
    in let _ = (extract input "") in 
    queue


(* 
   -----------------------------------------
        
    -------    ABSTRACT SYNTAX    -------  

   -----------------------------------------
*)
type ty = TYCON of string | TYVAR of string | CONAPP of ty * ty list
let intty = TYCON "int"
let boolty = TYCON "bool"
let strty = TYCON "string"
let listty t = CONAPP(TYCON "list", [t])
let tuplety list = CONAPP (TYCON "tuple", list)
let funtype (args, result) =
  CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result])

type tyscheme = FORALL of string list * ty
type subst = (ty * ty) list
type tyenv = (string * tyscheme) list * string list 

type con = TRIVIAL | EQ of ty * ty | CONJ of con * con

let degentype tau = FORALL ([], tau)
type constructor = UNARYCONS of string * ty
                |  NULLCONS of string 

let rec type_to_string = function
    | TYVAR(a) -> a
    | TYCON(c) -> c
    | CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result]) -> 
        "(" ^ list_to_string type_to_string args ^ " -> " ^ type_to_string result ^ ")"
    | CONAPP(tc, taus) ->
         "(" ^ type_to_string tc ^ " " ^ list_to_string type_to_string taus ^ ")"
let scheme_to_string = function 
    | FORALL (alphas, tau) -> "(forall " ^ list_to_string (fun a -> a) alphas ^ " " ^ type_to_string tau ^ ")" 
  
type kind = TYPE | INWAITING of kind list * kind

type exp = LITERAL of value
        | VAR of string 
        | IF of exp * exp * exp
        | APPLY of exp * exp list 
        | LAMBDA of string list * exp
        | LET of def list * exp
        | MATCH of exp * (pattern * exp) list
        | TUPLE of (exp list)
and value = STRING of string 
        |  NUMBER of int
        |  BOOLV  of bool
        |  NIL
        |  PAIR of value * value
        |  CLOSURE of exp * (string * value) list
        |  PRIMITIVE of (value list -> value)
        |  TUPLEV of (value list)
        |  TYPECONS of (value list -> value)
        |  PATTERNV of pattern
and def =  LETDEF of string * exp
        | LETREC of string * exp 
        | EXP of exp
        | ADT of string * string list * (constructor list)
and pattern = GENERIC of string
        |  VALUE of value 
        |  PATTERN of string * (pattern list)

(* 
   -----------------------------------------
        
    -------    TO STRING LIBRARY    -------  

   -----------------------------------------
*)
let cons_to_string = function 
    | (UNARYCONS (name, tau)) -> "UNARYCONS(" ^ name ^ ", " ^ type_to_string tau ^ ")"
    | (NULLCONS name) -> "NULLCONS(" ^ name ^ ")" 

let rec kind_to_string = function 
    | (TYPE) -> "TYPE"
    | (INWAITING (ks, k)) -> "INWAITING(" ^ (list_to_string kind_to_string ks) ^ ", " ^ kind_to_string k ^ ")"

let rec def_to_string = function 
         | (LETDEF (x, e)) -> "LETDEF(" ^ x ^ ", " ^ exp_to_string e ^ ")"
         | (LETREC (x, e)) -> "LETREC(" ^ x ^ ", " ^ exp_to_string e ^ ")"
         | (EXP e) -> "EXP(it, " ^ exp_to_string e ^ ")"
         | (ADT (name, tyvars, cons)) -> "ADT(" ^ name ^ ", "
                                 ^ (list_to_string (fun s -> s) tyvars) ^ ", "
                                 ^ (list_to_string cons_to_string cons)
                                 ^ ")"
    and exp_to_string = function 
        | (LITERAL v) -> value_to_string v
        | (VAR s) -> "VAR(" ^ s ^ ")"
        | (IF (e, e2, e3)) -> "IF(" ^ exp_to_string e ^ ", " ^ exp_to_string e2 ^ ", " ^ exp_to_string e3 ^ ")"
        | (APPLY (f, args)) -> "APPLY(" ^ exp_to_string f ^ ", " ^ list_to_string exp_to_string args ^")"
        | (LAMBDA (xs, e))  -> "LAMBDA(" ^ list_to_string (fun a -> a) xs ^ ", " ^ exp_to_string e ^ ")"
        | (LET (ds, e)) -> "LET(" ^ list_to_string def_to_string ds ^ ", " ^ exp_to_string e ^ ")"
        | (MATCH (e, cases)) -> "MATCH(" ^ (exp_to_string e) ^ ", " ^ 
                                    (list_to_string 
                                        (fun (p, e) -> "(" ^ (pattern_to_string p) ^ ", " ^ exp_to_string e ^ ")")
                                         cases)
                                    ^ ")"
        | (TUPLE exps) -> "TUPLE(" ^ (list_to_string exp_to_string exps) ^ ")"
    and value_to_string = function 
        | (STRING s) -> "STRING(" ^ s ^ ")"
        | (NUMBER n) -> "NUMBER(" ^ string_of_int n ^ ")"
        | (BOOLV false) -> "BOOLV(false)"
        | (BOOLV true) -> "BOOLV(true)"
        | NIL -> "NIL"
        | (PAIR (e, v)) -> "PAIR(" ^ value_to_string e ^ ", " ^ value_to_string v ^ ")"
        | (CLOSURE (LAMBDA (args, e), rho))  -> "<function>"
        | (PRIMITIVE f) -> "PRIM"
        | (TUPLEV l) -> "TUPLEV(" ^ (list_to_string value_to_string l) ^ ")"
        | (TYPECONS f) -> "TYPECONS"
        | (PATTERNV v) -> "PATTERNV(" ^ pattern_to_string v ^ ")"
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
let val_patterns = [(GENERIC "_")]

let cons a b = PATTERN ("CONS",[(tuple_pattern [a;b])])
let nil = PATTERN ("NIL", [])

(* 
   -----------------------------------------
        
    -------        PATTERNS   -------  
     * exhuastiveness +  evaluation +  *
   -----------------------------------------
*)
let get_fun_result = function 
    | CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result]) -> 
        result
    | _ -> raise (Ill_Typed "get_fun_result")
    
(* 
   Given a value, converts it into a pattern

   Used to pattern match values of expressions on patterns.

   value -> pattern
*)
let rec value_to_pattern = function 
    | TUPLEV (values) -> tuple_pattern (List.map value_to_pattern values)
    | NIL             -> nil
    | PAIR (v, vs)    -> cons (value_to_pattern v) (value_to_pattern vs)
    | PATTERNV p  -> p_vals_to_p p
    | (CLOSURE _) 
    | (PRIMITIVE _)   -> raise (Ill_Typed ("Cannot pattern match on a function."))
    | (TYPECONS s)    -> raise (Ill_Typed ("Pattern matching on constructor requires application '()'. "))
    | v               -> (VALUE v)
and 
(* 
   Extracts the values from patterns and transforms them into
   patterns

   pattern -> pattern
*)
p_vals_to_p = function
    | (PATTERN (name, list)) -> (PATTERN (name, List.map p_vals_to_p list))
    | (VALUE v)  -> value_to_pattern v
    | _          -> raise (Ill_Typed "Generic is not a valid pattern value.")
(* 
   Given a pattern, converts it into a value
    
   Used to extract value of generics in pattern matching.
*)
let rec pattern_to_value = function 
    | (VALUE v)   -> v
    | (GENERIC c) -> raise (Ill_Typed ("Cannot transform a generic" ^ c ^ " to a value"))
    | (PATTERN ("NIL", [])) -> NIL
    | (PATTERN ("TUPLE", ps)) -> TUPLEV (List.map pattern_to_value ps) 
    | (PATTERN ("CONS", ps)) -> 
        (match ps with 
            | [p] -> (match pattern_to_value p with 
                    | (TUPLEV [v; vs]) -> PAIR (v, vs)
                    | _                ->  raise (Ill_Typed ("Ill formed CONS application.")))
            |  _  -> raise (Ill_Typed ("Ill formed CONS application.")))
    |  p  -> (PATTERNV p)

(* let _ = print_endline (pattern_to_string (value_to_pattern (PAIR (NUMBER 3, PAIR (NUMBER 1, NIL))))) *)
(* let _ = print_endline (pattern_to_string (value_to_pattern (PATTERNV (PATTERN ("twice", [VALUE (TUPLEV [(PATTERNV (PATTERN ("ZERO", []))); PATTERNV (PATTERN ("ONEBIT", []))])]))))) *)

let rec double_list_all p list list' =
    match list, list' with 
        | [], [] -> true 
        | (x::xs), (y::ys) -> (p x y) && double_list_all p xs ys
        | _   -> raise (Ill_Typed ("ill formed constructors when comparing " ^ 
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
    | _ -> raise (Ill_Typed "Tried to get name of generic/value")
(* 
    Given an ideal pattern and a user pattern, splits
    the ideal pattern into more ideal patterns.
   
    pattern -> pattern -> (pattern list) list

    x :: ys covering {x :: y :: zs}
    
*)
let rec equal_pattern p p' = 
    match p, p' with 
        | (GENERIC _), (GENERIC _) -> true
        | (PATTERN (name, list), PATTERN (name', list')) -> 
            name = name' && double_list_all equal_pattern list list'
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
        | []    -> raise (Ill_Typed "Find pattern Issue")
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
   Given a pattern, returns true if the pattern contains a value
*)
let rec contains_value = function 
   | (GENERIC _) -> false
   | (VALUE _) -> true
   | (PATTERN (_, list)) -> List.exists contains_value list
   
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
    | (GENERIC _), (PATTERN _) ->  
        if (contains_value user) 
        then user::(all_possible_patterns user)
        else (all_possible_patterns user)
    | (PATTERN (name, list), PATTERN (name', list')) -> 
        let ideals = map_ideals list list' in 
        let product = cartesian_product ideals [] [] in
        List.map (fun list -> (PATTERN (name, List.rev list))) product
    | (GENERIC _), (GENERIC _) -> [GENERIC "_"]
    | (GENERIC _), (VALUE s)   -> [(VALUE s); (GENERIC "_");]
    | (VALUE _), (VALUE _)     -> []
    | _, _             -> raise (Ill_Typed ((pattern_to_string ideal) ^ " is more specific than " ^ (pattern_to_string user))))
and
(* Helper function for splitting *)
map_ideals ideal_list user_list = (match ideal_list, user_list with 
    | [], []           -> []
    | (i::is), (u::us) -> splitting i u::(map_ideals is us)
    | _, _             -> raise (Ill_Typed "Mismatch constructor lists"))
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
    | [], (x::xs) -> raise (Pattern_Matching ((pattern_to_string x) ^ " will never be reached."))
    | (x::xs), [] -> raise (Pattern_Matching ((pattern_to_string x) ^ " is not matched in your patterns."))
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
    | [x] -> raise (Pattern_Matching ((pattern_to_string x) ^ " is repeated in your patterns."))
    |  _ -> pattern_exhaust [GENERIC "_"] user_patterns




(* 
   -----------------------------------------
        
    -------    TOKENIZATION    -------  

   -----------------------------------------
*)
(* 
  Takes in a queue of strings, and then tokenizes the result

  string queue -> def
*)

let tokenize queue = 
    let tokenWhileDelim delim f = 
        let rec tokenWhile () = 
            let curr = Queue.pop queue in 
            if curr = delim 
                then []
                else 
                    let exp = f curr in 
                    exp::(tokenWhile ())
        in tokenWhile ()
    in 
    let rec tokenType = function 
        | "(" -> let tau = TYCON (Queue.pop queue) in 
                 let taus = tokenWhileDelim ")" tokenType in 
                 CONAPP (tau, taus)
        |  tau  -> if tau.[0] = '\''
                   then TYVAR (pop_first_char tau)
                   else TYCON tau  
    in 
    let rec tokenADT () = 
        let name = Queue.pop queue in 
        let cons =
            if (Queue.length queue <> 0) && (Queue.peek queue) = "of" 
            then let _ = Queue.pop queue in 
                 UNARYCONS (name, tokenType (Queue.pop queue))
            else NULLCONS (name)
        in 
        if (Queue.length queue <> 0) && (Queue.peek queue) = "|" 
        then let _ = Queue.pop queue in (* for | *)
             cons::(tokenADT ())
        else [cons] 
    in 
    let rec tokenList = function
            | "]" -> NIL
            |  x  -> match token x with
                     | (LITERAL v) -> let rest = tokenList (Queue.pop queue) in 
                                      PAIR (v, rest)
                     | _  -> (raise (Ill_Typed "Cannot have non-values in list"))
    and tokenPattern = function 
            | "(" -> let name = Queue.pop queue in 
                    let cons_params = tokenWhileDelim ")" tokenPattern in 
                    let param = PATTERN (name, cons_params) in 
                    param
            | "{" -> tuple_pattern (tokenWhileDelim "}" tokenPattern)
            | "false" -> VALUE (BOOLV false)
            | "true"  -> VALUE (BOOLV true)
            | "\"" -> let p = VALUE (STRING (Queue.pop queue)) in 
                let _   = Queue.pop queue in p
            | x    ->  if (Str.string_match (Str.regexp "[0-9]+") x 0) 
                       then VALUE (NUMBER (int_of_string x))
                       else (GENERIC x)
    and tokenMatchCases () = 
            if (Queue.length queue) <> 0 && (Queue.peek queue) = "|"
            then let _ = Queue.pop queue in (* popping "|" *)
                 let patterns = tokenWhileDelim "=" tokenPattern in
                 let exp  = token (Queue.pop queue) in
                  (tuple_pattern patterns, exp)::(tokenMatchCases ())
            else []
    and token = function 
            | "fn"  ->  let names = tokenWhileDelim "->" (fun s -> s) in 
                        let exp  =  token (Queue.pop queue) in 
                        LAMBDA (names, exp)
            | "let" -> let bindings = tokenWhileDelim "in" tokenDef in 
                        let exp = token (Queue.pop queue) in 
                        LET (bindings, exp)
            | "if"  -> let cond = token (Queue.pop queue) in 
                        let exp1 = token (Queue.pop queue) in 
                        let exp2 = token (Queue.pop queue) in 
                        IF (cond, exp1, exp2)
            | "["  -> LITERAL (tokenList (Queue.pop queue))
            | "("  -> let exp = token (Queue.pop queue) in 
                            (match exp with
                                | (VAR _) | (APPLY _) | (LAMBDA _) -> 
                                    (let args = tokenWhileDelim ")" token
                                     in APPLY (exp, args))
                                |  _      -> let _ = Queue.pop queue in exp)
            | "match" -> let exps = tokenWhileDelim "with" token in 
                         MATCH (TUPLE exps, tokenMatchCases ())
            | "false" -> LITERAL (BOOLV false)
            | "true"  -> LITERAL (BOOLV true)
            | "\"" -> let exp = LITERAL (STRING (Queue.pop queue)) in 
                let _   = Queue.pop queue in exp
            | "{" -> TUPLE (tokenWhileDelim "}" token)
            |  str ->  if (Str.string_match (Str.regexp "[0-9]+") str 0)
                            then LITERAL (NUMBER (int_of_string str))
                            else VAR str 
    and tokenDef = function 
            | "val" ->  let key = Queue.pop queue in 
                        if key = "rec"
                        then let name = Queue.pop queue in 
                             let _ = Queue.pop queue in (* for = *)
                             LETREC (name, token (Queue.pop queue))
                        else let _ = Queue.pop queue in (* for = *)
                            LETDEF (key, token (Queue.pop queue))
            | "datatype" -> let name = Queue.pop queue in 
                            let tyvars = tokenWhileDelim "=" pop_first_char in 
                            ADT (name, tyvars, tokenADT ())  
          |  name -> EXP (token (name))
      in tokenDef (Queue.pop queue)
(* 
   -----------------------------------------
        
    -------    EVALUATION    -------  

   -----------------------------------------
*)
(* 
    Given a matched pattern and argument, return 
    an association list of the parameters mapped to 
    their corresponding value

    pattern -> pattern -> (string * value)
*)
let rec extract_parameters p arg = match p, arg with 
    | (VALUE _),   (VALUE _)   -> []
    | (GENERIC x), _ -> [(x, pattern_to_value arg)]
    | (PATTERN (_, ps)), (PATTERN (_, ps')) -> 
        List.fold_left2 (fun acc p p' -> List.append (extract_parameters p p') acc) [] ps ps'
    | _   -> raise (Ill_Typed "Incorrectly matched patterns")
(* 
   Given a constructor, create a binding of the constructor in rho

   constructor -> string * value
*)
let rec eval_cons = function 
    | UNARYCONS (name, _) ->
        (name, 
        TYPECONS (fun args -> match args with 
                    | [v]     -> PATTERNV (PATTERN (name, [VALUE v]))
                    |  _   -> raise (Runtime_Error 
                                        ("Applied " ^ name ^ " constructor with "
                                         ^ (string_of_int (List.length args)) ^ 
                                         "arguments. Expected 1 argument."))))
    | NULLCONS name -> 
        (name, 
        TYPECONS (fun args -> match args with 
                    | []  -> PATTERNV (PATTERN (name, []))
                    |  _   -> raise (Runtime_Error 
                                        ("Applied " ^ name ^ " constructor with " 
                                          ^ (string_of_int (List.length args)) ^ 
                                          "arguments. Expected 0 arguments."))))
(* 
    Given a name and an expression, determine if 
    the name is free in the expression. 
*)
let rec freeExp name exp = 
    let rec free = function 
        | (VAR x) -> x = name 
        | (IF (e1, e2, e3)) -> List.exists free [e1; e2; e3]
        | (APPLY (f, args)) -> List.exists free (f::args)
        | (LAMBDA (names, body)) ->  not (List.exists ((=) name) names) && free body
        | (LET (bindings, body)) -> 
            let names = List.map (fun b -> match b with   
                                        | LETREC (n, e) | LETDEF (n, e) -> n 
                                        | _ -> raise (Runtime_Error "Ill formed let")) bindings in 
            let exps  = List.map (fun b -> match b with 
                                        | LETREC (n, e) | LETDEF (n, e) -> e 
                                        | _ -> raise (Runtime_Error "Ill formed let")) bindings in 
            let memberNames = List.exists ((=) name) names in 
            (not memberNames) && List.exists free exps || (not memberNames) && free body
        | (TUPLE exps) -> List.exists free exps
        | (MATCH (e, ps)) -> free e || (List.exists (fun (p, e) -> free e) ps)
        | (LITERAL _) -> false 
    in free exp

(* let _ = print_endline (string_of_bool (freeExp "x" (VAR "x")))  true *)
(* let _ = print_endline (string_of_bool (freeExp "y" (VAR "x"))) false *)
(* let _ = print_endline (string_of_bool (freeExp "y" (LET ([LETDEF ("x", VAR "y")], VAR "y")))) true *)
(* let _ = print_endline (string_of_bool (freeExp "x" (LET ([LETDEF ("x", VAR "y")], VAR "y")))) false *)
(* first binding of x references a free variable y, second creates a new bound variable y, returns bound variable y, should be true *)
(* let _ = print_endline (string_of_bool (freeExp "y" (LET ([LETDEF ("x", VAR "y"); LETDEF ("y", LITERAL (NUMBER 4))], VAR "y")))) *)
(* y is not free *)
(* let _ = print_endline (string_of_bool (freeExp "y" (LET ([LETDEF ("x", LITERAL (NUMBER 5)); LETDEF ("y", LITERAL (NUMBER 4))], VAR "y"))))  *)
(* y is free *)
(* let _ = print_endline (string_of_bool (freeExp "y" (LET ([LETDEF ("x", LITERAL (NUMBER 5)); LETDEF ("z", LITERAL (NUMBER 4))], VAR "y"))))   *)
(* let _ = print_endline (string_of_bool (freeExp "y" (LAMBDA (["x"; "y"; "z"], VAR("y"))))) *)
(* 
   Given an expression and rho, compute the value it returns

   exp -> (string * value) list -> value
*)
let rec eval_exp exp rho = 
    let rec eval = function 
        | (LITERAL v) -> v
        | (VAR x) -> lookup x rho
        | (IF (e1, e2, e3)) -> 
            let bool = eval e1 in 
                (match bool with 
                    | (BOOLV v) -> if v then eval e2 else eval e3
                    | _ -> raise (Ill_Typed "Condition is not a boolean."))
        | (APPLY (f, args)) -> 
            let closure = eval f in
            let values = List.map (fun a -> eval a) args in
                (match closure with 
                    | (CLOSURE (LAMBDA (names, body), copy_rho)) -> 
                        let rho' = List.append (zip names values) copy_rho in 
                        eval_exp body rho'
                    | (PRIMITIVE f) -> f values
                    | (TYPECONS f) -> f values
                    | _ -> raise (Ill_Typed "Cannot apply non-function."))
        | (LAMBDA (names, body)) -> 
            let rho_names = List.map fst rho in 
            let exists = List.exists (fun a -> List.mem a rho_names) names in 
            if exists 
            then raise (Runtime_Error "LAMBDA") 
            else (CLOSURE (LAMBDA (names, body), 
                            List.filter (fun (n, _) -> freeExp n exp) rho))
        | (LET (defs, body)) -> 
            let final_rho = List.fold_right (fun d rho' -> snd (eval_def d rho')) defs rho in 
            eval_exp body final_rho
        | (TUPLE exps) -> TUPLEV (List.map eval exps)
        | (MATCH (e, ps)) -> 
            let value_pattern =  value_to_pattern (eval e) in 
            let (p, case) = List.find (fun (p, case) -> pattern_covers p value_pattern) ps in 
            let env = extract_parameters p value_pattern in
            eval_exp case (List.append env rho)
    in eval exp  
(* 
   def -> (string * value) list -> (value * rho)
*)
and eval_def def rho = 
        match def with 
        | LETDEF (name, exp) -> 
            if name <> "it" && List.exists (fun n -> n = name) (List.map fst rho) 
            then raise (Runtime_Error  "LETDEF")
            else let value = eval_exp exp rho in 
                (value, (name, value)::rho)
        | LETREC (name, exp) -> (match exp with 
            | (LAMBDA _) -> 
                if List.exists (fun n -> n = name) (List.map fst rho) 
                then raise (Runtime_Error "LETREC")
                else let closure = eval_exp exp rho 
                    in (match closure with 
                            | (CLOSURE (l, c)) -> 
                                let rec rho' = (name, (CLOSURE (l, rho')))::rho in 
                                ((CLOSURE (l, rho')), rho')
                            |  _ -> raise (Ill_Typed "Expression in letrec is not a lambda"))
            | _ -> raise (Ill_Typed "Expression in letrec is not a lambda"))
        | EXP e -> eval_def (LETDEF ("it", e)) rho
        | ADT (name, tyvars, cons) -> 
            let bindings = List.map eval_cons cons in
            let rho' = List.append bindings rho in 
            (STRING (def_to_string def), rho')
(* 
   -----------------------------------------
        
    -------  TYPE INFERENCE    -------  

   -----------------------------------------
*)

let domain t = List.map (fun (x, _) -> x) t
let union xs ys = List.fold_left
      (fun acc x -> if (List.exists (fun y -> y = x) ys) then acc else x::acc) ys xs
let inter xs ys = List.fold_left
      (fun acc x -> if (List.exists (fun y -> y = x) ys) then x::acc else acc) [] xs
let diff xs ys = List.fold_left
      (fun acc x -> if (List.exists (fun y -> y = x) ys) then acc else x::acc) [] xs

let (^^) t1 t2 = EQ (t1, t2)
let (^^^) c1 c2 = CONJ (c1, c2)
let (-->) a t = match t with
  | TYVAR (a') -> if a = a' then [] else [(a, TYVAR a')]
  | tau        -> [(a, tau)]      

let rec insert y l = match l with
  | []    -> [y]
  | x::xs -> if y = x then l else x::(insert y xs)

let rec member y l = match l with
  | [] -> false
  | x::xs -> y = x || member y xs

let varsubst theta = 
  let rec find t a = match t with
    | [] -> TYVAR a
    | (a', x)::ps -> if a' = a then x else find ps a 
  in find theta 

let tysubst theta = 
  let rec sub tau = match tau with
    | TYVAR (a)     -> varsubst theta a
    | TYCON (tc)    -> TYCON tc
    | CONAPP(t, ts) -> CONAPP (sub t, List.map sub ts)
 in sub

let consubst theta =
  let rec subst c = match c with
  |  EQ   (t1, t2) -> tysubst theta t1  ^^ tysubst theta t2
  |  CONJ (c1, c2) -> subst c1 ^^^ subst c2
  |  TRIVIAL       -> c  
  in subst 

let compose (theta2, theta1) = 
  let d = union (domain theta1) (domain theta2) in
  let o f g = fun x -> f (g x) in
  let xd1 = o (tysubst theta2) in
  let xd2 = xd1 (varsubst theta1) in
  (* let rep = o ((tysubst theta2) (varsubst theta1)) in *)
  List.map (fun x -> (x, xd2 x)) d

let tyvarCt = ref 0

let freshtyvar _ = let () = tyvarCt := !tyvarCt + 1
  in TYVAR (string_of_int !tyvarCt)

let ftvs tau = 
  let rec getftvs curSet t = match t with
    | TYVAR(a) -> insert a curSet
    | TYCON(_) -> curSet
    | CONAPP(ty, tys) -> List.fold_left getftvs (getftvs curSet ty) tys
  in getftvs [] tau

let rec ftvsConstraint c = 
    let rec getftvs set = function 
        | EQ (t1, t2) -> union (union (ftvs t1) (ftvs t2)) set 
        | CONJ (c1, c2) -> union (ftvsConstraint c1) (ftvsConstraint c2)
        | TRIVIAL -> []
    in getftvs [] c

let ftvsGamma(_, free) = free

let findTyscheme s gamma = match gamma with
  | (env, free) ->
    let rec locate g = match g with
    | []               -> raise (Cringe "var inference led to missing type scheme")
    | (s', scheme)::xs -> if s' = s then scheme else locate xs
    in locate env

let bindtyscheme (x, ts, (g, f)) = match ts with 
  | FORALL(bound, t) -> ((x, ts)::g, union f (diff (ftvs t) bound))

let rec bindList ys zs l = match (ys, zs) with
  | (w::ws, x::xs) -> bindList ws xs ((w, x)::l)
  | ([], [])       -> l
  | _              -> raise typeInferenceBug

let instantiate ts tys = match ts with
  | FORALL(bound, t) -> tysubst (bindList bound tys []) t

let freshInstance ts = match ts with
  | FORALL(bound, tau) -> instantiate ts (List.map freshtyvar bound)

let rec conjoin c = match c with 
  | []       -> TRIVIAL
  | [c1]     -> c1
  | curC::cs -> curC ^^^ (conjoin cs)

let canonify ts = match ts with
  | FORALL(bound, tau) ->
    let genTyvarName n = String.cat "t" (string_of_int n) in
    let freenut = diff (ftvs tau) bound in
    let rec nextIdx n =
      if member (genTyvarName n) freenut then nextIdx (n + 1) else n in
    let rec newVars idx olds = match olds with
      | []    -> []
      | o::os -> let n = nextIdx idx in
        genTyvarName n :: (newVars(idx + 1) os) in
    let newBoundVars = newVars 0 bound in
    FORALL(newBoundVars, tysubst (bindList bound (List.map (fun x -> TYVAR x) newBoundVars) []) tau)
    

let generalize vars tau = 
  canonify (FORALL (diff (ftvs tau) vars, tau))

let confirmLambda e = match e with
  | LAMBDA(_, _) -> e
  | _            -> raise typeInferenceBug

let rec solve c = match c with
  | TRIVIAL      -> []
  | CONJ(c1, c2) -> 
      let t1 = solve c1 in
      let t2 = solve (consubst t1 c2) in
      compose (t2, t1)
  | EQ(t1, t2) -> match (t1, t2) with
    | (TYVAR a, TYVAR _)  -> a --> t2
    | (TYVAR a, TYCON _)   -> a --> t2
    | (TYVAR a, CONAPP _)  -> if member a (ftvs t2) then raise typeInferenceBug else a --> t2
    | (TYCON c1, TYCON c2) -> if c1 = c2 then [] else raise typeInferenceBug
    | (TYCON _, CONAPP _)  -> raise typeInferenceBug
    | (CONAPP(t1, t1s), CONAPP(t2, t2s)) -> 
        let rec zip l1 l2 acc = match (l1, l2) with
        | ([], [])       -> List.rev acc
        | (x::xs, y::ys) -> zip xs ys ((x, y)::acc)
        | _              -> raise typeInferenceBug in
        let zipped = zip t1s t2s [] in 
        List.fold_left(fun acc (t, t') -> compose(acc, solve(consubst acc (t ^^ t')))) (solve(t1 ^^ t2)) zipped
    | _                    -> solve (t2 ^^ t1)

let rec printType t = match t with 
    | TYVAR(a) -> print_string a
    | TYCON(c) -> print_string c
    | CONAPP(TYCON tc, [ty]) ->
      let () = print_string tc in let () = print_string " " in printType ty
    | _ -> print_string "Margaret Thatcher"  

let rec printConstraint c = match c with
    | TRIVIAL -> print_string "TRIVIAL"
    | EQ(t1, t2) -> 
        let () = print_string "(" in
        let () = print_string (type_to_string t1) in
        let () = print_string " ~ " in
        let () =  print_string (type_to_string t2) in print_string ")"
    | CONJ(c1, c2) ->
        let () = print_string "(" in
        let () = printConstraint c1 in
        let () = print_string " ^^^ " in
        let () = printConstraint c2 in print_string ")"

let rec typeof exp g = 
  (* 
        Given a patttern of a datatype constructor
        and the type of the constructor, return the
        bindings of the pattern generics mapped to their types
        + a constraint

        pattern -> ty -> (string * ty) list * con
    *)
    let extract_tau_params p tau = 
        let rec extract p tau = 
            (match p, tau with 
            | (GENERIC n), _ -> [(n, FORALL ([], tau))]
            | (PATTERN (_, ps)), (CONAPP (_, taus)) -> List.concat (List.map2 extract ps taus)
            | _ -> [])
        in match p with 
            | (GENERIC _) | (VALUE _) -> (extract p tau, TRIVIAL)
            | (PATTERN (x, ps)) -> 
                let instantiated = freshInstance (findTyscheme x g) in 
                match instantiated with
                | (CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); ret_ty])) -> 
                     (extract p instantiated, ret_ty ^^ tau)
                | _ -> raise (Ill_Typed "Pattern constructor does not have a function type.")
    in 
    let rec infer ex = match ex with
        | LITERAL(value) -> inferLiteral value

        | VAR(s) -> (freshInstance (findTyscheme s g), TRIVIAL)

        | IF(e1, e2, e3) ->
            let (t1, c1) = infer e1 in
            let (t2, c2) = infer e2 in
            let (t3, c3) = infer e3 in
                (t2, c1 ^^^ c2 ^^^ c3 ^^^ (t2 ^^ t3) ^^^ (t1 ^^ boolty))

        | LAMBDA(formals, b) -> 
            let alphas = List.map (fun form -> (form, freshtyvar())) formals in
            let newG = List.fold_left (fun acc (x, c) -> bindtyscheme (x, FORALL ([], c), acc)) g alphas in
            let (endty, endc) = typeof b newG in (funtype ((List.map snd alphas), endty), endc)

        | LET(ds, e) -> 
            let (defsC, finalGamma) = List.fold_left (fun (curC, curG) d -> 
                let (_, nextC, nextG, _) = typeOfDef d curG in
                (nextC, nextG)) (TRIVIAL, g) ds in
                let (tau, expC) = typeof e finalGamma in (tau, expC ^^^ defsC) 

        | TUPLE(es) -> let (taus, c) = typesof es g in (tuplety taus, c)

        | APPLY(f, es) -> (match (typesof (f::es) g) with
            | ([], _) -> raise (Cringe "invalid")
            | (fty::etys, con) -> 
                let crisp = freshtyvar() in
                let c = con ^^^ fty ^^ (funtype (etys, crisp)) in 
                (crisp, c))

        | MATCH (exp1, ps_exps) -> (match ps_exps with
          | (p1, e1)::pairs -> 
            let appendGamma bindings g = 
              List.fold_left (fun curG (x, ts) -> bindtyscheme (x, ts, curG)) g bindings in
            let (t0, c0) = typeof exp1 g in
            (*get first gamma, constraint, pTy, and eTy for folding later*)
            let (g1, c1, pTy1, rTy1) = 
              let (tyOfp1, cOfp1) = typeof (LITERAL(PATTERNV(p1))) g in
              let (bindings1, extract1C) = extract_tau_params p1 tyOfp1 in
              let newG = appendGamma bindings1 g in 
              let result1ty, result1C = typeof e1 newG in
              (newG, (c0 ^^^ cOfp1 ^^^ extract1C ^^^ result1C ^^^ (tyOfp1 ^^ t0)), tyOfp1, result1ty) in

            let (finalG, finalC) = List.fold_left (fun (curG, curC) (curP, curE) ->
              let (curPTy, curPC) = typeof (LITERAL(PATTERNV(curP))) g in (*shouldn't need curG here*)
              let (curBindings, curExtractC) = extract_tau_params curP pTy1 in
              let nextG = appendGamma curBindings curG in
              let (curResTy, curResC) = typeof curE nextG in
              let nextC = curC ^^^ (curPTy ^^ pTy1) ^^^ (curResTy ^^ rTy1) ^^^ curExtractC ^^^ curPC in
              (nextG, nextC)
            ) (g1, c1) pairs in
            (rTy1, finalC)
          | _ -> raise (Ill_Typed "bad match inference"))

    and inferLiteral v = match v with
        | STRING(_) -> (strty, TRIVIAL)
        | NUMBER(_) -> (intty, TRIVIAL)
        | BOOLV(_) -> (boolty, TRIVIAL)
        | NIL -> (freshInstance (FORALL (["a"], listty (TYVAR "a"))), TRIVIAL)
        | PAIR(e, v) -> 
            let (t1, c1) = infer (LITERAL e) in
            let (t2, c2) = infer (LITERAL v) in
            (t2, c1 ^^^ c2 ^^^ (listty t1 ^^ t2))
        | _ -> (boolty, TRIVIAL)
    and typesof es g = List.fold_right (fun e (ts, c) ->
            let (curty, curc) = typeof e g in
            (curty::ts, c ^^^ curc)) es ([], TRIVIAL) 

  in infer exp


(* (tyscheme, con, type env, output string) *)
and typeOfDef d g = 
  let rec inferDef def = match def with 
    | LETDEF(n, e) -> 
      let (tau, c) = typeof e g in
      let theta = solve c in
      let crisps = inter (domain theta) (ftvsGamma g) in
      let finalC = conjoin(List.map (fun x -> TYVAR x ^^ varsubst theta x) crisps) in
      let ligma = generalize (union (ftvsGamma g) (ftvsConstraint finalC)) ((tysubst theta) tau) in
      let newGamma = bindtyscheme(n, ligma, g) in
      (ligma, finalC, newGamma, "")
      
    (* possible bug due to using newGamma underneath its definition? type rules say to use gamma *)
    | LETREC(n, e) -> 
      let _ = confirmLambda e in
      let alpha = freshtyvar() in
      let newGamma = bindtyscheme(n, FORALL([], alpha), g) in
      let (tau, c) = typeof e newGamma in
      let c2 = c ^^^ (alpha ^^ tau) in
      let theta = solve c2 in
      let crisps = inter (domain theta) (ftvsGamma g) in
      let finalC = conjoin(List.map (fun x -> TYVAR x ^^ varsubst theta x) crisps) in
      let ligma = generalize (union (ftvsGamma g) (ftvsConstraint finalC)) ((tysubst theta) tau) in
      let finalGamma = bindtyscheme(n, ligma, g) in
      (ligma, finalC, finalGamma, "")

    | EXP(e) -> typeOfDef (LETDEF ("it", e)) g

    | ADT(name, alphas, cs) -> raise (Ill_Typed "Not implemented yet")
  in inferDef d

let printExpType e =
    let (tau, _) = typeof e ([], []) in let () = printType tau in print_endline ""

(*returns string forms of type and constraint*)
let debugExpType e = 
  let (tau, c) = typeof e ([], []) in
  let () = printType tau in let () = print_string ", " in let () = printConstraint c in print_endline ""

(* let _ = print_endline (list_to_string 
                            (fun (n, t) -> "(" ^ n ^ ", " ^ type_to_string t ^ ")") 
                            (extract_tau_params (cons (VALUE (NUMBER 56)) (GENERIC "xs")) 
                                                (funtype ([tuple [(TYVAR "'a"); (listty (TYVAR "'a"))]], (listty (TYVAR "'a")))))) *)
(* 
   -----------------------------------------
        
    -------  KINDING! -------  

   -----------------------------------------
*)
let rec eqKind k k' = match k, k' with 
    | (TYPE, TYPE) -> true
    | (INWAITING (ks, k), INWAITING (ks', k')) -> eqKind k k' && (List.for_all2 eqKind ks ks')
    | _             -> false


let kindOf tau delta = 
    let rec kind = function 
        | (TYCON name) | (TYVAR name) -> lookup name delta
        | (CONAPP (TYCON "tuple", taus)) -> 
            if (List.for_all (fun t -> kind t = TYPE) taus)
            then TYPE
            else raise (Ill_Typed ("Tried to apply tuple type to invalid types")) 
        | (CONAPP (tau, taus)) -> 
            (match kind tau with 
                | INWAITING (kinds, result_kind) -> 
                    if List.for_all2 eqKind kinds (List.map kind taus)
                    then result_kind
                    else raise (Ill_Typed "Tried to apply type constructor with wrong/unequal types.")
                | _                 -> raise (Ill_Typed "Tried to apply non-type constructor with types."))
        
    in kind tau

let asType delta tau = (match kindOf tau delta with 
    | TYPE -> true
    | _    -> raise (Ill_Typed (String.cat (type_to_string tau) " is waiting for another type.")))

(* 
   -----------------------------------------
        
    -------  Datatype Evaluation -------  

   -----------------------------------------
*)
(* 
   Given a type, returns the most general pattern of the type

   type_to_pattern : tau -> pattern
*)
let type_to_pattern = function 
    | (CONAPP (TYCON "tuple", taus)) -> PATTERN ("TUPLE", List.map (fun _ -> GENERIC "_") taus)
    | _                              -> GENERIC "_"

(* 
   Given a constructor of some datatype, returns the most general pattern 
   of the constructor

    constructor_to_pattern : constructor -> pattern
*)
let constructor_to_pattern = function 
    | (NULLCONS name) -> PATTERN (name, [])
    | (UNARYCONS (name, tau)) -> PATTERN (name, [type_to_pattern tau])
(* 
   Given a datatype definition, introduce the defintion into
   the Pi and Delta environment.

   def -> (string * pattern list) -> (string * kind) -> 
        (string * pattern list) * (string * kind)
*)
let intro_adt d pi delta = match d with 
    | ADT (name, alphas, cs) -> 
        let _ = print_endline (def_to_string d) in
        let eq_name = fun (n, _) -> name = n in
        if List.exists eq_name pi || List.exists eq_name delta
        then raise (Ill_Typed ("The datatype already exists."))
        else 
        let kind = match alphas with 
                    | [] -> TYPE 
                    | _  -> INWAITING (List.map (fun _ -> TYPE) alphas, TYPE)
        in
        let bs = (name, kind)::(List.map (fun a -> (a, TYPE)) alphas) in 
        let delta' = List.append bs delta in 
        let curry_as_type = asType delta' in
        let _ = List.for_all (fun c -> match c with 
                                | (NULLCONS _) -> true 
                                | (UNARYCONS (name, tau)) -> curry_as_type tau) 
                cs
        in
        let ps = List.map constructor_to_pattern cs in
        let pi' = (name, ps)::pi in  
        ((name, kind)::delta, pi')
    | _      -> (delta, pi)

(* 
   -----------------------------------------
        
    -------  ENVIRONMENTS    -------  
    
   -----------------------------------------
*)
let math_primop fn = PRIMITIVE (fun xs -> match xs with
                                    ((NUMBER a)::(NUMBER b)::[]) -> NUMBER (fn a b)
                                    | _ -> raise (Ill_Typed "Cannot apply math operation to non-numbers."))

let bin_primop fn = PRIMITIVE (fun xs -> match xs with 
                                    ((BOOLV a)::(BOOLV b)::[]) -> BOOLV (fn a b)
                                    | _ -> raise (Ill_Typed "Cannot apply boolean operation to non-booleans."))
let math_ty = funtype ([intty; intty], intty)
let alpha = TYVAR "a"

let initial_basis = 
    [
    ("<", PRIMITIVE (fun xs -> match xs with
                            ((NUMBER a)::(NUMBER b)::[]) -> BOOLV (a < b)
                            | _ -> raise (Ill_Typed "Cannot apply < to non-numbers.")),
            math_ty);
    (">", PRIMITIVE (fun xs -> match xs with
                            ((NUMBER a)::(NUMBER b)::[]) -> BOOLV (a > b)
                            | _ -> raise (Ill_Typed "Cannot apply > to non-numbers.")),
            math_ty);
    ("=", PRIMITIVE (fun xs -> match xs with 
                                   ((NUMBER a)::(NUMBER b)::[]) -> BOOLV (a = b)
                                 | ((BOOLV a)::(BOOLV b)::[])   -> BOOLV (a = b)
                                 | ((STRING a)::(STRING b)::[]) -> BOOLV (a = b)
                                 | _        -> raise (Ill_Typed "Cannot apply = to non primitives or mixed types")),
            funtype ([alpha; alpha], boolty));
    ("-", math_primop (-), math_ty);
    ("+", math_primop (+), math_ty);
    ("/", math_primop (/), math_ty);
    ("*", math_primop ( * ), math_ty);
    ("mod", math_primop (mod), math_ty);
    ("car", PRIMITIVE (fun xs -> match xs with [(PAIR (v, v'))] -> v | _ -> raise (Ill_Typed "Cannot apply car to non-lists")),
        funtype ([listty alpha], alpha));
    ("cdr", PRIMITIVE (fun xs -> match xs with [(PAIR (v, v'))] -> v' | _ -> raise (Ill_Typed "Cannot apply cdr to non-lists")),
        funtype([listty alpha], listty alpha));
    ("null?", PRIMITIVE (fun xs -> match xs with [NIL] -> BOOLV true | _ -> BOOLV false), funtype([listty alpha], boolty));
    ("CONS", TYPECONS (fun arg -> match arg with 
                                | [TUPLEV [v; vs]] -> PAIR (v, vs)
                                | _ -> raise (Ill_Typed "CONS applied to non-tuple")),
            funtype([tuplety [alpha; (listty alpha)]], (listty alpha)));
    ("NIL", TYPECONS (fun arg -> match arg with 
                                | [] -> NIL
                                | _ -> raise (Ill_Typed "NIL applied to args")),
            funtype([], (listty alpha)))
    ]
(* 
  Environment association list of names to list of pattern constructors
*)
let pi = [("list", list_patterns); ("tuple", []);]
let delta = [("int", TYPE); ("bool", TYPE); ("string", TYPE); ("list", INWAITING ([TYPE], TYPE)); ]

(*
    Environment of variables to their types

*)
let (rho, gamma) = List.fold_left 
                    (fun (r, g) (n, v, t) -> 
                        ((n, v) :: r, (n, generalize [] t) :: g))
                    ([], [])
                    initial_basis


let interpret_def (rho, pi, delta, gamma) def = 
    let (ty, _, gamma', str) = typeOfDef def gamma in
    let (delta', pi') = intro_adt def pi delta in
    let (value, rho') = eval_def def rho in
    (value, scheme_to_string ty, rho', pi', delta', gamma')

let (_, _, rho, pi, delta, gamma) = List.fold_left 
                        (fun (_, _, r, p, d, g) line -> interpret_def (r, p, d, g) (tokenize (parse line)))
                        (STRING "null", "null", rho, pi, delta, (gamma, []))
                        [
                            "val && = fn a b -> if a b false"; 
                            "val || = fn a b -> if a true b";
                            "val rec exists? = fn f xs -> if (null? xs) false (|| (f (car xs)) (exists? f (cdr xs)))";
                            "val rec all? = fn f xs -> if (null? xs) true (&& (f (car xs)) (all? f (cdr xs)))";
                        ] 

(* 
    interpret_lines runs indefintely, 
    accepting input from stdin and parsing it 

    typeOfDef : (tyscheme, con, type env, output string)
*)
let rec interpret_lines rho pi delta gamma = 
    let rec interpret () = 
        let _ = print_string "> " in 
        try 
            let tokens = (parse (read_line ())) in 
            let def = tokenize tokens in 
            let (v, t, rho', pi', delta', gamma') = interpret_def (rho, pi, delta, gamma) def in 
            let _ = print_endline (value_to_string v ^ " : " ^ t) in 
            interpret_lines rho' pi' delta' gamma'
        with error -> 
            let _ = print_error error in 
            interpret ()
    in interpret ()


let () = interpret_lines rho pi delta gamma

    
