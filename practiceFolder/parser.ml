
(* PARSING INPUT *)
let pop_first_char input = String.sub input 1 ((String.length input) - 1)

let list_to_string f xs = 
    let rec stringify = function 
      |  []         -> ""
      |  [x]        -> (f x)
      |  (x::xs)    -> (f x) ^ ", " ^ stringify xs
    in "[" ^ stringify xs ^ "]"

exception Not_Found of string
exception Ill_Typed of string 
exception Mismatch_Lengths
exception Shadowing of string
exception Ill_Formed of string
(* 
    Returns the value of a key in an association list
   'a -> ('a * 'b) list -> 'b
*)
let rec lookup k = function 
            | [] -> raise (Not_Found ("Could not find variable '" ^ k ^ "'"))
            | ((k', v)::rest) -> if k' = k then v else lookup k rest

let rec zip xs ys = match xs, ys with
    | [], [] -> []
    | k::ks, v::vs -> (k, v)::zip ks vs
    | _ ,      _       -> raise Mismatch_Lengths

let fst = function (a, b) -> a
let snd = function (a, b) -> b
(* 
   parse takes in string input and returns a list of tokens,
   which is any keyword or string deliminated by a space
*)
let rec parse input = 
    let rec parse_string input = match input.[0] with 
        | '"' -> ("", pop_first_char input)
        | c   -> let (str, leftover) = parse_string (pop_first_char input) 
                 in ((String.make 1 c) ^ str, leftover)
    in
    let rec extract input str = match input with 
        | "" -> []
        | _  -> (match input.[0] with 
                | ' ' | ';' | '(' | ')' | '[' | ']' | ',' | '"' | '{' | '}' -> 
                    if input.[0] = '"'
                    then let (parsed, leftover) = parse_string (pop_first_char input)
                         in  str::(String.make 1  input.[0])::
                             parsed::(String.make 1 '"')::(extract leftover "")
                    else str::(String.make 1  input.[0])::extract (pop_first_char input) ""  
                | c -> if (String.length input) = 1
                       then [(str ^ String.make 1 c)]
                       else (extract (pop_first_char input) (str ^ (String.make 1 c))))
    in 
    let tokens = (extract input "") in 
    List.filter (fun t -> t <> " " && t <> "") tokens
   
(* Patterns *)

type exp = LITERAL of value
         | VAR of string 
         | IF of exp * exp * exp
         | APPLY of exp * exp list 
         | LAMBDA of string list * exp
         | LET of def list * exp
         | MATCH of exp list * ((pattern list) * exp) list
         | TUPLE of (exp list)
and value =    STRING of string 
            |  NUMBER of int
            |  BOOLV  of bool
            |  NIL
            |  PAIR of value * value
            |  CLOSURE of exp * (string * value) list
            |  PRIMITIVE of (value list -> value)
            |  TUPLEV of (value list)
and def =  LETDEF of string * exp
         | LETREC of string * exp 
         | EXP of exp
and pattern = GENERIC of string
         |  VALUE of value 
         |  PATTERN of string * (pattern list)

(* Types! *)
type ty = TYCON of string | TYVAR of string | CONAPP of ty * ty list
let intty = TYCON "int"
let boolty = TYCON "bool"
let strty = TYCON "string"
let listty t = CONAPP(TYCON "list", [t])
let tuple list = CONAPP (TYCON "tuple", list)
let funtype (args, result) =
  CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result])

type tyscheme = FORALL of string list * ty

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
        | (TUPLE exps) -> "TUPLE(" ^ (list_to_string exp_to_string exps) ^ ")"
    and value_to_string = function 
        | (STRING s) -> "STRING(" ^ s ^ ")"
        | (NUMBER n) -> "NUMBER(" ^ string_of_int n ^ ")"
        | (BOOLV false) -> "BOOLV(false)"
        | (BOOLV true) -> "BOOLV(true)"
        | NIL -> "NIL"
        | (PAIR (e, v)) -> "PAIR(" ^ value_to_string e ^ ", " ^ value_to_string v ^ ")"
        | (CLOSURE (LAMBDA (args, e), rho))  -> "CLOSURE(" ^ exp_to_string (LAMBDA (args, e)) ^ ", rho)"
        | (PRIMITIVE f) -> "PRIM"
        | (TUPLEV l) -> "TUPLEV(" ^ (list_to_string value_to_string l) ^ ")"
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
(* 
  Takes in a queue of strings, and then tokenizes the result

  string queue -> def
*)
let rec whileDelim delim f = function 
    | x::xs -> if x = delim 
               then ([], xs)
               else let fst = f x in 
                    let (exps, rest) = whileDelim delim f xs in 
                    (fst::exps, rest)
    | _     -> raise (Ill_Formed " while ")

let rec tokenize = function 
    | x::xs -> 
        (match x with 
            |  "fn" -> let (params, queue) = whileDelim "->" (fun a -> a) xs in 
                    LAMBDA (params, tokenize queue)
            |  "if" -> tokenize xs 
            |  "false"  -> LITERAL (BOOLV false)
            |  "true"   -> LITERAL (BOOLV true)
            |  "\""     -> (match xs with 
                            | str::"\""::s -> LITERAL (STRING str)
                            | _             -> raise Ill_Formed ("Ill-formed string"))
            | str       -> if (Str.string_match (Str.regexp "[0-9]+") str 0)
                            then LITERAL (NUMBER (int_of_string str))
                            else VAR str
        )
    | _     -> raise (Ill_Formed " token is ill formed. ")


(* 
    interpret_lines runs indefintely, 
   accepting input from stdin and parsing it 
*)
let rec interpret_lines rho = 
    let _ = print_string "> " in 
    let tokens = (parse (read_line ())) in 
    let _ = print_endline (list_to_string (fun a -> a) tokens) in
    print_endline (exp_to_string (tokenize tokens)) 
    (* let def = tokenize tokens in 
    let (value, rho') = eval_def def rho in
    let () = print_endline (value_to_string value) in  
    interpret_lines rho' *)

let () = interpret_lines []

    