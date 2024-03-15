
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
exception KindError of string
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
            | "false" -> PATTERN ("BOOL", [VALUE (BOOLV false)])
            | "true"  -> PATTERN ("BOOL", [VALUE (BOOLV true)])
            | "\"" -> let p = PATTERN ("STRING", [GENERIC (Queue.pop queue)]) in 
                let _   = Queue.pop queue in p
            | x    ->  if (Str.string_match (Str.regexp "[0-9]+") x 0) 
                       then PATTERN ("INT", [VALUE (NUMBER (int_of_string x))])
                       else (GENERIC x)
    and tokenMatchCases () = 
            if (Queue.length queue) <> 0 && (Queue.peek queue) = "|"
            then let _ = Queue.pop queue in (* popping "|" *)
                 let patterns = tokenWhileDelim "=" tokenPattern in
                 let exp  = token (Queue.pop queue) in
                 (patterns, exp)::(tokenMatchCases ())
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
                         MATCH (exps, tokenMatchCases ())
            | "false" -> LITERAL (BOOLV false)
            | "true"  -> LITERAL (BOOLV true)
            | "\"" -> let exp = LITERAL (STRING (Queue.pop queue)) in 
                let _   = Queue.pop queue in exp
            | "{" -> TUPLE (tokenWhileDelim "}" token)
            |  str ->  if (Str.string_match (Str.regexp "[0-9]+") str 0)
                            then LITERAL (NUMBER (int_of_string str))
                            else VAR str 
    and tokenDef = function 
          | "val" -> tokenDef (Queue.pop queue)
          | "rec" -> let name = Queue.pop queue in 
                     let _ = Queue.pop queue in 
                     let keyword = Queue.pop queue in
                     LETREC (name, token keyword)
          |  name -> let _ = Queue.pop queue in LETDEF (name, token (Queue.pop queue))
      in if (Queue.peek queue) = "val" 
         then tokenDef (Queue.pop queue)
         else EXP (token (Queue.pop queue))

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
                    | _ -> raise (Ill_Typed "Cannot apply non-function."))
        | (LAMBDA (names, body)) -> 
            let rho_names = List.map fst rho in 
            let exists = List.exists (fun a -> List.mem a rho_names) names in 
            if exists then raise (Shadowing "LAMBDA") else (CLOSURE (LAMBDA (names, body), rho))
        | (LET (defs, body)) -> 
            let final_rho = List.fold_right (fun d rho' -> snd (eval_def d rho')) defs rho in 
            eval_exp body final_rho
        | (TUPLE exps) -> TUPLEV (List.map eval exps)
        | m  -> (STRING (exp_to_string m))
    in eval exp  
(* 
   def -> (string * value) list -> (value * rho)
*)
and eval_def def rho = 
        match def with 
        | LETDEF (name, exp) -> 
            if name <> "it" && List.exists (fun n -> n = name) (List.map fst rho) 
            then raise (Shadowing  "LETDEF")
            else let value = eval_exp exp rho in 
                (value, (name, value)::rho)
        | LETREC (name, exp) ->
            if List.exists (fun n -> n = name) (List.map fst rho) 
            then raise (Shadowing "LETREC")
            else let closure = eval_exp exp rho 
                  in (match closure with 
                        | (CLOSURE (LAMBDA (args, e), c)) -> 
                            let rec rho' = (name, (CLOSURE (LAMBDA (args, e), rho')))::rho in 
                            ((CLOSURE (LAMBDA (args, e), rho')), rho')
                        |  _ -> raise (Ill_Typed "Expression in letrec is not a lambda"))
        | EXP e -> eval_def (LETDEF ("it", e)) rho

let math_primop fn = PRIMITIVE (fun xs -> match xs with
                                    ((NUMBER a)::(NUMBER b)::[]) -> NUMBER (fn a b)
                                    | _ -> raise (Ill_Typed "Cannot apply math operation to non-numbers."))

let bin_primop fn = PRIMITIVE (fun xs -> match xs with 
                                    ((BOOLV a)::(BOOLV b)::[]) -> BOOLV (fn a b)
                                    | _ -> raise (Ill_Typed "Cannot apply boolean operation to non-booleans."))
let initial_rho = 
    [
    ("<", PRIMITIVE (fun xs -> match xs with
                            ((NUMBER a)::(NUMBER b)::[]) -> BOOLV (a < b)
                            | _ -> raise (Ill_Typed "Cannot apply < to non-numbers.")));
    (">", PRIMITIVE (fun xs -> match xs with
                            ((NUMBER a)::(NUMBER b)::[]) -> BOOLV (a > b)
                            | _ -> raise (Ill_Typed "Cannot apply > to non-numbers.")));
    ("=", PRIMITIVE (fun xs -> match xs with 
                                   ((NUMBER a)::(NUMBER b)::[]) -> BOOLV (a = b)
                                 | ((BOOLV a)::(BOOLV b)::[])   -> BOOLV (a = b)
                                 | ((STRING a)::(STRING b)::[]) -> BOOLV (a = b)
                                 | _        -> raise (Ill_Typed "Cannot apply = to non-primitives.")));
    ("-", math_primop (-));
    ("+", math_primop (+));
    ("/", math_primop (/));
    ("*", math_primop ( * ) );
    ("mod", math_primop (mod));
    ("car", PRIMITIVE (fun xs -> match xs with [(PAIR (v, v'))] -> v | _ -> raise (Ill_Typed "Cannot apply car to non-lists")));
    ("cdr", PRIMITIVE (fun xs -> match xs with [(PAIR (v, v'))] -> v' | _ -> raise (Ill_Typed "Cannot apply car to non-lists")));
    ("null?", PRIMITIVE (fun xs -> match xs with [NIL] -> BOOLV true | _ -> BOOLV false))
    ]

let standard_lib = List.fold_left 
                        (fun acc a -> (snd (eval_def (tokenize (parse a)) acc)) ) 
                        initial_rho
                        [
                            "val && = fn a b -> if a b false"; 
                            "val || = fn a b -> if a true b";
                            "val rec exists? = fn f xs -> if (null? xs) false (|| (f (car xs)) (exists? f (cdr xs)))";
                            "val rec all? = fn f xs -> if (null? xs) true (&& (f (car xs)) (all? f (cdr xs)))";
                        ] 

(* 
    interpret_lines runs indefintely, 
   accepting input from stdin and parsing it 
*)
let rec interpret_lines rho = 
    let _ = print_string "> " in 
    let tokens = (parse (read_line ())) in 
    let def = tokenize tokens in 
    let (value, rho') = eval_def def rho in
    let () = print_endline (value_to_string value) in 
    interpret_lines rho'

let () = interpret_lines standard_lib

    