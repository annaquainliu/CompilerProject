
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
                | ' ' | ';' | '(' | ')' | '[' | ']' | ',' | '"' -> 
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
    

(* Expression/Definitions! *)

type exp = LITERAL of value
         | VAR of string 
         | IF of exp * exp * exp
         | APPLY of exp * exp list 
         | LAMBDA of string list * exp
         | LET of def list * exp
and value =    STRING of string 
            |  NUMBER of int
            |  BOOLV  of bool
            |  NIL
            |  PAIR of value * value
            |  CLOSURE of exp * (string * value) list
            |  PRIMITIVE of (value list -> value)
and def =  LETDEF of string * exp
         | LETREC of string * exp 
         | EXP of exp

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


(*
    Kind Environment:

    Mapping of names to kinds.

    Every time a user create a valid datatype, the datatype will
    be added to the kind environment.
*)

(* Type or type in waiting *)
type kind = TYPE | INWAITING of (kind list * kind)

let initial_delta = [("int", TYPE); ("bool", TYPE); ("string", TYPE); 
                        ("list", INWAITING ([TYPE], TYPE));]
(* 
let kindof tau Delta = 
    let eqKind x y = 
       (match x, y with
            | TYPE, TYPE -> true
            | (INWAITING (kinds, kind), INWAITING (kinds', kind')) ->  
                eqKinds kinds kinds' && eqKind kind kind'
            | _ -> false)
    and eqKinds xs ys =
        match xs, ys with 
            | ([], []) -> true 
            | (kind::kinds, kind'::kinds') -> eqKind kind kind' && eqKinds kinds kinds' 
            | _ -> false
    let badkind = (fun tau -> (kind tau) <> TYPE)
    let kind = match tau with 
                | (TYVAR a) -> lookup a Delta
                | (TYCON c) -> lookup c Delta
                | (CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args)], result)) -> 
                    match kind result with 
                        | TYPE -> if List.exists badkind args 
                                  then raise (KindError "Argument gave kind error")
                                  else TYPE
                        | _ -> raise (KindError "") 
                | (CONAPP (TYCON "tuple", [taus])) -> 
                    if List.exists badkind taus 
                    then raise (KindError "Tuple argument gave kind error")
                    else TYPE
                | (CONAPP (tau, taus)) -> 
                    match kind tau with 
                        | (INWAITING (kinds, kind)) -> 
                            let conapp_kinds = map kind 
    in kind tau *)
    

(* fun kindof (tau, Delta) =
  let (* definition of internal function [[kind]] 388a *)
      fun kind (TYVAR a) =
            (find (a, Delta)
             handle NotFound _ => raise TypeError ("unknown type variable " ^ a)
                                                                               )
      (* definition of internal function [[kind]] 388b *)
        | kind (TYCON c) =
            (find (c, Delta)
             handle NotFound _ => raise TypeError ("unknown type constructor " ^
                                                                             c))
      (* definition of internal function [[kind]] 388c *)
        | kind (FUNTY (args, result)) =
            let fun badKind tau = not (eqKind (kind tau, TYPE))
            in  if badKind result then
                  raise TypeError "function result is not a type"
                else if List.exists badKind args then
                  raise TypeError "argument list includes a non-type"
                else
                  TYPE
            end
      (* definition of internal function [[kind]] 388d *)
        | kind (CONAPP (tau, actuals)) =
            (case kind tau
               of ARROW (formal_kinds, result_kind) =>
                    if eqKinds (formal_kinds, map kind actuals) then
                        result_kind
                    else
                        raise TypeError ("type constructor " ^ typeString tau ^
                                         " applied to the wrong arguments")
                | TYPE =>
                    raise TypeError ("tried to apply type " ^ typeString tau ^
                                     " as type constructor"))
      (* definition of internal function [[kind]] 389a *)
        | kind (FORALL (alphas, tau)) =
            let val Delta' =
                  foldl (fn (a, Delta) => bind (a, TYPE, Delta)) Delta alphas
            in  case kindof (tau, Delta')
                  of TYPE    => TYPE
                   | ARROW _ =>
                       raise TypeError
                                      "quantifed a non-nullary type constructor"
            end *)

(* let kind = ["string" ] *)

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
    and value_to_string = function 
        | (STRING s) -> "STRING(" ^ s ^ ")"
        | (NUMBER n) -> "NUMBER(" ^ string_of_int n ^ ")"
        | (BOOLV false) -> "BOOLV(false)"
        | (BOOLV true) -> "BOOLV(true)"
        | NIL -> "NIL"
        | (PAIR (e, v)) -> "PAIR(" ^ value_to_string e ^ ", " ^ value_to_string v ^ ")"
        | (CLOSURE (LAMBDA (args, e), rho))  -> "CLOSURE(" ^ exp_to_string (LAMBDA (args, e)) ^ ", rho)"
        | (PRIMITIVE f) -> "PRIM"
        | _ -> "ERROR"
(* 
  Takes in a queue of strings, and then tokenizes the result

  string queue -> def
*)
let tokenize queue = 
    let rec tokenLambda () = 
        let rec tokenParams = function 
                | "->"  -> []
                | x     -> x::tokenParams (Queue.pop queue)
        in 
        let names = tokenParams (Queue.pop queue) in 
        let exp  =  token (Queue.pop queue) in 
        LAMBDA (names, exp)
    and tokenLetExp () =
        let rec tokenLetBindings = function 
            | "in" -> []
            |  name   -> let def = tokenDef name in 
                            def::tokenLetBindings (Queue.pop queue)
        in  let bindings = tokenLetBindings (Queue.pop queue) in
            let exp = token (Queue.pop queue) in 
            LET (bindings, exp)
      and tokenList = function
            | "]" -> NIL
            |  x  -> match token x with
                     | (LITERAL v) -> let rest = tokenList (Queue.pop queue) in 
                                      PAIR (v, rest)
                     | _  -> (raise (Ill_Typed "Cannot have non-values in list"))
      and tokenApplyArgs = function 
             | ")" -> []
             |  x  -> let arg = token x in 
                      let args = tokenApplyArgs (Queue.pop queue) in 
                      arg::args
      and token = function 
          | "fn"  -> tokenLambda ()
          | "let" -> tokenLetExp ()
          | "if"  -> let cond = token (Queue.pop queue) in 
                     let exp1 = token (Queue.pop queue) in 
                     let exp2 = token (Queue.pop queue) in 
                    IF (cond, exp1, exp2)
          | "\"" -> let exp = LITERAL (STRING (Queue.pop queue)) in 
                    let _   = Queue.pop queue in exp
          | "["  -> LITERAL (tokenList (Queue.pop queue))
          | "("  -> let exp = token (Queue.pop queue) in 
                        (match exp with
                            | (VAR _) | (APPLY _) | (LAMBDA _) -> 
                                (let args = tokenApplyArgs (Queue.pop queue) in APPLY (exp, args))
                            |  _      -> let _ = Queue.pop queue in exp)
          | "false" -> LITERAL (BOOLV false)
          | "true"  -> LITERAL (BOOLV true)
          |  str    ->  if (Str.string_match (Str.regexp "[0-9]+") str 0)
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

    