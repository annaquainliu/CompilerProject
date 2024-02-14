
(* PARSING INPUT *)
let pop_first_char input = String.sub input 1 ((String.length input) - 1)

let list_to_string f xs = 
    let rec stringify = function 
      |  []         -> ""
      |  [x]        -> (f x)
      |  (x::xs)    -> (f x) ^ ", " ^ stringify xs
    in "[" ^ stringify xs ^ "]"

exception Not_Found
exception Ill_Typed
exception Mismatch_Lengths
exception Shadowing
(* 
    Returns the value of a key in an association list
   'a -> ('a * 'b) list -> 'b
*)
let rec lookup k = function 
            | [] -> raise Not_Found
            | ((k', v)::rest) -> if k' = k then v else lookup k rest

(* let rec zip = function 
    | [] [] -> []
    | k::ks v::vs -> (k, v)::zip(ks, vs)
    | _       _       -> raise Mismatch_Lengths *)

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
    

(* TOKENIZING! *)

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
            |  UNIT
            |  PAIR of exp * value
            |  CLOSURE of exp * (string * value) list
and def =  LETDEF of string * exp
         | LETREC of string * exp 
         | EXP of exp


let rec def_to_string = function 
         | (LETDEF (x, e)) -> "LETDEF(" ^ x ^ ", " ^ exp_to_string e ^ ")"
         | (LETREC (x, e)) -> "LETREC(" ^ x ^ ", " ^ exp_to_string e ^ ")"
         | (EXP e) -> "EXP(it, " ^ exp_to_string e ^ ")"
    and exp_to_string = function 
         | (LITERAL v) ->
            let rec value_to_string = function 
                    | (STRING s) -> "STRING(" ^ s ^ ")"
                    | (NUMBER n) -> "NUMBER(" ^ string_of_int n ^ ")"
                    | (BOOLV false) -> "BOOLV(false)"
                    | (BOOLV true) -> "BOOLV(true)"
                    | NIL -> "NIL"
                    | UNIT -> "UNIT"
                    | (PAIR (e, v)) -> "PAIR(" ^ exp_to_string e ^ ", " ^ value_to_string v ^ ")"
                    | _  -> "error"
            in value_to_string v
        | (VAR s) -> "VAR(" ^ s ^ ")"
        | (IF (e, e2, e3)) -> "IF(" ^ exp_to_string e ^ ", " ^ exp_to_string e2 ^ ", " ^ exp_to_string e3 ^ ")"
        | (APPLY (f, args)) -> "APPLY(" ^ exp_to_string f ^ ", " ^ list_to_string exp_to_string args ^")"
        | (LAMBDA (xs, e))  -> "LAMBDA(" ^ list_to_string (fun a -> a) xs ^ ", " ^ exp_to_string e ^ ")"
        | (LET (ds, e)) -> "LET(" ^ list_to_string def_to_string ds ^ ", " ^ exp_to_string e ^ ")"
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
              |  x  -> let v = token x in
                       let rest = tokenList (Queue.pop queue) in 
                       PAIR (v, rest)
      and tokenApplyArgs = function 
              | ")" -> []
              |  x  -> let arg = (token x) in 
                       let args = tokenApplyArgs (Queue.pop queue) in 
                       arg::args 
      and token = function 
          | "fn"  -> tokenLambda ()
          | "let" -> tokenLetExp ()
          | "if"  -> let cond = token (Queue.pop queue) in 
                     let exp1 = token (Queue.pop queue) in 
                     let exp2 = token (Queue.pop queue) in 
                    IF (cond, exp1, exp2)
          | "\""  -> let exp = LITERAL (STRING (Queue.pop queue)) in 
                     let _   = Queue.pop queue in exp
          | "["   -> LITERAL (tokenList (Queue.pop queue))
          | "("   -> let exp = token (Queue.pop queue) in 
                      (match exp with
                        | (VAR x) -> let args = tokenApplyArgs (Queue.pop queue) in 
                                     APPLY (VAR x, args) 
                        |  _      -> exp)
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
(* let eval_exp exp rho = 
    let rec eval = function 
        | (LITERAL v) -> v 
        | (VAR x) -> lookup x rho
        | (IF (e1, e2, e3)) -> 
            let bool = eval e1 in 
                match bool with 
                    | (BOOLV v) -> if v then eval e2 else eval e3
                    | _ -> raise Ill_Typed 
        | (APPLY (f, args)) -> 
            let closure = eval f in 
                match closure with 
                    | (CLOSURE (LAMBDA (names, body), copy_rho)) -> 
                        let values = List.map (fun a -> eval a) args in 
                        let rho' = List.append (zip names values) copy_rho in 
                        eval_exp body rho'
                    | _ -> raise Ill_Typed
        | (LAMBDA (names, body)) -> 
            let rho_names = List.map fst rho in 
            let exists = List.exists (fun a -> List.mem a rho_names) names in 
            if exists then raise Shadowing else (CLOSURE (LAMBDA (names, body), rho))
        | (LET (defs, body)) -> 
            let final_rho = List.foldr (fun rho' d -> snd (eval_def d rho')) rho defs in 
            eval_exp body final_rho
    in eval exp  *)
(* 
   def -> (string * value) list -> (value * rho)
*)
(* and eval_def def rho = 
        match def with 
        |  *)
(* 
    interpret_lines runs indefintely, 
   accepting input from stdin and parsing it 
*)
let rec interpret_lines () = 
    let _ = print_string "> " in 
    let tokens = (parse (read_line ())) in 
    let () = Queue.iter (fun a -> print_endline a) tokens in 
    let def = tokenize tokens in 
    let () = print_endline (def_to_string def) in 
    interpret_lines ()

let () = interpret_lines ()

    