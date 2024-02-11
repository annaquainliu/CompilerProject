
(* PARSING INPUT *)
let pop_first_char input = String.sub input 1 ((String.length input) - 1)

let list_to_string f xs = 
    let rec stringify = function 
      |  []         -> ""
      |  [x]        -> (f x)
      |  (x::xs)    -> (f x) ^ "\n" ^ stringify xs
    in stringify xs

(* 
   parse takes in string input and returns a list of tokens,
   which is any keyword or string deliminated by a space
*)
let rec parse input = 
    let rec extract input str = match input with 
        | "" -> []
        | _  -> match input.[0] with 
                | ' ' | ';' | '(' | ')' | '[' | ']' | ',' | '"' -> 
                        str::(String.make 1 input.[0])::(extract (pop_first_char input) "") 
                | c  -> if String.length input == 1
                        then [(str ^ String.make 1 c)] (* to handle case where last char is not a delimeter *)
                        else extract (pop_first_char input) (str ^ String.make 1 c) 
    in List.rev (List.filter (fun (a) -> a <> " " && a <> "") (extract input ""))

(* 
    interpret_lines runs indefintely, 
   accepting input from stdin and parsing it 
*)
let rec interpret_lines () = 
    let _ = print_string "> " in 
    let tokens = (parse (read_line ())) in 
    let () = print_endline (list_to_string (fun (x) -> x) tokens) in 
    interpret_lines ()

(* TOKENIZING! *)

(*

let rec tokenizeLine = function 
    | [] -> ()
    | (x::xs) -> 
        match x with
        |  "if"  ->  (* if statement *)
        |  "let" -> (* 3 cases: if next word is 'let' : expression, 'rec' : letrec, anything else : definition*)
        |  "fn"  -> (* lambda *)
        |   "("  ->  (* call tokenizeLine again, if the token is a var, create an apply token, else return token *)
        |   "["  ->  (* list *)
        |   "\""  -> (* string *)
        |   x    -> (* check if is a number, else must be a variable *)

*)

let () = interpret_lines ()

    