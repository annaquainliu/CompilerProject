let pop_first_char input = String.sub input 1 ((String.length input) - 1)

let list_to_string f xs = 
    let rec stringify = function 
      |  []         -> ""
      |  [x]        -> (f x)
      |  (x::xs)    -> (f x) ^ "\n" ^ stringify xs
    in stringify xs

let rec parse input = 
    let rec extract input str = match input with 
        | "" -> []
        | _  -> match input.[0] with 
                | ' ' | ';' | '(' | ')' | '[' | ']' | ',' | '"' -> 
                        str::(String.make 1 input.[0])::(extract (pop_first_char input) "") 
                | c  -> if String.length input == 1
                        then (str ^ String.make 1 c)::extract (pop_first_char input) ""
                        else extract (pop_first_char input) (str ^ String.make 1 c) 
    in 
    let tokens = List.filter (fun (a) -> a <> " " && a <> "") (extract input "") in
    if List.length tokens == 0 && String.length input <> 0 then 
        [input]
    else tokens 

let rec interpret_lines () = 
    let _ = print_string "> " in 
    let tokens = (parse (read_line ())) in 
    let () = print_endline (list_to_string (fun (x) -> x) tokens) in 
    interpret_lines ()

let () = interpret_lines ()

    