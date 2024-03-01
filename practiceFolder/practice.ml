let rec binary n = 
    if n = 0 
    then 0 
    else (n mod 2) + (10 * binary (n / 2))

let () = assert ((binary 2) = 10)
let () = assert ((binary 3) = 11)

(* 
  Takes in a tuple of lists and returns a list of tuples
*)
exception Invalid_input;;

let rec zip = function 
    | ([], [])       -> []
    | (x::xs, y::ys) -> (x, y)::zip (xs, ys)
    | _              ->  raise Invalid_input

let () = assert ((zip ([1; 2; 3; 4], ["a"; "b"; "c"; "d"])) = [(1, "a"); (2, "b"); (3, "c"); (4, "d")])

(* 
  Takes in a list of tuples and returns a tuple of lists
*)
let unzip = function
    | []          -> [], []
    | ys          -> 
        let rec map f ys = match ys with 
            | []     -> []
            | (x::xs)  -> (f x)::(map f xs)
        in map (fun (a, b) -> a) ys, map (fun (a, b) -> b) ys

let () = assert (unzip ["a", "b"; "d", "e"; "f", "g"] = (["a"; "d"; "f"], ["b"; "e"; "g"]))
let () = assert (unzip [] = ([],[]))

let rec foldl f acc xs = match xs with 
        | [] -> acc
        | (x::xs) -> foldl f (f x acc) xs

let () = assert ((foldl (fun a b -> a::b) [] [1;2;3]) = [3;2;1])

let rec foldr f acc xs = match xs with 
        | [] -> acc
        | (x::xs) -> f x (foldr f acc xs)

let () = assert ((foldr (fun a b -> a::b) [] [1;2;3]) = [1;2;3])

(* 
  Turns any list into a string, accepting 
  f which is a function that turns each element into a string,
  and xs which is the list.
*)
let listToString f xs = 
    let rec stringify = function 
      |  []         -> ""
      |  [x]        -> (f x)
      |  (x::xs)    -> (f x) ^ ", " ^ stringify xs
    in "[" ^ stringify xs ^ "]"

let () = print_endline (listToString string_of_int [1;2;3;4])
let () = print_endline (listToString (fun (a, b) -> "(" ^ a ^", "^ string_of_int b ^ ")") ["a", 3;"asda", 45435;"taylor", 1989;"swift", 233])

type excrement = POO | PEE
type toilet = TOILET of excrement * excrement

type greet = BYE of toilet | GREET of greet * greet 

(* let test = function 
      | (BYE (TOILET (POO, PEE))) -> 3
      |  (BYE (TOILET (PEE, PEE))) -> 3
      |  (BYE (TOILET (POO, POO))) -> 3
      |  (BYE (TOILET (PEE, POO))) -> 3
      |  (GREET (BYE (TOILET (x, y)), a)) -> 3
      |  (GREET (GREET (x , y), b)) -> 3 *)

(* (PATTERN ("BYE", [PATTERN ("TOILET", [PATTERN ("POO", []); PATTERN ("PEE", [])])]));
(PATTERN ("BYE", [PATTERN ("TOILET", [PATTERN ("PEE", []); PATTERN ("POO", [])])]));
(PATTERN ("BYE", [PATTERN ("TOILET", [PATTERN ("PEE", []); PATTERN ("PEE", [])])]));
(PATTERN ("BYE", [PATTERN ("TOILET", [PATTERN ("POO", []); PATTERN ("POO", [])])]));
(PATTERN ("GREET", [PATTERN ("BYE", [PATTERN ("TOILET", [GENERIC; GENERIC])]); GENERIC]));
(PATTERN ("GREET", [PATTERN ("GREET", [GENERIC; GENERIC]); GENERIC])); *)

let test = function 
    | x::xs::x::xs::y -> 