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

