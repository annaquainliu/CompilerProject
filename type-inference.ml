(*NOT FINISHED YET*)
(*TODO: [write support functions for generalize, finish remaining patterns, unit test, clean up code]*)
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


exception Cringe of string
let typeInferenceBug = Cringe("The problem with pissing on my grave is eventually you'll run out of piss. -Margaret Thatcher")
let usefulError x = Cringe x (*for debugging*)

type ty = TYCON of string | TYVAR of string | CONAPP of ty * ty list
let intty = TYCON "int"
let boolty = TYCON "bool"
let strty = TYCON "string"
let listty t = CONAPP(TYCON "list", [t])
let funtype (args, result) =
  CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args); result])

type tyscheme = FORALL of string list * ty

type tyenv = (string * tyscheme) list * string list 

type con = TRIVIAL | EQ of ty * ty | CONJ of con * con

type subst = (ty * ty) list

let (^^) t1 t2 = EQ (t1, t2)
let (^) c1 c2 = CONJ (c1, c2)
let (-->) a t = match t with
  | TYVAR (a') -> if a = a' then [] else [(a, TYVAR a')]
  | tau        -> [(a, tau)]

let domain t = List.map (fun (x, _) -> x) t
let union xs ys = List.fold_left
      (fun acc x -> if (List.exists (fun y -> y = x) ys) then acc else x::acc) ys xs
let inter xs ys = List.fold_left
      (fun acc x -> if (List.exists (fun y -> y = x) ys) then x::acc else acc) [] xs
let diff xs ys = List.fold_left
      (fun acc x -> if (List.exists (fun y -> y = x) ys) then acc else x::acc) [] xs

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
  |  CONJ (c1, c2) -> subst c1 ^ subst c2
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
  in TYVAR (String.cat String.empty (string_of_int !tyvarCt))

let ftvs tau = 
  let rec getftvs curSet t = match t with
    | TYVAR(a) -> insert a curSet
    | TYCON(_) -> curSet
    | CONAPP(ty, tys) -> List.fold_left getftvs (getftvs curSet ty) tys
  in getftvs [] tau

(* let findTyscheme s gamma = 
  let rec locate g = match g with
  | []               -> raise (Cringe "var inference led to missing type scheme")
  | (s', scheme)::xs -> if s' = s then scheme else locate xs
  in locate gamma *)

let bindtyscheme (x, ts, (g, f)) = match ts with 
  | FORALL(bound, t) -> ((x, ts)::g, union f (diff (ftvs t) bound))


let rec solve c = match c with
  | TRIVIAL      -> []
  | CONJ(c1, c2) -> 
      let t1 = solve c1 in
      let t2 = solve c2 in
      compose (t2, t1)
  | EQ(t1, t2) -> match (t1, t2) with
    | (TYVAR a, TYVAR _)  -> a --> t2
    | (TYVAR a, TYCON _)   -> a --> t2
    | (TYVAR a, CONAPP _)  -> if member a (ftvs t2) then raise typeInferenceBug else a --> t2
    | (TYCON c1, TYCON c2) -> if c1 = c2 then [] else raise typeInferenceBug
    | (TYCON _, CONAPP _)  -> raise typeInferenceBug
    | _                    -> solve (t2 ^^ t1)


let rec typeof exp g = 
  let rec infer ex = match ex with
  | LITERAL(value) -> inferLiteral value
  | VAR(s) -> (strty, TRIVIAL)
  | IF(e1, e2, e3) ->
      let (t1, c1) = infer e1 in
      let (t2, c2) = infer e2 in
      let (t3, c3) = infer e3 in
        (t2, c1 ^ c2 ^ c3)
  | LAMBDA(formals, b) -> 
      let alphas = List.map (fun form -> (form, freshtyvar())) formals in
      let newG = List.fold_left (fun acc (x, c) -> bindtyscheme (x, FORALL ([], c), acc)) g alphas in
      let (endty, endc) = typeof b newG in (funtype ((List.map snd alphas), endty), endc)
  | APPLY(f, es) -> match (typesof (f::es) g) with
      | ([], _) -> raise (Cringe "invalid")
      | (fty::etys, con) -> let crisp = freshtyvar() in
        (crisp, con ^ fty ^^ (funtype (etys, crisp)))

  | _ -> (boolty, TRIVIAL)

  and inferLiteral v = match v with
  | STRING(_) -> (strty, TRIVIAL)
  | NUMBER(_) -> (intty, TRIVIAL)
  | BOOLV(_) -> (boolty, TRIVIAL)
  | PAIR(e, v) -> 
    let (t1, c1) = infer e in
    let (t2, c2) = infer (LITERAL v) in
      (t2, c1 ^ c2 ^ (listty t1 ^^ t2))
  | _ -> (boolty, TRIVIAL)

  and typesof es g = List.fold_left (fun (ts, c) e ->
         let (curty, curc) = typeof e g in
         (curty::ts, c ^ curc)) ([], TRIVIAL) es



  in infer exp
