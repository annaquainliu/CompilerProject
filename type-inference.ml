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
let unitty = TYCON "unit"
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
  in TYVAR (string_of_int !tyvarCt)

let ftvs tau = 
  let rec getftvs curSet t = match t with
    | TYVAR(a) -> insert a curSet
    | TYCON(_) -> curSet
    | CONAPP(ty, tys) -> List.fold_left getftvs (getftvs curSet ty) tys
  in getftvs [] tau

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
  | curC::cs -> curC ^ (conjoin cs)

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
  
let rec typeof exp g = 
  let rec infer ex = match ex with
  | LITERAL(value) -> inferLiteral value
  | VAR(s) -> (freshInstance (findTyscheme s g), TRIVIAL)
  | IF(e1, e2, e3) ->
      let (t1, c1) = infer e1 in
      let (t2, c2) = infer e2 in
      let (t3, c3) = infer e3 in
        (t2, c1 ^ c2 ^ c3 ^ (t2 ^^ t3) ^ (t1 ^^ boolty))
  | LAMBDA(formals, b) -> 
      let alphas = List.map (fun form -> (form, freshtyvar())) formals in
      let newG = List.fold_left (fun acc (x, c) -> bindtyscheme (x, FORALL ([], c), acc)) g alphas in
      let (endty, endc) = typeof b newG in (funtype ((List.map snd alphas), endty), endc)

  | LET(ds, e) -> 
    let (defsC, finalGamma) = List.fold_left (fun (curC, curG) d -> 
        let (_, nextC, nextG, _) = typeOfDef d curG in
        (nextC, nextG)) (TRIVIAL, g) ds in
        let (tau, expC) = typeof e finalGamma in (tau, expC ^ defsC)      
  | APPLY(f, es) -> match (typesof (f::es) g) with
      | ([], _) -> raise (Cringe "invalid")
      | (fty::etys, con) -> let crisp = freshtyvar() in
        (crisp, con ^ fty ^^ (funtype (etys, crisp)))

  and inferLiteral v = match v with
  | STRING(_) -> (strty, TRIVIAL)
  | NUMBER(_) -> (intty, TRIVIAL)
  | BOOLV(_) -> (boolty, TRIVIAL)
  | NIL -> (freshInstance (FORALL (["a"], listty (TYVAR "a"))), TRIVIAL)
  | PAIR(e, v) -> 
    let (t1, c1) = infer e in
    let (t2, c2) = infer (LITERAL v) in
      (t2, c1 ^ c2 ^ (listty t1 ^^ t2))
  | UNIT -> (unitty, TRIVIAL)
  | _ -> (boolty, TRIVIAL)

  and typesof es g = List.fold_left (fun (ts, c) e ->
         let (curty, curc) = typeof e g in
         (curty::ts, c ^ curc)) ([], TRIVIAL) es

  in infer exp


(* (tyscheme, con, type env, output string) *)
and typeOfDef d g = 
  let rec inferDef def = match def with 
    | LETDEF(n, e) -> 
      let (tau, c) = typeof e g in
      let theta = solve c in
      let crisps = inter (domain theta) (ftvsGamma g) in
      let finalC = c ^ conjoin(List.map (fun x -> TYVAR x ^^ varsubst theta x) crisps) in
      let ligma = generalize (ftvsGamma g) ((tysubst theta) tau) in
      let newGamma = bindtyscheme(n, ligma, g) in
      (ligma, finalC, newGamma, "")
      
    (* possible bug due to using newGamma underneath its definition? type rules say to use gamma *)
    | LETREC(n, e) -> 
      let _ = confirmLambda e in
      let alpha = freshtyvar() in
      let newGamma = bindtyscheme(n, FORALL([], alpha), g) in
      let (tau, c) = typeof e newGamma in
      let c2 = c ^ (alpha ^^ tau) in
      let theta = solve c2 in
      let crisps = inter (domain theta) (ftvsGamma newGamma) in
      let finalC = c2 ^ conjoin(List.map (fun x -> TYVAR x ^^ varsubst theta x) crisps) in
      let ligma = generalize (ftvsGamma newGamma) ((tysubst theta) tau) in
      let finalGamma = bindtyscheme(n, ligma, g) in
      (ligma, finalC, finalGamma, "")

    | EXP(e) -> typeOfDef (LETDEF ("it", e)) g
  in inferDef d

let rec printType t = match t with 
  | TYVAR(a) -> print_string a
  | TYCON(c) -> print_string c
  | CONAPP(TYCON tc, [ty]) -> (*lists currently the only CONAPP application*)
    let () = print_string tc in let () = print_string " " in printType ty
  | _ -> print_string "Margaret Thatcher"  

let printExpType e =
  let (tau, _) = typeof e ([], []) in let () = printType tau in print_endline ""

let rec printConstraint c = match c with
  | TRIVIAL -> print_string "TRIVIAL"
  | EQ(t1, t2) -> 
      let () = print_string "(" in
      let () = printType t1 in
      let () = print_string " ~ " in
      let () = printType t2 in print_string ")"
  | CONJ(c1, c2) ->
      let () = print_string "(" in
      let () = printConstraint c1 in
      let () = print_string " ^ " in
      let () = printConstraint c2 in print_string ")"

(*returns string forms of type and constraint*)
let debugExpType e = 
  let (tau, c) = typeof e ([], []) in
  let () = printType tau in let () = print_string ", " in let () = printConstraint c in print_endline ""




(*type inference sanity checks*)

(* let () = let () = print_string "type1 is... " in printExpType (LITERAL (NUMBER 666))
let () = let () = print_string "type2 is... " 
         in printExpType (IF (LITERAL(BOOLV true), LITERAL (NUMBER 420), LITERAL (NUMBER 666)))
let () = let () = print_string "type3 is... " 
         in printExpType (IF (LITERAL(BOOLV true), LITERAL (STRING "xd"), LITERAL (STRING "XD")))
let () = let () = print_string "type4 (should fail) is... " 
        in printExpType (IF (LITERAL(NUMBER 0), LITERAL (STRING "xd"), LITERAL (STRING "XD"))) *)


(*type inference debugging*)

(* let () = let () = print_string "debug test1: " 
        in debugExpType (IF (LITERAL(NUMBER 0), LITERAL (STRING "xd"), LITERAL (STRING "XD")))
let wtf = 
  let (ty, c) = typeof (IF (LITERAL(NUMBER 0), LITERAL (STRING "xd"), LITERAL (STRING "XD"))) ([], []) in
  solve c
let wtf2 = let (ty, c) = typeof(NIL) in solve c *)


(*type inference unit testing*)

let unitTestCt = ref 0

let checkValidTypeInf e = 
 let () = unitTestCt := !unitTestCt + 1 in
 let (ty, c) = typeof e ([], []) in
 try let _ = solve c in () with Cringe _ -> 
  let () = print_string("failed test ") in print_endline(string_of_int !unitTestCt)

let checkInvalidTypeInf e = 
  let () = unitTestCt := !unitTestCt + 1 in
  let (ty, c) = typeof e ([], []) in
  try 
    let _ = solve c in 
      let () = print_string "failed test " in 
      print_endline(string_of_int !unitTestCt) with Cringe _ -> ()

let () = checkValidTypeInf (LITERAL(NUMBER 666))
let () = checkInvalidTypeInf (IF (LITERAL(NUMBER 0), LITERAL (STRING "xd"), LITERAL (STRING "XD")))
let () = checkValidTypeInf (IF (LITERAL(BOOLV true), LITERAL (NUMBER 420), LITERAL (NUMBER 666)))
let () = checkValidTypeInf (LITERAL NIL)
let () = checkValidTypeInf (LITERAL(PAIR(LITERAL(STRING "anthrax"), NIL)))

let () = debugExpType (LITERAL (PAIR (LITERAL(STRING "anthrax"), PAIR(LITERAL(NUMBER 500), NIL))))
let cringe = let (ty, c) = 
    typeof(LITERAL (PAIR (LITERAL(STRING "anthrax"), PAIR(LITERAL(NUMBER 500), NIL)))) ([], []) in solve c
