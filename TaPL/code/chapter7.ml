open Printf;;

type term = 
    TmVar of int
    | TmAbs of term
    | TmApp of term * term;;

let rec term_to_string (t) = 
    match t with
    TmVar a -> "TmVar"
    | TmAbs t' -> "TmAbs " ^ term_to_string t'
    | TmApp (t1, t2) -> "TmApp " ^ term_to_string t1 ^ term_to_string t2;;
let t = TmApp (TmVar(3), TmApp (TmVar (2), TmVar (6)));;
printf "%s\n" (term_to_string t);;
let fix = fun f -> (fun x -> f (fun y z -> x x y z)) (fun x -> f (fun y z -> x x y z));;
let gcd = fun g a b -> if b = 0 then a else g b (a mod b);;
printf "%d\n" ((fix gcd) 10 15);;