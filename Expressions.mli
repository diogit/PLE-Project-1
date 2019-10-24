(* Expressions module interface *)
(* LAP (AMD 2017) *)

(*
01234567890123456789012345678901234567890123456789012345678901234567890123456789
   80 columns
*)

type exp =
      Add of exp*exp
    | Sub of exp*exp
    | Mult of exp*exp
    | Div of exp*exp
    | Const of float
    | V
    | Poly of float list
;;

val pcount : float list -> int * int
val size : exp -> int
val eval : float -> exp -> float
val deriv : exp -> exp
val alike : float -> int -> exp -> exp -> bool
val newton : float -> exp -> float
val simpl : exp -> exp
val graph : int -> int -> float -> exp -> string list