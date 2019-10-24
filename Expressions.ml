(* Expressions module body *)

(*
Aluno 1: 45679 Diogo Rafael Rebocho Silverio
Aluno 2: 48500 Joao Bernardo Coimbra Marques

Comment:

Todos as funcoes pedidas no enunciado estao implementadas. Qualquer funcao que
achamos que merece uma explicacao tem um comentario antes do seu codigo.

*)


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

let epsilon = 0.000001;;
let step = 0.1;;

let feq f1 f2 =
    abs_float(f1 -. f2) <= epsilon
;;

let pcount l =
    let count (nz, z) f = if feq f 0. then (nz, z + 1) else (nz + 1, 0) in
        List.fold_left count (0, 0) l
;;

let rec size e =
    match e with
    | V -> 1
    | Const _ -> 1
    | Add (e1, e2) -> 1 + size e1 + size e2
    | Sub (e1, e2) -> 1 + size e1 + size e2
    | Div (e1, e2) -> 1 + size e1 + size e2
    | Mult (e1, e2) -> 1 + size e1 + size e2
    | Poly l -> let (nz, z) = pcount l in 1 + nz + z
;;

let rec eval v e =
    match e with
    | V -> v
    | Const f -> f
    | Add (e1, e2) -> eval v e1 +. eval v e2
    | Sub (e1, e2) -> eval v e1 -. eval v e2
    | Div (e1, e2) -> eval v e1 /. eval v e2
    | Mult (e1, e2) -> eval v e1 *. eval v e2
    | Poly [] -> 0.0
    | Poly (c :: cs) -> c +. v *. eval v (Poly cs)
;;

let rec deriv e =
    match e with
    | V -> Const 1.0
    | Const _ -> Const 0.0
    | Add (e1, e2) -> Add (deriv e1, deriv e2)
    | Sub (e1, e2) -> Sub (deriv e1, deriv e2)
    | Mult (e1, e2) -> Add (Mult (deriv e1, e2), Mult (e1, deriv e2))
    | Div (e1, e2) ->
        Div (
            Sub (Mult (deriv e1, e2), Mult (e1, deriv e2)),
            Mult (e2, e2)
        )
    | Poly [] -> Const 0.0
    | Poly (_ :: xs) -> Add (Poly xs, Mult (V, deriv (Poly xs)))
;;

(* A funcao alike esta definida apenas para n >= 0, nao faz sentido comparar
   duas expressoes num numero negativo de pontos. Para n = 0 duas expressoes
   sao sempre iguais, pois foram comparadas em zero pontos. *)
let rec alike a n e1 e2 =
    if n = 0 then
        true
    else
        feq (eval a e1) (eval a e2) && alike (a +. step) (n - 1) e1 e2
;;

let rec newton s e =
    if feq (eval s e) 0.0 then
        s
    else
        newton (s -. eval s (Div (e, deriv e))) e
;;

(* Remove os zeros nao-significativos de um polinomio. *)
let rec simplPoly l =
    match l with
    | [] -> []
    | 0.0 :: xs ->
        let p = simplPoly xs in
            if p = [] then p else 0.0 :: p
    | x :: xs -> x :: simplPoly xs
;;

(* Multiplica todos os coeficientes de um polinomio por -1.0. *)
let rec minusPoly l =
    match l with
    | [] -> []
    | x :: xs -> (x *. (-1.0)) :: minusPoly xs
;;

(* Aplica um predicado aos coeficientes de um polinomio e uma constante. *)
let rec applyConstPoly p const l =
    match l with
    | [] -> []
    | x :: xs -> (p x const) :: applyConstPoly p const xs
;;

(* Realiza a soma de dois polinomios e devolve o resultado. *)
let rec sumPolyPoly l1 l2 =
    match l1, l2 with
    | [], l -> l
    | l, [] -> l
    | x :: xs, y :: ys -> (x +. y) :: sumPolyPoly xs ys
;;

(* Realiza a multiplicacao de dois polinomios e devolve o resultado. Cada
   coeficiente do polinomio de l1 'e multiplicado por todos os coeficientes de
   l2. A cada coeficiente de l1, um coeficiente de l2 passa para a potencia
   seguinte (o mesmo que acrescentar um zero a cabeca). Os polinomios
   resultantes destas multiplicacoes vao sendo somados. *)
let rec multPolyPoly l1 l2 =
    match l1 with
    | [] -> []
    | x :: xs ->
        sumPolyPoly (applyConstPoly ( *. ) x l2) (multPolyPoly xs (0.0 :: l2))
;;

let rec simpl e =
    match e with
    | V -> e
    | Const _ -> e
    | Poly [] -> Const 0.0
    | Poly [x] -> Const x
    | Poly l -> Poly (simplPoly l)

    | Add (Const 0.0, e) -> simpl e
    | Add (e, Const 0.0) -> simpl e
    | Add (Const a, Const b) -> Const (a +. b)
    | Add (Const a, V) -> Poly [a; 1.0]
    | Add (V, Const a) -> Poly [a; 1.0]
    | Add (Const a, Poly []) -> Const a
    | Add (Poly [], Const a) -> Const a
    | Add (Const a, Poly (x :: xs)) -> Poly ((x +. a) :: xs)
    | Add (Poly (x :: xs), Const a) -> Poly ((x +. a) :: xs)
    | Add (V, V) -> Poly [0.0; 2.0]
    | Add (V, Poly []) -> Poly [0.0; 1.0]
    | Add (Poly [], V) -> Poly [0.0; 1.0]
    | Add (V, Poly [a]) -> Poly [a; 1.0]
    | Add (Poly [a], V) -> Poly [a; 1.0]
    | Add (V, Poly (x :: y :: xs)) -> Poly (x :: (y +. 1.0) :: xs)
    | Add (Poly (x :: y :: xs), V) -> Poly (x :: (y +. 1.0) :: xs)
    | Add (Poly l1, Poly l2) -> Poly (sumPolyPoly l1 l2)
    | Add (e1, e2) ->
        if alreadySimpl e1 && alreadySimpl e2 then
            e
        else
            simpl (Add (simpl e1, simpl e2))

    | Sub (e, Const 0.0) -> simpl e
    | Sub (Const a, Const b) -> Const (a -. b)
    | Sub (Const a, V) -> Poly [a; -1.0]
    | Sub (V, Const a) -> Poly [(a *. -1.0); 1.0]
    | Sub (Const a, Poly []) -> Const a
    | Sub (Poly [], Const a) -> Const (a *. -1.0)
    | Sub (Const a, Poly (x :: xs)) -> Poly (minusPoly ((x -. a) :: xs))
    | Sub (Poly (x :: xs), Const a) -> Poly ((x -. a) :: xs)
    | Sub (V, V) -> Const 0.0
    | Sub (V, Poly []) -> Poly [0.0; 1.0]
    | Sub (Poly [], V) -> Poly [0.0; -1.0]
    | Sub (V, Poly [a]) -> Poly [(a *. -1.0); 1.0]
    | Sub (Poly [a], V) -> Poly [a; -1.0]
    | Sub (V, Poly (x :: y :: xs)) -> Poly (minusPoly (x :: (y -. 1.0) :: xs))
    | Sub (Poly (x :: y :: xs), V) -> Poly (x :: (y -. 1.0) :: xs)
    | Sub (Poly l1, Poly l2) -> Poly (sumPolyPoly l1 (minusPoly l2))
    | Sub (e1, e2) ->
        if alreadySimpl e1 && alreadySimpl e2 then
            e
        else
            simpl (Sub (simpl e1, simpl e2))

    | Mult (Const 1.0, e) -> simpl e
    | Mult (e, Const 1.0) -> simpl e
    | Mult (Const a, Const b) -> Const (a *. b)
    | Mult (Const a, V) -> Poly [0.0; a]
    | Mult (V, Const a) -> Poly [0.0; a]
    | Mult (V, V) -> e
    | Mult (Const a, Poly l) -> Poly (applyConstPoly ( *. ) a l)
    | Mult (Poly l, Const a) -> Poly (applyConstPoly ( *. ) a l)
    | Mult (V, Poly l) -> Poly (0.0 :: l)
    | Mult (Poly l, V) -> Poly (0.0 :: l)
    | Mult (Poly l1, Poly l2) -> Poly (multPolyPoly l1 l2)
    | Mult (e1, e2) ->
        if alreadySimpl e1 && alreadySimpl e2 then
            e
        else
            simpl (Mult (simpl e1, simpl e2))

    | Div (e, Const 1.0) -> simpl e
    | Div (_, Const 0.0) -> e
    | Div (Const 0.0, Const b) -> Const 0.0
    | Div (Const a, Const b) -> Const (a /. b)
    | Div (Poly [], Const a) -> Const 0.0
    | Div (Const 0.0, Poly [x]) -> if feq x 0.0 then e else Const 0.0
    | Div (Poly l, Const a) -> Poly (applyConstPoly (/.) a l)
    | Div (_, V) -> e
    | Div (_, Poly _) -> e
    | Div (e1, e2) ->
        if alreadySimpl e1 && alreadySimpl e2 then
            e
        else
            simpl (Div (simpl e1, simpl e2))

(* Devolve true se a expressao 'e' ja estiver na forma simplificada, false
   caso contrario. Mutuamente recursiva com a funcao 'simpl'. *)
and alreadySimpl e =
    e = simpl e
;;

let rec findMinMaxY nx s e =
    let y = eval s e in
        if nx = 1 then
            (y, y)
        else
            let (minimum, maximum) = findMinMaxY (nx - 1) (s +. step) e in
                (min y minimum, max y maximum)
;;

let near value marking stepValue =
    let lower = marking -. stepValue /. 2.0 in
        let upper = marking +. stepValue /. 2.0 in
            lower < value && value <= upper
;;

(* A funcao 'near' 'e usada para encontrar o sitio correcto dos eixos, o eixo
   das abcissas 'e quando o y esta perto do 0.0, analogamente o eixo das
   ordenadas 'e quando o x esta perto do 0.0.

   Seria possivel usar apenas a funcao 'feq' para encontrar o eixo das ordenadas
   se o valor de 's' dado a funcao 'graph' tivesse no maximo uma casa decimal.
   Assumimos que esta situacao nao 'e garantida e como tal 'e mais seguro usar
   a funcao 'near' para localizar o eixo. *)
let rec plotLine nx x y stepY e =
    if nx = 0 then
        ""
    else
        let c = if near (eval x e) y stepY then "*"
                else if near y 0.0 stepY then "-"
                else if near x 0.0 step then "|"
                else " "
        in
            c ^ plotLine (nx - 1) (x +. step) y stepY e
;;

let rec plot nx ny x y stepY e =
    if ny = 0 then
        []
    else
        (plotLine nx x y stepY e) :: plot nx (ny - 1) x (y -. stepY) stepY e
;;

let graph nx ny s e =
    let (minimum, maximum) = findMinMaxY nx s e in
        let stepY = (maximum -. minimum) /. float_of_int (ny - 1) in
            plot nx ny s maximum stepY e
;;
