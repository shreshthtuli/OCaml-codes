(* COL226 - Assignment 2. Shreshth Tuli - 2016CS10680 *)

type exp = Const of int | Abs of exp | Neg of exp | Var of string | Add of exp * exp 
| Sub of exp * exp | Mul of exp * exp | Div of exp * exp | Mod of exp * exp 
| Exponent of exp * exp | T | F | Not of exp | And of exp * exp | Or of exp * exp 
| Implies of exp * exp | Eq of exp * exp | Gt of exp * exp | Lt of exp * exp
| Gte of exp * exp | Lte of exp * exp | Tuple of exp list * int | Proj of int * exp;;

type answer = Const_ of int | T_ | F_ | Tuple_ of answer list * int;;

let value x = match x with	
	(** [val value : answer -> int = <fun>]  *)
	Const_ n -> n;;

exception Error;;

let rec eval rho x = match x with
	(** [val eval : (string -> answer) -> exp -> answer = <fun>]  *)
    Const n -> Const_ n
  | Abs e -> if (value (eval rho e)) >= 0 then Const_ (value (eval rho e)) else Const_ (-1 * value (eval rho e))
  | T -> T_
  | F -> F_
  | Neg e -> if (eval rho e) = T_ then F_ else T_
  | Var x -> rho x
  | Add(e1, e2) -> Const_ (value (eval rho e1) + value (eval rho e2))
  | Sub(e1, e2) -> Const_ (value (eval rho e1) - value (eval rho e2))
  | Mul(e1, e2) -> Const_ (value (eval rho e1) * value (eval rho e2))
  | Div(e1, e2) -> Const_ (value (eval rho e1) / value (eval rho e2))
  | Mod(e1, e2) -> Const_ (value (eval rho e1) mod value (eval rho e2))
  | Exponent(e1, e2) -> let rec pow a = function
  							| 0 -> 1
  							| 1 -> a
  							| n -> let b = pow a (n/2) in b * b * (if n mod 2 = 0 then 1 else a) in
  				   Const_ (pow (value (eval rho e1)) (value (eval rho e2)))
  | Not(e) -> if (eval rho e) = T_ then F_ else F_
  | And(e1, e2) -> let a = eval rho e1 in let b = eval rho e2 in if a = T_ then if b = T_ then T_ else F_ else F_
  | Or(e1, e2) -> let a = eval rho e1 in let b = eval rho e2 in if a = F_ then if b = T_ then T_ else F_ else T_
  | Implies(e1, e2) -> let a = eval rho e1 in let b = eval rho e2 in if a = T_ then if b = F_ then F_ else T_ else T_
  | Eq(e1, e2) -> if (value (eval rho e1)) = (value (eval rho e2)) then T_ else F_
  | Gt(e1, e2) -> if (value (eval rho e1)) > (value (eval rho e2)) then T_ else F_
  | Lt(e1, e2) -> if (value (eval rho e1)) < (value (eval rho e2)) then T_ else F_
  | Gte(e1, e2) -> if (value (eval rho e1)) >= (value (eval rho e2)) then T_ else F_
  | Lte(e1, e2) -> if (value (eval rho e1)) <= (value (eval rho e2)) then T_ else F_
  | Proj(i, Tuple(l, n)) -> let rec trav i l = match (i, l) with
  								(1, x::xs) -> x
  							  | (i, x::xs) -> trav (i-1) xs 
  							  | _ -> raise Error in
  					eval rho (trav i l)
  | Tuple(l, n) -> let rec map l = match l with
  								[] -> []
  							  | x::xs -> [(eval rho x)]@(map xs) in
  					Tuple_((map l), n)
  | _ -> raise Error;;

type opcode = CONST of int | ABS | NEG | LOOKUP of string | ADD | SUB | MUL | DIV | MOD | EXPONENT 
| TOp | FOp | NOT | AND | OR | IMPLIES | EQ | GT | LT | GTE | LTE | TUPLE of opcode list list * int 
| PROJ of int;; 

let rec compile x = match x with
	(** [val compile : exp -> opcode list = <fun>]  *)
	Abs e -> (compile e)@[ABS] 
  |	Const n -> [CONST n]
  | T -> [TOp]
  | F -> [FOp]
  | Neg e -> (compile e)@[NEG]
  | Var x -> [LOOKUP x]
  | Add(e1, e2) -> (compile e1)@(compile e2)@[ADD]
  | Sub(e1, e2) -> (compile e1)@(compile e2)@[SUB]
  | Mul(e1, e2) -> (compile e1)@(compile e2)@[MUL]
  | Div(e1, e2) -> (compile e1)@(compile e2)@[DIV]
  | Mod(e1, e2) -> (compile e1)@(compile e2)@[MOD]
  | Exponent(e1, e2) -> (compile e1)@(compile e2)@[EXPONENT]
  | Not e -> (compile e)@[NOT]
  | And(e1, e2) -> (compile e1)@(compile e2)@[AND]
  | Or(e1, e2) -> (compile e1)@(compile e2)@[OR]
  | Implies(e1, e2) -> (compile e1)@(compile e2)@[IMPLIES]
  | Eq(e1, e2) -> (compile e1)@(compile e2)@[EQ]
  | Gt(e1, e2) -> (compile e1)@(compile e2)@[GT]
  | Lt(e1, e2) -> (compile e1)@(compile e2)@[LT]
  | Gte(e1, e2) -> (compile e1)@(compile e2)@[GTE]
  | Lte(e1, e2) -> (compile e1)@(compile e2)@[LTE]
  | Proj(i, Tuple(l, n)) -> let rec map f l = match l with
  								[] -> []
  							  | x::xs -> [(f x)]@(map f xs) in
  							[TUPLE((map compile l), n); PROJ i]
  | Tuple(l, n) -> let rec map f l = match l with
  								[] -> []
  							  | x::xs -> [(f x)]@(map f xs) in
  							[TUPLE((map compile l), n)]
  | _ -> raise Error;;                

let rec execute s rho c = match (s, c) with
	(** [val execute : answer list -> (string -> answer) -> opcode list -> answer = <fun>]  *)
    (s::s', []) -> s
  | (s, (CONST n)::c') -> execute ((Const_ n)::s) rho c'
  | (s, TOp::c') -> execute (T_::s) rho c'
  | (s, FOp::c') -> execute (F_::s) rho c'
  | (n::s, ABS::c') -> if value(n) >= 0 then execute (n::s) rho c' else execute ((Const_ (-1 * value(n)))::s) rho c' 
  | (n::s', NEG::c') -> execute (Const_ (-1 * value(n))::s') rho c'
  | (s, LOOKUP x::c') -> execute (rho x::s) rho c'
  | (n1::n2::s, ADD::c') -> execute (Const_ (value n2 + value n1)::s) rho c'
  | (n1::n2::s, SUB::c') -> execute (Const_ (value n2 - value n1)::s) rho c'
  | (n1::n2::s, MUL::c') -> execute (Const_ (value n2 * value n1)::s) rho c'
  | (n1::n2::s, DIV::c') -> execute (Const_ (value n2 / value n1)::s) rho c'
  | (n1::n2::s, MOD::c') -> execute (Const_ (value n2 mod value n1)::s) rho c'
  | (n1::n2::s, EXPONENT::c') -> let rec pow a = function
                            | 0 -> 1
                            | 1 -> a
                            | n -> let b = pow a (n/2) in b * b * (if n mod 2 = 0 then 1 else a) in
                            execute (Const_ (pow (value n1) (value n2))::s) rho c'
  | (n1::s, NOT::c') -> let invb x = match x with T_ -> F_ | F_ -> T_ | _ -> raise Error in
                            execute ((invb n1)::s) rho c'
  | (n1::n2::s, AND::c') -> let andb x y = match (x, y) with
                            (T_,T_) -> T_ | _ -> F_ in
                            execute ((andb n2 n1)::s) rho c'
  | (n1::n2::s, OR::c') -> let orb x y = match (x,y) with
                            (F_,F_) -> F_ | _ -> T_ in
                            execute ((orb n2 n1)::s) rho c'
  | (n1::n2::s, IMPLIES::c') -> let impb x y = match (x,y) with
                            (T_,F_) -> F_ | _ -> T_ in
                            execute ((impb n2 n1)::s) rho c'
  | (n1::n2::s, EQ::c') -> if (value n2) = (value n1) then execute (T_::s) rho c' else execute (F_::s) rho c'
  | (n1::n2::s, GT::c') -> if (value n2) > (value n1) then execute (T_::s) rho c' else execute (F_::s) rho c'
  | (n1::n2::s, LT::c') -> if (value n2) < (value n1) then execute (T_::s) rho c' else execute (F_::s) rho c'
  | (n1::n2::s, GTE::c') -> if (value n2) >= (value n1) then execute (T_::s) rho c' else execute (F_::s) rho c'
  | (n1::n2::s, LTE::c') -> if (value n2) <= (value n1) then execute (T_::s) rho c' else execute (F_::s) rho c'
  | (s, TUPLE(l, n)::(PROJ i)::c') -> let rec trav i l = match (i, l) with
                    		  (1, x::xs) -> x
                  			| (i, x::xs) -> trav (i-1) xs 
                  			| _ -> raise Error in
                            execute s rho ((trav i l)@c')
  | (s, TUPLE(l, n)::c') -> let rec map_exec l = match l with
  								[] -> []
  							  | x::xs -> [(execute [] rho x)]@(map_exec xs) in
  					execute (Tuple_((map_exec l), n)::s) rho c'
  | _ -> raise Error;;


let rho x = match x with
	(** [val rho : string -> answer = <fun>]  *)
    "x" -> Const_ 2
  | "y" -> Const_ 3
  | _ -> Const_ 0;;

(********* Examples: *********)

let exp1 = Add(Const 1, Const 2);;
(* val exp1 : exp = Add (Const 1, Const 2) *)
compile exp1;;
(* opcode list = [CONST 1; CONST 2; ADD] *)
execute [] rho (compile exp1);;
(* answer = Const_ 3 *)
eval rho exp1;;
(* answer = Const_ 3 *)

let exp2 = Proj(1, Tuple([Not T; F], 2));;
(* val exp2 : exp = Proj (1, Tuple ([Not T; F], 2)) *)
compile exp2;;
(* opcode list = [TUPLE ([[TOp; NOT]; [FOp]], 2); PROJ 1] *)
execute [] rho (compile exp2);;
(* answer = F_ *)
eval rho exp2;;
(* answer = F_ *)

let exp3 = And(Eq(Proj(1, Tuple([Abs(Const (-3)); Const 4],2)), Const 4) , T);;
(* val exp3 : exp = And (Eq (Proj (1, Tuple ([Abs (Const (-3)); Const 4], 2)), Const 4), T) *)
compile exp3;;
(* opcode list = [TUPLE ([[CONST (-3); ABS]; [CONST 4]], 2); PROJ 1; CONST 4; EQ; TOp; AND] *)
execute [] rho (compile exp3);;
(* answer = F_ *)
eval rho exp3;;
(* answer = F_ *)

let exp4 = Proj(1, Tuple([Add(Var "x", Var "y");Sub(Var "x", Var "y")], 2));;
(* val exp4 : exp = Proj (1, Tuple ([Add (Var "x", Var "y"); Sub (Var "x", Var "y")], 2)) *)
compile exp4;;
(* opcode list = [TUPLE ([[LOOKUP "x"; LOOKUP "y"; ADD]; [LOOKUP "x"; LOOKUP "y"; SUB]], 2); PROJ 1] *)
execute [] rho (compile exp4);;
(* answer = Const_ 5 *)
eval rho exp4;;
(* answer = Const_ 5 *)

let exp5 = Tuple([And(T, F); Implies(T, F); Or(T, F)], 3);;
(* val exp5 : exp = Tuple ([And (T, F); Implies (T, F); Or (T, F)], 3) *)
compile exp5;;
(* opcode list = [TUPLE ([[TOp; FOp; AND]; [TOp; FOp; IMPLIES]; [TOp; FOp; OR]], 3)] *)
execute [] rho (compile exp5);;
(* answer = Tuple_ ([F_; T_; T_], 3) *)
eval rho exp5;;
(* answer = Tuple_ ([F_; T_; T_], 3) *)

let exp6 = Tuple([Add(Var "x", Var "y"); Sub(Var "x", Var "y"); Mul(Var "x", Var "y"); Div(Var "x", Var "y")], 4);;
(* val exp6 : exp = Tuple ([Add (Var "x", Var "y"); Sub (Var "x", Var "y"); Mul (Var "x", Var "y");
     Div (Var "x", Var "y")], 4) *)
compile exp6;;
(* opcode list = [TUPLE ([[LOOKUP "x"; LOOKUP "y"; ADD]; [LOOKUP "x"; LOOKUP "y"; SUB];
[LOOKUP "x"; LOOKUP "y"; MUL]; [LOOKUP "x"; LOOKUP "y"; DIV]], 4)] *)
execute [] rho (compile exp6);;
(* answer = Tuple_ ([Const_ 5; Const_ (-1); Const_ 6; Const_ 0], 4) *)
eval rho exp6;;
(* answer = Tuple_ ([Const_ 5; Const_ (-1); Const_ 6; Const_ 0], 4) *)


(* Checking two 3 digit numbers are equal or not *)
let rho1 x = match x with
	(** [val rho : string -> answer = <fun>]  *)
    "x1" -> Const_ 1
  | "x2" -> Const_ 2
  | "x3" -> Const_ 3
  | "y1" -> Const_ 1
  | "y2" -> Const_ 2
  | "y3" -> Const_ 3
  | _ -> Const_ 0;;

let exp7 = And(And(Eq(Var "x1", Var "y1"), Eq(Var "x2", Var "y2")), Eq(Var "x3", Var "y3"));;
(* val exp5 : exp = And (And (Eq (Var "x1", Var "y1"), Eq (Var "x2", Var "y2")), Eq (Var "x3", Var "x3")) *)
compile exp7;;
(* opcode list = [LOOKUP "x1"; LOOKUP "y1"; EQ; LOOKUP "x2"; LOOKUP "y2"; EQ; AND; LOOKUP "x3"; LOOKUP "x3"; EQ; AND] *)
execute [] rho1 (compile exp7);;
(* answer = T_ *)
eval rho exp7;;
(* answer = T_ *)


(* END OF CODE *)