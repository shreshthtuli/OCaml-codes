(* COL226 - Assignment 4. Shreshth Tuli - 2016CS10680 *)

(* Call by value : Closure =>v Answer
	exp, variable
	value closure : table * variable * opcode list
	answer : ... | Value Closure
	table : (variable * answer) list,
*)

type variable = Var of string;;

type exp = Const of int | Abs of exp | Neg of exp | V of variable | Add of exp * exp 
| Sub of exp * exp | Mul of exp * exp | Div of exp * exp | Mod of exp * exp 
| Exponent of exp * exp | T | F | Not of exp | And of exp * exp | Or of exp * exp 
| Implies of exp * exp | Eq of exp * exp | Gt of exp * exp | Lt of exp * exp
| Gte of exp * exp | Lte of exp * exp | Tuple of exp list * int | Proj of int * exp
| IfTE of exp * exp * exp | Lambda of variable * exp | Apply of exp * exp
| Letin of exp * exp | Def of variable * exp | Seq of exp * exp | Par of exp * exp;;

type opcode = CONST of int | ABS | NEG | LOOKUP of variable | ADD | SUB | MUL | DIV | MOD | EXPONENT 
| TOp | FOp | NOT | AND | OR | IMPLIES | EQ | GT | LT | GTE | LTE | TUPLE of opcode list list * int 
| PROJ of int | COND of opcode list * opcode list | CLOS of variable * opcode list | RET | APPLY
| BIND of variable | UNBIND | SEQ | ENDSEQ | PAR | APPLYDEF;;


type answer = Const_ of int | T_ | F_ | Tuple_ of answer list * int 
| ValClos of table * variable * opcode list | DefClos of (variable * answer) list
and table = (variable * answer) list;;

exception Error;;

let value x = match x with	
	(** [val value : answer -  q > int = <fun>]  *)
	Const_ n -> n;;
 
let rec compile x = match x with
	(** [val compile : exp -> opcode list = <fun>]  *)
	  Abs e -> (compile e)@[ABS] 
  |	Const n -> [CONST n]
  | T -> [TOp]
  | F -> [FOp]
  | Neg e -> (compile e)@[NEG]
  | V x -> [LOOKUP x]
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
  | IfTE(e0, e1, e2) -> (compile e0)@[COND(compile e1, compile e2)]
  | Lambda(x, e1) -> [CLOS(x, (compile e1)@[RET])]
  | Apply(e1, e2) -> (compile e1)@(compile e2)@[APPLY]
  | Def(x, e) -> (compile e)@[BIND x]
  | Seq(d1, d2) -> (compile d1)@[SEQ]@(compile d2)@[ENDSEQ]
  | Par(d1, d2) -> (compile d1)@(compile d2)@[PAR]
  | Letin(d, e) -> (compile d)@[APPLYDEF]@(compile e)@[UNBIND]
  | _ -> raise Error;;        

let rec execute s e c d = match (s,e,c,d) with
    ((Const_ n)::s, e, ABS::c', d) -> if(n >= 0) then execute ((Const_ n)::s) e c' d 
									 else execute ((Const_ (-1*value(Const_ n)))::s) e c' d
  | (s, e, (CONST n)::c', d) -> execute ((Const_ n)::s) e c' d
  | (s, e, TOp::c', d) -> execute (T_::s) e c' d
  | (s, e, FOp::c', d) -> execute (F_::s) e c' d
  | (n::s, e, NEG::c', d) -> execute ((Const_ ((-1)*value(n)))::s) e c' d
  | (s, e, (LOOKUP x)::c', d) -> let rec find a s = match s with
  									[] -> raise Error
  								  |	(x1, x2)::xs -> if (x1=a) then x2 else find a xs in
  								execute ((find x e)::s) e c' d
  | (a::b::s, e, ADD::c, d) -> execute ((Const_ (value(b) + value(a)))::s) e c d
  | (a::b::s, e, SUB::c, d) -> execute ((Const_ (value(b) - value(a)))::s) e c d
  | (a::b::s, e, MUL::c, d) -> execute ((Const_ (value(b) * value(a)))::s) e c d
  | (a::b::s, e, DIV::c, d) -> execute ((Const_ (value(b) / value(a)))::s) e c d
  | (a::b::s, e, MOD::c, d) -> execute ((Const_ (value(b) mod value(a)))::s) e c d
  | (a::b::s, e, EXPONENT::c, d) -> let rec pow a = function
                            | 0 -> 1
                            | 1 -> a
                            | n -> let b = pow a (n/2) in b * b * (if n mod 2 = 0 then 1 else a) in
                             execute (Const_ (pow (value a) (value b))::s) e c d
  | (a::s, e, NOT::c, d) -> let invb x = match x with T_ -> F_ | F_ -> T_ | _ -> raise Error in
  							execute ((invb a)::s) e c d
  | (a::b::s, e, AND::c, d) -> let andb x y = match (x, y) with (T_,T_) -> T_ | _ -> F_ in
  							execute ((andb a b)::s) e c d
  | (a::b::s, e, OR::c, d) -> let orb x y = match (x,y) with (F_,F_) -> F_ | _ -> T_ in
  							execute ((orb a b)::s) e c d
  | (a::b::s, e, IMPLIES::c, d) -> let impb x y = match (x,y) with (T_,F_) -> F_ | _ -> T_ in
  							execute ((impb b a)::s) e c d
  | (a::b::s, e, EQ::c, d) -> if (value a) = (value b) then execute (T_::s) e c d
  							else execute (F_::s) e c d
  | (a::b::s, e, GT::c, d) -> if (value b) > (value a) then execute (T_::s) e c d
  							else execute (F_::s) e c d
  | (a::b::s, e, LT::c, d) -> if (value b) < (value a) then execute (T_::s) e c d
  							else execute (F_::s) e c d
  | (a::b::s, e, GTE::c, d) -> if (value b) >= (value a) then execute (T_::s) e c d
  							else execute (F_::s) e c d
  | (a::b::s, e, LTE::c, d) -> if (value b) <= (value a) then execute (T_::s) e c d
  							else execute (F_::s) e c d
  | (s, e, TUPLE(l, n)::(PROJ i)::c', d) -> let rec trav i l = match (i, l) with
                    		  (1, x::xs) -> x
                  			| (i, x::xs) -> trav (i-1) xs 
                  			| _ -> raise Error in
                            execute s e ((trav i l)@c') d
  | (s, e, TUPLE(l, n)::c', d) -> let rec map_exec l = match l with
  								[] -> []
  							  | x::xs -> [(execute [] e x d)]@(map_exec xs) in
  							execute (Tuple_((map_exec l), n)::s) e c' d		
  | (a::s, e, COND(c1, c2)::c, d) -> if (a = T_) then execute s e (c1@c) d
  							else if (a = F_) then execute s e (c2@c) d
  							else raise Error
  | (s, e, CLOS(x,c1)::c', d) -> execute (ValClos(e, x, c1)::s) e c' d
  | (a::ValClos(e', x, c')::s, e, APPLY::c, d) -> execute s ((x, a)::e') c' ((s, e, c)::d)
  | (s', e', RET::c', (s, e, c)::d) -> execute s' e c d
  | (a::s', e, (BIND x)::c', d) -> execute (DefClos([(x,a)])::s') e c' d
  | (DefClos([(x, a)])::s, e, SEQ::c, d) -> execute (DefClos([(x, a)])::s) ([(x,a)]@e) c ((s, e, c)::d)
  | (DefClos([(x, a)])::DefClos([(y, b)])::s', e', ENDSEQ::c', (s, e, c)::d') -> execute (DefClos([(x, a); (y, b)])::s') e c' d'
  | (DefClos([(x, a)])::DefClos([(y, b)])::s, e, PAR::c, d) -> execute (DefClos([(x, a); (y, b)])::s) e c d
  | (DefClos(l)::s, e, APPLYDEF::c, d) -> execute s (l@e) c ((s, e, c)::d)
  | (s', e', UNBIND::c', (s, e, c)::d') -> execute s' e c' d'
  | (s::s', e, [], d) -> s;;

let exec e = execute [] [] (compile e) [];;

(* END OF CODE *)

(* TESTCASES *)

(* Calculator *)

let e = Sub(Const 1, Const 2);;
compile e;;
exec e;;

let e = Proj(1, Tuple([Not T; F], 2));;
compile e;;
exec e;;

let e = And(Eq(Proj(1, Tuple([Abs(Const (-3)); Const 4],2)), Const 4) , T);;
compile e;;
exec e;;

let e = Proj(1, Tuple([Add(V (Var "x"), V (Var "y"));Sub(V (Var "x"), V (Var "y"))], 2));;
compile e;;
execute [] [(Var "x", Const_ 2); (Var "y", Const_ 3)] (compile e) [];;

let e = Tuple([And(T, F); Implies(T, F); Or(T, F)], 3);;
compile e;;
exec e;;

let e = Tuple([Add(V (Var "x"), V (Var "y")); 
  Sub(V (Var "x"), V (Var "y")); 
  Mul(V (Var "x"), V (Var "y")); 
  Div(V (Var "x"), V (Var "y"))], 4);;
compile e;;
execute [] [(Var "x", Const_ 2); (Var "y", Const_ 3)] (compile e) [];;

let e = Implies(Not(Implies(Or(T, F), And(T, F))),Implies(And(T, F), Or(T, F)));;
compile e;;
exec e;;

let e = Abs(Sub(Const 3, Const 6));;
compile e;;
exec e;;

let e = Implies(Eq(Const 7, Const 7), F);;
compile e;;
exec e;;

let e = Not(And(V(Var "x"), T));;
compile e;;
execute [] [(Var "x", T_)] (compile e) [];;

(* Functions *)

let e = Apply(Lambda(Var "x", Add(V(Var "x"), Const 3)) , Const 4);;
compile e;;
exec e;;

let e = Apply(Lambda(Var "x", 
  (Apply(Lambda(Var "y", Add(V(Var "y"), V(Var "x"))) , Const 3)))
  , Const 4);;
compile e;;
exec e;;

(* If_Then_Else *)

let e = IfTE(Eq(Const 4, Add(Const 2, Const 1)), 
  Apply(Lambda(Var "x", Add(V(Var "x"), Const 3)) , Const 4), 
  Apply(Lambda(Var "x", Add(V(Var "x"), Const 5)) , Const 6)
  );;
compile e;;
exec e;;

(* Local Definitions *)

let e = Add(V(Var "x"), Const 5);;
compile e;;
execute [] [(Var "x", Const_ 4)] (compile e) [];;

let e = Letin(Def(Var "x", Const 5), Add(V(Var "x"), Const 5));;
compile e;;
exec e;;

let e = Letin(Def(Var "x", Const 6), Add(V(Var "x"), Const 5));;
compile e;;
execute [] [(Var "x", Const_ 4)] (compile e) [];;

let e = Letin(Par(Def(Var "x", Const 4), Def(Var "y", Add(V(Var "x"), Const 1))), 
  Tuple([V(Var "x"); V(Var "y")], 2));;
compile e;;
execute [] [(Var "x", Const_ 2)] (compile e) [];;

let e = Letin(Seq(Def(Var "x", Const 4), Def(Var "y", Add(V(Var "x"), Const 1))), 
  Tuple([V(Var "x"); V(Var "y")], 2));;
compile e;;
execute [] [(Var "x", Const_ 2)] (compile e) [];;

