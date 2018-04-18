(* COL226 - Assignment 4. Shreshth Tuli - 2016CS10680 *)

(* Call by name : Closure =>n Answer
	exp, variable
	closure : table * exp,
	table : variable * closure,
*)

type variable = Var of string;;
type bool = T | F;;

type exp = Const of int | Abs of exp | Neg of exp | V of variable | Add of exp * exp 
| Sub of exp * exp | Mul of exp * exp | Div of exp * exp | Mod of exp * exp 
| Exponent of exp * exp | Bool of bool | Not of exp | And of exp * exp | Or of exp * exp 
| Implies of exp * exp | Eq of exp * exp | Gt of exp * exp | Lt of exp * exp
| Gte of exp * exp | Lte of exp * exp | Tuple of exp list * int | Proj of int * exp
| IfTE of exp * exp * exp | Lambda of variable * exp | Apply of exp * exp
| NIL | TUPLE of exp list * answer list * int| IF of exp * exp | Letin of variable * exp * exp
and table = (variable * closure) list 
and closure = Clos of table * exp
and answer = Const_ of int | T_ | F_ | Tuple_ of answer list * int | ValClos of table * exp
| DefClos of table * exp | NIL_ | Lambda_ of variable * answer | Apply_ of answer * answer
| Abs_ of answer | Neg_ of answer | Add_ of answer * answer | Sub_ of answer * answer 
| Mul_ of answer * answer | Div_ of answer * answer | Mod_ of answer * answer 
| Exponent_ of answer * answer | Not_ of answer | And_ of answer * answer 
| Or_ of answer * answer | Implies_ of answer * answer | Eq_ of answer * answer 
| Gt_ of answer * answer | Lt_ of answer * answer | Gte_ of answer * answer 
| Lte_ of answer * answer | Proj_ of int * answer
| IfTE_ of answer * answer * answer;;

exception Error;;

let value x = match x with	
	(** [val value : answer -> int = <fun>]  *)
	Const n -> n;;

let rec unpack x = match x with
	Clos(t, Const n) -> Const_ n
  | Clos(t, Bool T) -> T_
  | Clos(t, Bool F) -> F_
  | Clos(t, NIL) -> NIL_
  | Clos(t, V x) -> let rec find a s = match s with
  				[] -> raise Error
  			  |	(x1, x2)::xs -> if (x1=a) then x2 else find a xs in
  			unpack (find x t)
  | Clos(t, Add(e1, e2)) -> Add_ ((unpack (Clos(t, e1)),  (unpack (Clos(t, e2)))))
  | Clos(t, Sub(e1, e2)) -> Sub_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Mul(e1, e2)) -> Mul_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Div(e1, e2)) -> Div_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Mod(e1, e2)) -> Mod_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Exponent(e1, e2)) -> Exponent_((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, And(e1, e2)) -> And_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Or(e1, e2)) -> Or_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Implies(e1, e2)) -> Implies_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Eq(e1, e2)) -> Eq_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Gte(e1, e2)) -> Gte_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Lte(e1, e2)) -> Lte_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Gt(e1, e2)) -> Gt_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Lt(e1, e2)) -> Lt_ ((unpack (Clos(t, e1)),  unpack (Clos(t, e2))))
  | Clos(t, Tuple(e, n)) -> let rec map f l = match l with
  								[] -> []
  							  | x::xs -> (f (Clos(t, x)))::(map f xs) in 
  							Tuple_ ((map unpack e), n)
  | Clos(t, IfTE(e0, e1, e2)) -> IfTE_ ((unpack (Clos(t, e0))), (unpack (Clos(t, e1))),  unpack (Clos(t, e2)))
  | Clos(t, Lambda(x, e)) -> let rec rem a s s' = match s with
  				[] -> []
  			  | (x1, x2)::xs -> if (x1=a) then s'@xs else rem a xs ((x1, x2)::s') in
  			Lambda_ (x, (unpack (Clos(rem x t [], e))))
  | Clos(t, Apply(e1, e2)) -> Apply_(unpack (Clos(t, e1)), unpack (Clos(t, e2)));;

let rec execute c s = match (c, s) with  
    (Clos(t, Abs e), s) -> execute (Clos(t, e)) (Clos(t, Abs(NIL))::s)
  | (Clos(t, Const n), Clos(t1, Abs(NIL))::s) -> if (n >= 0) then execute (Clos(t1, Const n)) s
  						else execute (Clos(t1, Const ((-1)*n))) s

  | (Clos(t, Neg e), s) -> execute (Clos(t, e)) (Clos(t, Neg(NIL))::s)
  | (Clos(t, Const n), Clos(t1, Neg(NIL))::s) -> execute (Clos(t1, Const (-1*n))) s

  | (Clos(t, Add(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Add(NIL,e2))::s)
  | (Clos(t, Const n), Clos(t1, Add(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Add(Const n, NIL))::s)
  | (Clos(t, Const n2), Clos(t1, Add(Const n1, NIL))::s) -> execute (Clos(t1, Const (n1 + n2))) s

  | (Clos(t, Sub(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Sub(NIL, e2))::s)
  | (Clos(t, Const n), Clos(t1, Sub(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Sub(Const n, NIL))::s)
  | (Clos(t, Const n2), Clos(t1, Sub(Const n1, NIL))::s) -> execute (Clos(t1, Const (n1 - n2))) s

  | (Clos(t, Mul(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Mul(NIL, e2))::s)
  | (Clos(t, Const n), Clos(t1, Mul(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Mul(Const n, NIL))::s)
  | (Clos(t, Const n2), Clos(t1, Mul(Const n1, NIL))::s) -> execute (Clos(t1, Const (n1 * n2))) s

  | (Clos(t, Div(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Div(NIL, e2))::s)
  | (Clos(t, Const n), Clos(t1, Div(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Div(Const n, NIL))::s)
  | (Clos(t, Const n2), Clos(t1, Div(Const n1, NIL))::s) ->  execute (Clos(t1, Const (n1 / n2))) s

  | (Clos(t, Mod(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Mod(NIL, e2))::s)
  | (Clos(t, Const n), Clos(t1, Mod(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Mod(Const n, NIL))::s)
  | (Clos(t, Const n2), Clos(t1, Mod(Const n1, NIL))::s) ->  execute (Clos(t1, Const (n1 mod n2))) s

  | (Clos(t, Exponent(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Exponent(NIL, e2))::s)
  | (Clos(t, Const n), Clos(t1, Exponent(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Exponent(Const n, NIL))::s)
  | (Clos(t, Const n2), Clos(t1, Exponent(Const n1, NIL))::s) -> 
                          let rec pow a = function
                            | 0 -> 1
                            | 1 -> a
                            | n -> let b = pow a (n/2) in b * b * (if n mod 2 = 0 then 1 else a) in
  							            execute (Clos(t1, Const (pow n1 n2))) s

  | (Clos(t, Not e), s) -> execute (Clos(t, e)) (Clos(t, Not(NIL))::s)
  | (Clos(t, Bool T), Clos(t1, Not(NIL))::s) -> execute (Clos(t1, Bool F)) s
  | (Clos(t, Bool F), Clos(t1, Not(NIL))::s) -> execute (Clos(t1, Bool T)) s

  | (Clos(t, And(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, And(NIL, e2))::s)
  | (Clos(t, Bool b), Clos(t1, And(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, And(Bool b, NIL))::s)
  | (Clos(t, Bool b2), Clos(t1, And(Bool b1, NIL))::s) -> let andb x y = match (x, y) with (T,T) -> T | _ -> F in
  							execute (Clos(t1, Bool (andb b1 b2))) s

  | (Clos(t, Or(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Or(NIL, e2))::s)
  | (Clos(t, Bool b), Clos(t1, Or(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Or(Bool b, NIL))::s)
  | (Clos(t, Bool b2), Clos(t1, Or(Bool b1, NIL))::s) -> let orb x y = match (x,y) with (F,F) -> F | _ -> T in
  							execute (Clos(t1, Bool (orb b1 b2))) s

  | (Clos(t, Implies(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Implies(NIL, e2))::s)
  | (Clos(t, Bool b), Clos(t1, Implies(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Implies(Bool b, NIL))::s)
  | (Clos(t, Bool b2), Clos(t1, Implies(Bool b1, NIL))::s) -> let impb x y = match (x,y) with (T,F) -> F | _ -> T in
  							execute (Clos(t1, Bool (impb b1 b2))) s

  | (Clos(t, Eq(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Eq(NIL, e2))::s)
  | (Clos(t, Const n), Clos(t1, Eq(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Eq(Const n, NIL))::s)
  | (Clos(t, Const n2), Clos(t1, Eq(Const n1, NIL))::s) -> if n1 == n2 then execute (Clos(t1, Bool T)) s else execute (Clos(t1, Bool F)) s

  | (Clos(t, Gt(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Gt(NIL, e2))::s)
  | (Clos(t, Const n), Clos(t1, Gt(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Gt(Const n, NIL))::s)
  | (Clos(t, Const n2), Clos(t1, Gt(Const n1, NIL))::s) -> if n1 > n2 then execute (Clos(t1, Bool T)) s else execute (Clos(t1, Bool F)) s

  | (Clos(t, Lt(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Lt(NIL, e2))::s)
  | (Clos(t, Const n), Clos(t1, Lt(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Lt(Const n, NIL))::s)
  | (Clos(t, Const n2), Clos(t1, Lt(Const n1, NIL))::s) -> if n1 < n2 then execute (Clos(t1, Bool T)) s else execute (Clos(t1, Bool F)) s

  | (Clos(t, Gte(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Gt(NIL, e2))::s)
  | (Clos(t, Const n), Clos(t1, Gt(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Gte(Const n, NIL))::s)
  | (Clos(t, Const n2), Clos(t1, Gte(Const n1, NIL))::s) -> if n1 >= n2 then execute (Clos(t1, Bool T)) s else execute (Clos(t1, Bool F)) s

  | (Clos(t, Lte(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, Lte(NIL, e2))::s)
  | (Clos(t, Const n), Clos(t1, Lte(NIL, e2))::s) -> execute (Clos(t1, e2)) (Clos(t1, Lte(Const n, NIL))::s)
  | (Clos(t, Const n2), Clos(t1, Lte(Const n1, NIL))::s) -> if n1 <= n2 then execute (Clos(t1, Bool T)) s else execute (Clos(t1, Bool F)) s


  | (Clos(t, Tuple(e::es, n)), s) -> execute (Clos(t, e)) (Clos(t, TUPLE(es, [], n))::s)
  | (Clos(t, a), (Clos(t1, TUPLE(e::es, al, n)))::s) -> execute (Clos(t1, e)) (Clos(t1, TUPLE(es, al@[unpack(Clos(t, a))], n))::s)
  | (Clos(t, a), (Clos(t1, TUPLE([], al, n)))::s) -> Tuple_ (al@[unpack (Clos(t, a))], n)

  | (Clos(t, Proj (i, Tuple(explist, n))), s) -> let rec trav i l = match (i, l) with
  								(1, x::xs) -> x
  							  | (i, x::xs) -> trav (i-1) xs 
  							  | _ -> raise Error in
  							execute (Clos(t, (trav i explist))) s

  | (Clos(t, IfTE(e0, e1, e2)), s) -> execute (Clos(t, e0)) (Clos(t, IF(e1, e2))::s)
  | (Clos(t, Bool b), Clos(t1, IF(e1, e2))::s) -> if (b == T) then execute (Clos(t1, e1)) s else execute (Clos(t1, e2)) s

  |	(Clos(t, V x), s) -> let rec find a s = match s with
  							[] -> raise Error
  						  |	(x1, x2)::xs -> if (x1=a) then x2 else find a xs in
  						execute (find x t) s
  | (Clos(t, Letin(x, e1, e2)), s) -> execute (Clos(((x, Clos([],e1))::t), e2)) s       

  | (Clos(t, Lambda(x, e1')), cl::s) -> execute (Clos(((x,cl)::t), e1')) s
  | (Clos(t, Apply(e1, e2)), s) -> execute (Clos(t, e1)) (Clos(t, e2)::s)
  | (Clos(t, x), []) -> unpack (Clos(t, x));;


let exec e = execute (Clos([], e)) [];;

  (* END OF CODE *)

  (* TESTCASES *)

let e = Abs(Const(-1));;
exec e;;

let e = Sub(Const 1, Const 2);;
exec e;;

let e = Proj(1, Tuple([Not (Bool T); Bool F], 2));;
exec e;;

let e = And(Eq(Proj(1, Tuple([Abs(Const (-3)); Const 4],2)), Const 4) , T);;
exec e;;

let e = Proj(1, Tuple([Add(V (Var "x"), V (Var "y")); Sub(V (Var "x"), V (Var "y"))], 2));;
execute (Clos([(Var "x", Clos([], Const 2)); (Var "y", Clos([], Const 3))], e)) [];;

let e = Tuple([And(Bool T, Bool F); Implies(Bool T, Bool F); Or(Bool T, Bool F)], 3);;
exec e;;

let e = And(Eq(Proj(1, Tuple([Abs(Const (-3)); Const 4],2)), Const 4) , Bool T);;
exec e;;

let e = Tuple([Add(V (Var "x"), V (Var "y")); 
  Sub(V (Var "x"), V (Var "y")); 
  Mul(V (Var "x"), V (Var "y")); 
  Div(V (Var "x"), V (Var "y"))], 4);;
execute (Clos([(Var "x", Clos([], Const 2)); (Var "y", Clos([], Const 3))], e)) [];;

let e = Implies(Not(Implies(Or(Bool T, Bool F), And(Bool T, Bool F))),Implies(And(Bool T, Bool F), Or(Bool T, Bool F)));;
exec e;;

let e = Abs(Sub(Const 3, Const 6));;
exec e;;

let e = Implies(Eq(Const 7, Const 7), Bool F);;
exec e;;

let e = Not(And(V(Var "x"), Bool T));;
execute (Clos([(Var "x", Clos([], Bool T))], e)) [];;

(* Functions *)

let e = Apply(Lambda(Var "x", Add(V(Var "x"), Const 3)) , Const 4);;
exec e;;

let e = Apply(Lambda(Var "x", 
  (Apply(Lambda(Var "y", Add(V(Var "y"), V(Var "x"))) , Const 3)))
  , Const 4);;
exec e;;

(* If_Then_Else *)

let e = IfTE(Eq(Const 4, Add(Const 2, Const 1)), 
  Apply(Lambda(Var "x", Add(V(Var "x"), Const 3)) , Const 4), 
  Apply(Lambda(Var "x", Add(V(Var "x"), Const 5)) , Const 6)
  );;
exec e;;

(* Miscellaneous *)

let e = Lambda(Var "x", NIL);;
exec e;;

let e = Add(Const 4, IfTE(Eq(Const 7, Const 7), Const 1, Bool T));;
exec e;;


(* Other test cases *)


execute (Clos([(Var "z", Clos([], Const 2))], V( Var "z"))) [];;

execute (Clos([],Add(Add(Const(2),Const(3)),Add(Const(2),Const(3))))) [];;

execute (Clos([(Var("z"),Clos([],Const(3)))],Add(Const(2),V(Var("z"))))) [];;

execute (Clos([],Apply(Lambda(Var("x"),Add(V(Var("x")),Const(1))),Const(2)))) [];;

execute (Clos([],Apply(Lambda(Var("x"),Mul(V(Var("x")),Add(V(Var("x")),Const(1)))),Const(2)))) [];;

execute (Clos([],Apply(Lambda(Var("x"),Apply(Lambda(Var("d"),Mul(V(Var("d")),Const(2))),Const(2))),Const(2)))) [];;

execute (Clos([],IfTE(Gt(Const(8),Const(2)),Apply(Lambda(Var("x"),Div(V(Var("x")),Const(2))),Const(2)),Apply(Lambda(Var("x"),Mul(V(Var("x")),Add(V(Var("x")),Const(1)))),Const(2))))) [];;

execute (Clos([],IfTE(Gt(Const(1),Const(2)),Apply(Lambda(Var("x"),Div(V(Var("x")),Const(2))),Const(2)),Apply(Lambda(Var("x"),Mul(V(Var("x")),Add(V(Var("x")),Const(1)))),Const(2))))) [];;

execute (Clos([],Letin(Var("a"),Const(2),Add(V(Var("a")),Const(20))))) [];;

(*krivine(ACL([],LetinEnd(Seq[Assgn(Var("a"),Num(2))],Plus(Var("a"),Num(20)))),[]);;*)

execute (Clos([],Proj(2, Tuple([Const(1);Const(2);Const(3)],3)))) [];;

(*execute (Clos([],Apply(Lambda(Var("x"),LetinEnd(Para[Assgn(Var("a"),Num(2))],Plus(Var("a"),Var("x")))),Num(2))),[]);;*)