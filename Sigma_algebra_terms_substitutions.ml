(* COL226 - Assignment 3. Shreshth Tuli - 2016CS10680 *)

(* Assuming signature is in list form *)

type symbol = Sym of string;;
type variable = Var of string;;

type term = V of variable | Node of symbol * (term list);;

type signature = (symbol * int) list;; (* Pair list of (symbol, arity) *)

(***** Exmaples of signatures and terms *****)

let signat : signature = [(Sym "+", 2); (Sym "-", 2); (Sym "0", 0); (Sym "1", 0)];;
let signat2 : signature = [(Sym "+", 2); (Sym "+", 1); (Sym "1", -1)];;

let term = Node(Sym "+", [V (Var "x"); Node(Sym "1", [])]);; (* x + 1 *)
let term2 = Node(Sym "+", [V (Var "x"); Node(Sym "+", [Node(Sym "1", [])])]);; (* invalid *)
let term3 = Node(Sym "+", [Node(Sym "+", [V (Var "x"); V (Var "y")]); Node(Sym "-", [V (Var "x"); V (Var "y")])]);;
(* (x + y) + (x - y) *)



(***** Function check_sig *****)

let check_sig (x:signature) = 
  (** [val check_sig : signature -> bool = <fun>]  *)
	let rec check_sig_list x l = match x with
		    [] -> true
  	  |	(x,y)::xs -> if ((List.mem x l) || (y<0)) then false
				 	else check_sig_list xs (x::l) in
	check_sig_list x [];;

check_sig signat;;
(* bool = true *)
check_sig signat2;;
(* bool = false *)



(***** Some helpful functions *****)

exception Error;;

let rec get_arity (x:symbol) (signat:signature) = match signat with
	  [] -> raise Error
  | (s, a)::signat' -> if (x = s) then a else (get_arity x signat');;

let rec map f l = match l with
	  [] -> []
  | x::xs -> (f x)::(map f xs);;

let rec foldl f e l = match l with
	  [] -> e
  | x::xs -> foldl f (f(x,e)) xs;;



(***** Function wfterm *****)

let rec wfterm (x:term) (signat:signature) = 
  (** [val wfterm : term -> signature -> bool = <fun>]  *)
  match x with
	  V var -> true
  | Node(sym, sub_terms) -> 
  			let wfterm1 x = wfterm x signat in
  			let andB (x,y) = if x&&y then true else false in
			if (get_arity sym signat) = (List.length sub_terms) then (foldl andB true (map wfterm1 sub_terms)) else false;;

wfterm term signat;;
(* bool = true *)
wfterm term2 signat;;
(* bool = false *)
wfterm term3 signat;;
(* bool = true *)



(***** Function Height *****)

let rec ht t = 
  (** [val ht : term -> int = <fun>]  *)
  match t with
	  V x -> 0
  | Node(sym, []) -> 0 
  | Node(sym, l) -> let max (x,y) = if x > y then x else y in
  			1 + (foldl max 0 (map ht l));;

ht term;;
(* int =  1 *)
ht term3;;
(* int =  2 *)



(***** Function Size *****)

let rec size t = 
  (** [val size : term -> int = <fun>]  *)
  match t with
	  V x -> 1
  | Node(sym, []) -> 1
  | Node(sym, l) -> let sum (x, y) = x + y in 
  			1 + foldl sum 0 (map size l);;

size term;;
(* int = 3 *)
size term3;;
(* int = 7 *)



(***** Function vars *****)

let rec vars t = 
  (** [val vars : term -> variable list = <fun>]  *)
  match t with
	  V x -> [x]
  | Node(sym, []) -> []
  | Node(sym, l) -> let rec union (x,y) = match x with
                        [] -> y
                      | x::xs -> if (List.mem x y) then union (xs, y) else x::(union (xs, y)) in
  			foldl union [] (map vars l);; 

vars term;;
(* variable list = [Var "x"] *)
vars term3;;
(* variable list = [Var "y"; Var "x"] *)



(***** Substitution *****)

type substitution = (variable * term) list;;

let s : substitution = [(Var "x", Node(Sym "+", [V (Var "x"); Node(Sym "1", [])])); (Var "y", V (Var "x"))];;
(* {x -> x+1, y -> x} *)
let s2 : substitution = [(Var "x", V (Var "y"))];;
(* {x -> y} *)
let s3 : substitution = [(Var "y", V (Var "z")); (Var "x", V (Var "z"))];;
(* {y -> z, x -> z} *)



(***** Unique homomorphic extension of substitution : subst *****)

let rec subst (s:substitution) (x:term) = 
  (** [val subst : substitution -> term -> term = <fun>]  *)
  match x with
	  V v -> let rec find v s = match s with
              [] -> V v
            | (a,b)::xs -> if (v = a) then b else find v xs in
           find v s
  | Node(sym, l) -> if (l = []) then Node(sym, l)
  		   else let subst1 x = subst s x in
  		   let l' = map subst1 l in 
  		   Node(sym, l');;

term;;
(* term = Node (Sym "+", [V (Var "x"); Node (Sym "1", [])]) *)
(*** x + 1 ***)
subst s term;;
(* term = Node (Sym "+", [Node (Sym "+", [V (Var "x"); Node (Sym "1", [])]); Node (Sym "1", [])]) *)
(*** (x + 1) + 1 ***)
subst s2 term;;
(* term = Node (Sym "+", [V (Var "y"); Node (Sym "1", [])]) *)
(*** y + 1 ***)
subst s3 term;;
(* term = Node (Sym "+", [V (Var "z"); Node (Sym "1", [])]) *)
(*** z + 1 ***)

term3;;
(* term = Node (Sym "+", [Node (Sym "+", [V (Var "x"); V (Var "y")]); 
 Node (Sym "-", [V (Var "x"); V (Var "y")])]) *)
(*** (x + y) + (x - y) ***)
subst s term3;;
(* term = Node (Sym "+", [Node (Sym "+", [Node (Sym "+", [V (Var "x"); Node (Sym "1", [])]); V (Var "x")]);
  Node (Sym "-", [Node (Sym "+", [V (Var "x"); Node (Sym "1", [])]); V (Var "x")])]) *)
(*** ((x + 1) + x) + ((x + 1) - x) ***)
subst s2 term3;;
(* term = Node (Sym "+", [Node (Sym "+", [V (Var "y"); V (Var "y")]);
 Node (Sym "-", [V (Var "y"); V (Var "y")])]) *)
(*** (y + y) + (y - y) ***)
subst s3 term3;;
(* term = Node (Sym "+", [Node (Sym "+", [V (Var "z"); V (Var "z")]); 
Node (Sym "-", [V (Var "z"); V (Var "z")])]) *)
(*** (z + z) + (z - z) ***)



(***** Composition of substitutions *****)

let compose (s1:substitution) (s2:substitution) : substitution = 
  (** [val compose : substitution -> substitution -> substitution = <fun>]  *)
  let s1' (a,b) = (a, subst s2 b) in
  let s1s2 = map s1' s1 in 
  let rec sigma2 l = match l with
     [] -> []
   | (a,b)::xs -> let rec member a l = match l with
                    [] -> false
                  | (v,t)::xs -> if (a = v) then true else member a xs in
  if member a s1s2 then sigma2 xs else [(a,b)]@(sigma2 xs) in
  let rec rm_id l = match l with
     [] -> []
   | (a,b)::xs -> if (V a = b) then (rm_id xs) else (a,b)::(rm_id xs) in
  rm_id (s1s2 @ (sigma2 s2));;

compose s s2;; (* This could have (Var "y", V (Var "y")) if identity maps weren't removed *)
(* substitution = [(Var "x", Node (Sym "+", [V (Var "y"); Node (Sym "1", [])]))] *)
compose s s3;;
(* substitution = [(Var "x", Node (Sym "+", [V (Var "z"); Node (Sym "1", [])]));
 (Var "y", V (Var "z"))] *)
compose s2 s3;;
(* substitution = [(Var "x", V (Var "z")); (Var "y", V (Var "z"))] *)



(***** Most General Unifier *****)

exception NOT_UNIFIABLE;;

let rec mgu t u : substitution = 
  (** [val mgu : term -> term -> substitution = <fun>]  *) 
  match (t, u) with
	  (V x, V y) -> if (x = y) then [] else [(x, V y)]
  | (V x, Node(sym, [])) -> [(x, Node(sym, []))]
  | (Node(sym, []), V x) -> [(x, Node(sym, []))]
  | (V x, Node(sym, l)) -> if (List.mem x (vars (Node(sym, l)))) then raise NOT_UNIFIABLE 
                           else [(x, Node(sym, l))]
  | (Node(sym, l), V x) -> if (List.mem x (vars (Node(sym, l)))) then raise NOT_UNIFIABLE
                           else [(x, Node(sym, l))]
  | (Node(sym, []), Node(sym', [])) -> if (sym = sym') then [] else raise NOT_UNIFIABLE
  | (Node(sym, t'), Node(sym', u')) -> if (List.length t' = List.length u' && sym = sym') then
  				let rec fold sigma t u = match (t,u) with
                  ([],[]) -> sigma
                | (t1::tr, u1::ur) -> fold (compose sigma (mgu (subst sigma t1) (subst sigma u1))) tr ur
                | _ -> raise Error in
          fold [] t' u'
          else raise NOT_UNIFIABLE;; 

let term4 = V (Var "z");;
let term5 = V (Var "y");;
let term6 = Node(Sym "+", [Node(Sym "-", [Node(Sym "1", []); V (Var "x")]); Node(Sym "+", [V (Var "x"); Node(Sym "0", [])])]);;
let term7 = Node(Sym "+", [Node(Sym "-", [Node(Sym "1", []); Node(Sym "0", [])]); Node(Sym "+", [V (Var "z"); V (Var "x")])]);;
let term8 = Node(Sym "+", [Node(Sym "-", [V (Var "x"); Node(Sym "0", [])]); V (Var "y")]);;
let term9 = Node(Sym "+", [V (Var "z"); Node(Sym "-", [Node(Sym "1", []); V (Var "x")])]);;

wfterm term6 signat;;
(* bool = true *)
wfterm term7 signat;;
(* bool = true *)
wfterm term8 signat;;
(* bool = true *)
wfterm term9 signat;;
(* bool = true *)

mgu term term3;;
(* Exception: NOT_UNIFIABLE *)
mgu term term4;;
(* Exception: NOT_UNIFIABLE. *)
mgu term term5;;
(* substitution = [(Var "y", Node (Sym "+", [V (Var "x"); Node (Sym "1", [])]))] *)
mgu term3 term4;;
(* substitution = [(Var "z", Node (Sym "+", [Node (Sym "+", [V (Var "x"); V (Var "y")]);
    Node (Sym "-", [V (Var "x"); V (Var "y")])]))] *)
mgu term3 term5;;
(* Exception: NOT_UNIFIABLE. *)
mgu term4 term5;;
(* substitution = [(Var "z", V (Var "y"))] *)
mgu term6 term7;;
(* substitution = [(Var "x", Node(Sym "0", [])); (Var "z", Node(Sym "0", []))] *)
mgu term8 term9;;
(* substitution = [(Var "z", Node (Sym "-", [V (Var "x"); Node (Sym "0", [])]));
 (Var "y", Node (Sym "-", [Node (Sym "1", []); V (Var "x")]))] *)

(* END OF CODE *)