type a = A | B | C | D;;
type 'a a_star = EmptyString | String of ('a list * 'a * 'a list * 'a * 'a * int);;
(* Stores an empty string or a string with (back list, pointer, front list, first, last, pointer position) *)

exception AtLast;;
exception AtFirst;;
exception TooShort;;
exception Empty;;

let create s = match s with
	(** [string -> char a_star]  *)
	"" -> EmptyString
  |	_ ->let rec exp i l=
    			if i < 1 then l else exp (i - 1) (s.[i] :: l) in
    		String ([], s.[0], (exp (String.length s -1) []), s.[0], s.[(String.length s -1)], 0);;

let forward s = match s with
	(** ['a a_star -> 'a a_star]  *)
	EmptyString -> raise Empty
  | String(_, _, [], _, _, _) -> raise AtLast
  | String(a, b, c::c', d, e, f) -> String(b::a, c, c', d, e, f+1);;
  (* Constant number of steps for shifting list elements and adding 1 to pointer position => O(1) *)

let back s = match s with
	(** ['a a_start -> 'a a_star]  *)
	EmptyString -> raise Empty
  | String([], _, _, _, _, _) -> raise AtFirst
  | String(a::a', b, c, d, e, f) -> String(a', a, b::c, d, e, f-1);;
  (* Constant number of steps for shifting list elements and subtracting 1 from pointer position => O(1) *)

let lgh s = match s with
	(** ['a a_star -> int]  *)
	EmptyString -> 0
  | String(a, b, c, d, e, f) -> 
    let rec length x = match x with
    	[] -> 0
      | x::xs -> 1 + (length xs) in
    1 + (length a) + (length c);;
    (* The lgh function takes recursive calls to the front and back lists to get their lengths
    Thus O(size of lists) = O(size of front list) + O(size of back list) = O(n), where 
   	n = the length of string. *)

let moveTo n s =
	(** [int -> 'a a_star -> 'a a_star]  *)
	if n>=lgh(s) then raise TooShort else
  	let rec mov s = match s with
  		EmptyString -> raise Empty
  	  | String(a,b,c,d,e,f) -> if f<n then mov (forward s) else if f>n then mov (back s) else s in
  	mov s;;
  	(* For movement to position 'n' from position 'p' it takes 'n-p' forward calls of O(1)
  	Thus move complexity = O(n-p). For length calculation O(n). Thus, movTo is O(n). *)

let replace w s = match s with
	(** ['a -> 'a a_star -> 'a a_star]  *)
	EmptyString -> raise Empty
  | String([], b, c::c', d, e, f) -> String([], w, c::c', w, e, f)
  | String(a::a', b, [], d, e, f) -> String(a::a', w, [], d, w, f)
  | String([], b, [], d, e, f) -> String([], w, [], w, w, f)
  | String(a, b, c, d, e, f) -> String(a, w, c, d, e, f);; 
  (* O(1) operation. Proof that lgh(replace w s) = lgh(s):
  lgh(s) = 1 + length(back list) + length(front list). As the replace operation changes the 
  character at pointer, and first and last elements so lengths of front and back lists remain
  unchanged, and hence the sum is 1 + length(back list) + length(front list) = lgh(replace w s) *)

let nonempty s = match s with
	(** ['a a_star -> bool]  *)
	EmptyString -> false
  | _ -> true;;
  (* O(1) pattern match. *)

let concat s1 s2 = match (s1, s2) with
	(** ['a a_star -> 'a a_star -> 'a a_star]  *)
	(EmptyString, a) -> a
  | (a, EmptyString) -> a
  | (String(a, b, c, d, e, f), String(a', b', c', d', e', f')) -> 
  			let rec rev l = match l with
  				[] -> []
  			  | x::xs -> (rev xs)@[x] in
  			String(a, b, c@(rev a')@[b']@(c'), d, e', f);;
  (* O(1) pattern match, but for non empty strings, the recursive function is called till the first
  list of s2 is reversed (and each call is O(1)), so O(pointer position of s2) time complexity. 
  Concatenation is O(sie of second list), so total complexity is O(size(s2)).
  Proof that lgh(concat s1 s2) = lgh(s1) + lgh(s2):
  let the alphabets a, b, c, a', b', c' denote what is used in this case then 
  lgh(s1) = 1 + size(a) + size(c), lgh(s2) = 1 + size(a') + size(c'), thus lgh(s1) + lgh(s2) = 
  2 + size(a) + size(c) + size(a') + size(c'). Now, when concatenating, size of rev(a') is same as
  size(a') as only the elements are reversed. Also, appending lists leads to addition of their sizes. 
  Thus lgh(concat s1 s2) = 1 + size(a) + size(c@(rev a')@[b']@(c')) = 1 + size(a) + size(c) + size(rev a') 
  size([b']) + size(c') = 1 + size(a) + size(c) + size(a) + 1 + size(c') = 2 + size(a) + size(c) + 
  size(a') + size(c') = lgh(s). Hence proved. *)

let reverse s = match s with
	(** ['a a_star -> 'a a_star]  *)
	EmptyString -> EmptyString
  |	String(a, b, c, d, e, f) -> String(c, b, a, e, d, lgh(s) - f - 1);;
  (* O(1) pattern match and O(n) lgh calculation thus reverse is O(n). Proof that lgh(reverse s) = lgh(s):
  lgh(s) = 1 + size(a) + size(c) = 1 + size(c) + size(a) {by commutativity of arithmetic addition} = 
  lgh(reverse s). Hence proved. {Note: Pointer remains on same element as before} *)

let first s = match s with
	(** ['a a_star -> 'a]  *)
	EmptyString -> raise Empty
  | String(a, b, c, d, e, f) -> d;;
  (* O(1) pattern match *)

let last s = match s with
	(** ['a a_star -> 'a]  *)
	EmptyString -> raise Empty
  | String(a, b, c, d, e, f) -> e;;
  (* O(1) pattern match *)

(* End of Code *)


(* Testcases *)

let alphabet=["1"; "2"; "a"; "b"; "c"; "A"];;

lgh EmptyString;;
lgh (create "a");;
lgh (create "abc");;
lgh (create "12");;

nonempty EmptyString;;
nonempty (create "a");;
nonempty (create "12");;

concat EmptyString EmptyString;;
concat EmptyString (create "a");;
concat (create "1") EmptyString;;
concat (create "1A") (create "abc");;

reverse EmptyString;;
reverse (create "abc");;
reverse (create "12");;

first EmptyString;;
first (create "a");;
first (create "abc");;

last EmptyString;;
last (create "a");;
last (create "abc");;

let editable = create "abac12a2aAac211";;

forward editable;;
back editable;;
moveTo 10 editable;;
replace 'b' editable;;
  