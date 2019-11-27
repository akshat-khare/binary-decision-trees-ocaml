open List;;
type prop = T | F | L of string 

                  | Not of prop

                  | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop
              ;;
let rec listletters a l= match a with
| T -> l
| F -> l
| L string -> string::l
| Not b -> append (listletters b []) l
| And (b,c) -> append (append (listletters b []) (listletters c [])) l 
| Or (b,c) -> append (append (listletters b []) (listletters c [])) l 
| Impl (b,c) -> append (append (listletters b []) (listletters c [])) l 
| Iff (b,c) -> append (append (listletters b []) (listletters c [])) l 
;;
let rec uniquelist l = match l with
| a::b -> if (mem a b) then (uniquelist b) else a::(uniquelist b)
| [] -> []
;;
let letters a = uniquelist (listletters a []);;

let rec truth a fn = match a with
| T -> true
| F -> false
| L string -> fn string
| Not b -> not (truth b fn)
| And(F, _ ) -> false
| And(_, F) -> false
| And (b,c) -> (truth b fn) && (truth c fn)
| Or(T, _)-> true
| Or(_,T) -> true
| Or (b,c) -> (truth b fn) || (truth c fn)
| Impl(F, _) -> true
| Impl(_, T) -> true
| Impl (b,c) -> (not (truth b fn)) || (truth c fn) 
| Iff (b,c) -> ((truth b fn) && (truth c fn))  || ((not (truth c fn)) && (not (truth b fn)))
;;
let rec replaceivar a str p = match a with
| T -> T
| F -> F
| L string -> if (string=str) then p else (L string)
| Not b -> Not (replaceivar b str p)
| And (b,c) -> And((replaceivar b str p), (replaceivar c str p))
| Or (b,c) -> Or((replaceivar b str p), (replaceivar c str p))
| Impl (b,c) -> Impl((replaceivar b str p), (replaceivar c str p))
| Iff (b,c) -> Iff((replaceivar b str p), (replaceivar c str p))
;;
exception DontCare;;
let testtable a = match a with
| _ -> raise DontCare;; 

let add ttable i l h = let curlen = length ttable in
					let ttable = ttable@[(i,l,h)] in
					(curlen, ttable);;
let member htable i l h = 
	let rec findilh htable i l h = (match htable with
	| [] -> false
	| x::xs -> let isilh x i l h = (match x with
									| (tuplethis, u) -> (if (tuplethis= (i,l,h)) then true else false)) in
				if (isilh x i l h) then true else (findilh xs i l h)
	) in 
	(findilh htable i l h);;
exception Lookup;;
let lookup htable i l h = 
	let rec findilh htable i l h = (match htable with
	| [] -> raise Lookup
	| x::xs -> let isilh x i l h = (match x with
									| (tuplethis, u) -> (if (tuplethis= (i,l,h)) then true else false)) in
				if (isilh x i l h) then (
					let a, b = x in
					b
				) else (findilh xs i l h)
	) in 
	(findilh htable i l h);;
let insert htable i l h u = htable@[((i,l,h),u)];;

let mk ttable htable i l h =
	if l=h then (ttable, htable, l)
	else if (member htable i l h) then (ttable, htable, (lookup htable i l h))
	else let u, ttable = add ttable i l h in
		let htable = insert htable i l h u in
		(ttable, htable, u);;
let build ttable htable t =
	let lettersList = letters t in
	let n = length lettersList in
	let rec builddash ttable htable t i = 
		if (i<n) then (
			let trutht = truth t testtable in
			if (trutht=false) then (ttable, htable, 0) else (ttable, htable, 1)
		)
		else (
			let replaceiwithFalse = replaceivar t (nth lettersList (i-1)) F in
			let replaceiwithTrue = replaceivar t (nth lettersList (i-1)) T in
			let ttable, htable, v0 = builddash ttable htable replaceiwithFalse (i+1) in
			let ttable, htable, v1 = builddash ttable htable replaceiwithTrue (i+1) in
			mk ttable htable i v0 v1
		)
	in
	builddash ttable htable t 1
;;




