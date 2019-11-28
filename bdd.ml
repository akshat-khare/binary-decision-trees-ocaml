open List;;
type prop = T | F | L of int

                  | Not of prop

                  | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop
              ;;
let rec listletters a l= match a with
| T -> l
| F -> l
| L i -> i::l
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
| L i -> fn i
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
let rec replaceivar a ivar p = match a with
| T -> T
| F -> F
| L i -> if (i=ivar) then p else (L i)
| Not b -> Not (replaceivar b ivar p)
| And (b,c) -> And((replaceivar b ivar p), (replaceivar c ivar p))
| Or (b,c) -> Or((replaceivar b ivar p), (replaceivar c ivar p))
| Impl (b,c) -> Impl((replaceivar b ivar p), (replaceivar c ivar p))
| Iff (b,c) -> Iff((replaceivar b ivar p), (replaceivar c ivar p))
;;
exception DontCare;;
let testtable a = match a with
| _ -> raise DontCare;; 

let rec removeImpliesIff a = match a with
| Impl(c,d) -> removeImpliesIff (Or(Not(c),d))
| Iff(c,d) -> removeImpliesIff (Or(And(c,d), And(Not(c),Not(d))))
| T -> T
| F -> F
| Not b -> Not (removeImpliesIff b)
| And (c,d) -> And ((removeImpliesIff c), (removeImpliesIff d))
| Or (c,d) -> Or ((removeImpliesIff c), (removeImpliesIff d))
| L string -> L string
;;

let rec pushNegationsInside a = match a with
| Not T -> F
| Not F -> T
| Not(And(c,d)) -> pushNegationsInside (Or((Not(c)), (Not(d))))
| Not(Or(c,d)) -> pushNegationsInside (And((Not(c)), (Not(d))))
| Not(Not(b)) -> pushNegationsInside b
| T -> T
| F -> F
| L string -> L string
| Not b -> Not (pushNegationsInside b)
| And (c,d) -> And ((pushNegationsInside c), (pushNegationsInside d))
| Or (c,d) -> Or ((pushNegationsInside c), (pushNegationsInside d))
| Impl (c,d) -> Impl ((pushNegationsInside c), (pushNegationsInside d))
| Iff (c,d) -> Iff ((pushNegationsInside c), (pushNegationsInside d))
;;

let rec pushDisjunctionsInside a = match a with
| Or(c, And(d, e)) -> pushDisjunctionsInside (And((Or(c,d)),(Or(c,e))))
| Or(And(d, e),c) -> pushDisjunctionsInside (And((Or(c,d)),(Or(c,e))))
| T -> T
| F -> F
| L string -> L string
| Not b -> Not b
| And (c,d) -> And ((pushDisjunctionsInside c), (pushDisjunctionsInside d))
| Or (c,d) -> Or ((pushDisjunctionsInside c), (pushDisjunctionsInside d))
| Impl (c,d) -> Impl ((pushDisjunctionsInside c), (pushDisjunctionsInside d))
| Iff (c,d) -> Iff ((pushDisjunctionsInside c), (pushDisjunctionsInside d))
;; 

let rec pushConjunctionsInside a = match a with
| And(c, Or(d, e)) -> pushConjunctionsInside (Or((And(c,d)),(And(c,e))))
| And(Or(d, e),c) -> pushConjunctionsInside (Or((And(c,d)),(And(c,e))))
| T -> T
| F -> F
| L string -> L string
| Not b -> Not b
| And (c,d) -> And ((pushConjunctionsInside c), (pushConjunctionsInside d))
| Or (c,d) -> Or ((pushConjunctionsInside c), (pushConjunctionsInside d))
| Impl (c,d) -> Impl ((pushConjunctionsInside c), (pushConjunctionsInside d))
| Iff (c,d) -> Iff ((pushConjunctionsInside c), (pushConjunctionsInside d))
;; 

let nnf a = pushNegationsInside (removeImpliesIff a);;
let cnf a = pushDisjunctionsInside (nnf a);;
let dnf a = pushConjunctionsInside (nnf a);;

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
	if l=h then l
	else if (Hashtbl.mem htable (i, l, h)) then (Hashtbl.find htable (i, l, h))
	else let u = Hashtbl.length ttable in
		(Hashtbl.add ttable u (i,l,h));
		(Hashtbl.add htable (i,l,h) u);
		u;;
let rec maxElem l i = match l with
| [] -> i
| x::xs -> if x<i then (maxElem xs i) else (maxElem xs x);;

let build t =
	let lettersList = letters t in
	let n = (maxElem lettersList 0) in
	let htable = Hashtbl.create 111111 in
	let ttable = Hashtbl.create 111111 in
	Hashtbl.add ttable 0 ((n+1),0,0);
	Hashtbl.add ttable 1 ((n+1),0,0);
	let rec builddash ttable htable t i = 
		if (i>n) then (
			let trutht = truth t testtable in
			if (trutht=false) then 0 else 1
		)
		else (
			let replaceiwithFalse = replaceivar t i F in
			let replaceiwithTrue = replaceivar t i T in
			let v0 = builddash ttable htable replaceiwithFalse (i+1) in
			let v1 = builddash ttable htable replaceiwithTrue (i+1) in
			mk ttable htable i v0 v1
		)
	in
	let ans = builddash ttable htable t 1 in
	ttable
;;
let simplemax a b = if a>b then a else b;;

let var table u = let (a,b,c) = Hashtbl.find table u in a;;
let low table u = let (a,b,c) = Hashtbl.find table u in b;;
let high table u = let (a,b,c) = Hashtbl.find table u in c;;

let apply tbdd1 tbdd2 u1 u2 op =
	let n1, _, _  = Hashtbl.find tbdd1 0 in
	let n2,_,_ = Hashtbl.find tbdd2 0 in
	let n = simplemax n1 n2 in
	let gtable = Hashtbl.create 111111 in
	let ttable = Hashtbl.create 111111 in
	let htable = Hashtbl.create 111111 in
	Hashtbl.add ttable 0 (n,0,0);
	Hashtbl.add ttable 1 (n,0,0);
	let rec app u1 u2 = 
		if(Hashtbl.mem gtable (u1,u2)) then (Hashtbl.find gtable (u1,u2))
		else if ((u1=0 || u1=1) && (u2=0 || u2=1)) then 
			let u = (op u1 u2) in
			Hashtbl.add gtable (u1,u2) u;
			u
		else if (var tbdd1 u1) = (var tbdd2 u2) then
			let first = (app (low tbdd1 u1) (low tbdd2 u2)) in
			let second = (app (high tbdd1 u1) (high tbdd2 u2)) in
			let u = mk ttable htable (var tbdd1 u1) first second in
			Hashtbl.add gtable (u1, u2) u;
			u
		else if (var tbdd1 u1) < (var tbdd2 u2) then
			let first = (app (low tbdd1 u1) u2) in
			let second = (app (high tbdd1 u1) u2 ) in
			let u = mk ttable htable (var tbdd1 u1) first second in
			Hashtbl.add gtable (u1,u2) u;
			u
		else
			let first = (app u1 (low tbdd2 u2)) in
			let second = (app u1 (high tbdd2 u2)) in
			let u = mk ttable htable (var tbdd2 u2) first second in
			Hashtbl.add gtable (u1, u2) u;
			u
	in
	let ans = (app u1 u2) in
	ttable;;

(* set high for now *)
let restrict t_bdd1 u j b = 
	let n1,_,_= Hashtbl.find t_bdd1 0 in 
	let t_bdd = Hashtbl.create 111111 in 
	let h_bdd = Hashtbl.create 111111 in
	Hashtbl.add t_bdd 0 (10000,0,0);	
	Hashtbl.add t_bdd 1 (10000,0,0);
	let rec res u = 
		if (var t_bdd1 u)>j then u
		else if (var t_bdd1 u)<j then 
				let temp1 = (res (low t_bdd1 u)) in 
				let temp2 = (res (high t_bdd1 u)) in 
				mk t_bdd h_bdd (var t_bdd1 u) temp1 temp2
		else if b=0 then (res (low t_bdd1 u))
		else (res (high t_bdd1 u))
	in 
	let f = (res u) in 
	t_bdd;;

let satcount t_bdd u = 
	let rec count u = 
		if (u=0) then
			let res = 0 in
			res
		else if (u=1) then
			let res = 1 in
			res
		else 
			let lowu = low t_bdd u in
			let highu = high t_bdd u in
			let varu = var t_bdd u in
			let twofirstpower = int_of_float(2.0**(float_of_int((var t_bdd lowu) - (varu) -1))) in
			let twosecondpower =  int_of_float(2.0**(float_of_int((var t_bdd highu) - (varu) -1))) in
			let res = twofirstpower*(count lowu) + twosecondpower*(count highu) in
			res
		in
	let twopower = int_of_float(2.0**(float_of_int((var t_bdd u)-1))) in
	let ans = twopower * (count u) in
	ans;;

exception AnysatError;;

let rec anySat t_bdd u = 
	if (u=0) then raise AnysatError
	else if (u=1) then []
	else if ((low t_bdd u)=0 ) then ((var t_bdd u), 1)::(anySat t_bdd (high t_bdd u))
	else ((var t_bdd u),0)::(anySat t_bdd (low t_bdd u))
;;

let rec all_union l x = match l with 
	  [] -> []
	| h::ls -> (x::h)::(all_union ls x)
;;

let rec allSat t_bdd u =
	if u=0 then []
	else if u=1 then [[]]
	else 
		let (r1) = (allSat t_bdd (high t_bdd u)) in
		let (r2) = (allSat t_bdd (low t_bdd u)) in
		let u1 = all_union r1 ((var t_bdd u), 1) in   
		let u2 = all_union r2 ((var t_bdd u), 0) in   
		u1@u2
	;;

let andOP a b = match (a,b) with
| (1,1) -> 1
| _ -> 0
;;
let orOP a b = match (a,b) with
| (0,0) -> 0
| _ -> 1
;;

let iffOP a b = match (a,b) with
| (1,1) -> 1
| (0,0) -> 1
| _ -> 0
;;
let implOP a b = match (a,b) with
| (1,0) -> 0
| _ -> 1
;;

let vx1 = L(1);;
let vx2 = L(2);;
let vx3 = L(3);;

let p0 = Iff(vx1, vx2);;
let p1 = Or(p0,vx3);;
let p2 = Or(vx2,vx3);;
let np1 = Not(p1);;

let p1' = nnf(p1);;
let p1'' = cnf(p1);;
let np1' = nnf(np1);;
let np1'' = cnf(np1);;

let tt = build T;;
let tf = build F;;

let tvx1 = build vx1;;
let tp2 = build p2;;
let tp0 = build p0;;
let tp1 = build p1;;
let tp1' = build p1';;
let tp1'' = build p1'';;

let tnp1 = build np1;;
let tnp1' = build np1';;
let tnp1'' = build np1'';;




(* 1 *)
tp1 = tp1';;
tp1 = tp1'';;
tnp1 = tnp1';;
tnp1 = tnp1'';;

(* 2 *)
let tp1anp1 = apply tp1 tnp1  ((Hashtbl.length tp1) - 1) ((Hashtbl.length tnp1) - 1) andOP;;
tp1anp1 = tf;;
let tp1onp1 = apply tp1 tnp1  ((Hashtbl.length tp1) - 1) ((Hashtbl.length tnp1) - 1) orOP;;
tp1onp1 = tt;;

(* 3 *)
let tp1rv30 = restrict tp1 ((Hashtbl.length tp1)-1) 3 0 ;;
tp1rv30 = tp0;;
let tp1rv31 = restrict tp1 ((Hashtbl.length tp1)-1) 3 1;;
tp1rv31 =  tt;;

(* 4 *)
satcount tp1 ((Hashtbl.length tp1) -1);;
let allsat1ans = allSat tp1 ((Hashtbl.length tp1) -1);;
let anysat1ans = anySat tp1 ((Hashtbl.length tp1) -1);;
length allsat1ans;;
length anysat1ans;;

