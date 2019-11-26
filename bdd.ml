open List;;

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
	let builddash t i = 
		if (i<)