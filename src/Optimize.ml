(* Optimization of coercions in an IL expression *)
open Printf
open IL


(* Optimization of expressions *)

let rec optim (l: lam) : lam =
  match l with
  |	Lcoerce (lambda, c2) ->
	  optim_coercion lambda c2
  | Lvar v -> Lvar v
  | Labstr(v, l) -> Labstr(v, optim l)
  | Lapp(l1, l2) -> Lapp(optim l1, optim l2)
  | Llet(v, l1, l2) -> Llet(v, optim l1, optim l2)
  | Lconst c -> Lconst c
  | Lunop(op, l1) -> Lunop(op, optim l1)
  | Lbinop(op, l1, l2) -> Lbinop(op, optim l1, optim l2)
  | Ltuple ll -> Ltuple (List.map optim ll)
  | Lfield(l, n) -> Lfield(optim l, n)


and optim_coercion (l : lam) (c2: coercion) =
  match optim l, c2 with
  | Lcoerce (l0, c1), _ ->
	let c = compose_coercions c1 c2 in
	Lcoerce(l0, c)
  (* Don't build big records that are coerced to smaller ones immdiately *)
  | Ltuple lam_list, Crecord i_coercion_list ->
		(* Case 1 : same number of fields, maybe we 
		   can simplify the coercion to Cid *)
	if List.length lam_list = List.length i_coercion_list then
	  let rec simpl_rec_coercion i_c_list index =
		match i_c_list with
		| [] -> Cid
		| hd::tl -> 
		  begin
			if (snd hd) = Cid && (fst hd) = index then
			  simpl_rec_coercion tl (index+1)
			else
			  c2
		  end
	  in
	  Lcoerce (l, (simpl_rec_coercion i_coercion_list 0))
	(* O/w simplify the record, we don't need the full tuple ! *)
	else
	  let rec simplify co_list =
		match co_list with
		| [] -> []
		| hd::tl ->
		  (optim_coercion (List.nth lam_list (fst hd)) (snd hd))::(simplify tl)
	  in
	  Ltuple (simplify i_coercion_list)
  | _ -> Lcoerce (l, c2)


  (*
	In case of nested coercions we have a lambda of the form
	 Lcoerce( Lcoerce(a, c1), c2) , we want to find the coercion c
	 so we can replace this term by Lcoerce (l , c)
  *)
and compose_coercions c1 c2 =
  match c1, c2 with
  | Cid, _ -> c2 | _ , Cid -> c1
  | c1', c2' when c1' = c2' -> c1
  | Cfun (a1, b1) , Cfun (a2, b2) ->
	Cfun( compose_coercions a1 a2, compose_coercions b1 b2)
  | Crecord r1, Crecord r2 ->
	begin
	  let rec merge r_in r' =
		match r_in with 
		| [] -> []
		| hd :: tl ->
		  try 
			let elt = List.find (fun x -> (fst x) = (fst hd)) r' in
			  (fst hd, compose_coercions (snd hd) (snd elt))::
				(merge tl r')
		  with Not_found -> failwith "Bad record coercion"
	  in
	  Crecord (merge r2 r1)
	end
  | _ -> failwith "Should not happen"
