(* Type-directed elaboration of SUB expressions into IL expressions *)

open Printf
open AST
open IL

(* Reporting of type errors *)

exception Type_error of string

let type_error msg = raise (Type_error msg)

let rec func pred lst c = match lst with
    | [] -> raise(Failure "Not Found")
    | hd::tl -> if pred hd then c else func pred tl (c+1)

let nthfind pred lst = func pred lst 0

(* Subtyping check.  If [t1] is a subtype of [t2], return the coercion 
   that transforms values of type [t1] into values of type [t2].
   If [t1] is not a subtype of [t2], raise [Not_subtype] exception. *)

exception Not_subtype

let rec subtype t1 t2 =
  if t1 = t2 
  then Cid
  else begin
	match t1, t2 with
	| _ , Top -> Cid
	| Int, Float -> Cint2float
	| Arrow(s1, s2), Arrow(s3, s4) ->
	  Cfun ((subtype s3 s1),(subtype s2 s4))
	| Record r1, Record r2 ->
	  Crecord( subtyperecs r1 r2)
	| _, _ -> raise Not_subtype
  end
and subtyperecs r1 r2 =
  let matching x1 x2 = 
	try
	  let coercion = subtype (snd x1) (snd x2) in
	  ((fst x1)=(fst x2), coercion)
	with Not_subtype -> (false, Cid)
  in
  let rec aux hd list c =
	begin
  			match list with
			| [] -> raise Not_subtype
			| r::rtl -> 
			  let matches, coercion =  matching r hd in
						if matches then (c, coercion)
						else aux hd rtl (c+1)
	end
  in
	  match r2 with
	  | [] -> []
	  | hd :: tl -> (aux hd r1 0)::(subtyperecs r1 tl)
								 

(* Elaborate the expression [e] in typing environment [env].
   Return a pair of the principal type and the IL term.
   Raise [Type_error] if the expression is ill-typed. *)

let rec elab env e = 
  match e with 
	(* Lambda calc *)
  | Evar v -> 
	let var_t = match lookup_typenv v env with
	  | Some t -> t
	  | None -> type_error (sprintf "Unbound variable %s" v) 
	in
	var_t, Lvar v

  | Eabstr (v, t, expr) ->
	let nw_env = add_typenv v t env in
	let lam_t, lam = elab nw_env expr in
	Arrow(t, lam_t),	Labstr (v, lam)

  | Eapp (e1, e2) ->
	begin match elab env e1 with 
	| Arrow (t1, t2), il1 ->
	  let il2 = check env e2 t1 in
	  t2, Lapp (il1, il2)

	| t, _ -> type_error (sprintf "not an arrow %s"
							(pretty_typ t))	
	end
  | Elet (v, ev, es) ->
	let typ_v, lam_v = elab env ev in
	let nw_env = add_typenv v typ_v env in
	let typ_s, lam_s = elab nw_env es in
	typ_s, Llet(v, lam_v, lam_s)
	

  (* Arithmetic *)
  | Econst c ->
	type_of_constant c, Lconst c

  | Eunop(op, e) ->
	let (targ, tres) = type_of_unop op in
	let lam = check env e targ in
	tres, Lunop (op, lam)

  | Ebinop(op, e1, e2) ->
	let (targ1, targ2, tres) = type_of_binop op in
	let lam1 = check env e1 targ1 in
	let lam2 = check env e2 targ2 in
	tres, Lbinop(op, lam1, lam2)

  | Erecord field_list ->
	let recl = List.map 
	  (fun x -> (fst x), (elab env (snd x)))
	  field_list
	in 
	Record (List.map (fun x -> fst x, (fst (snd x))) recl),
	Ltuple (List.map (fun x -> snd (snd x)) recl)
(* Record acess *)
  | Efield (expr, label) ->
	begin
    match elab env expr with
	| Record list, lam ->
	  let pos = nthfind (fun x -> (fst x) = label) list in
	  (snd (List.nth list pos)) , Lfield (lam, pos)
	| t , _ -> 
	  type_error 
		(sprintf "expected a record, but has type %s" 
		   (pretty_typ t))
	end

  | Econstraint(e, t) ->
	t, check env e t

(* Check that expression [e] has type [t] in typing environment [env].
   Return its lambda translation if so.
   Raise [Type_error] if not. *)

and check env e t = 
  let t1, lam = elab env e in
  let coercion = 
	try
	  subtype t1 t 
	with Not_subtype -> 
	  raise (Type_error 
			   (sprintf "expected type %s, got %s" 
				  (pretty_typ t) 
				  (pretty_typ t1)
			   )
	  )
  in Lcoerce (lam , coercion)
    
