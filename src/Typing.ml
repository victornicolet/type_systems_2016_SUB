(* Type-checking for the SUB language *)

open Printf
open AST

(* Reporting of type errors *)

exception Type_error of string

let type_error msg = raise (Type_error msg)

(* Subtyping check *)

let rec subtype t1 t2 = 
  if t1 = t2 
  then true (* SUBREFL *)
  else begin
	match t1, t2 with
	| _, Top -> true (* SUBTOP *)
	| Int, Float -> true (* SUBNUM *)
	| Arrow( s1, s2), Arrow( s3, s4) ->
	  (subtype s3 s1) && (subtype s2 s4) (* SUBFUN*)
	| Record r1, Record r2 ->
	  subtyperecs r1 r2 
		(* SUBREC *)
	| _, _ -> false
  end
and subtyperecs r1 r2 =
  match r2 with
  | [] -> true
  | hd::tl ->
	try
	  List.find
		(fun  x -> (fst x)=(fst hd)&& (subtype (snd x) (snd hd))) r1;
	  subtyperecs r1 tl
	with Not_found -> printf "Not found\n"; false
	  
(* Infer the principal type for expression [e] in typing environment [env].
   Raise [Type_error] if the expression is ill-typed. *)

let rec infer env e =
  match e with
  (* The lambda-calculus *)
  | Evar v ->
      begin match lookup_typenv v env with
      | Some t -> t
      | None -> type_error (sprintf "unbound variable %s" v)
      end
  (* Lam *)
  | Eabstr (v, t, expr) ->
	let nw_env = add_typenv v t env in
	let t2 = infer nw_env expr in
	Arrow(t, t2)
  (* App *)
  | Eapp (e1, e2) ->
	begin match infer env e1 with
	| Arrow (t1, t2) -> 
	  check env e2 t1; t2
	| _ -> type_error (sprintf "not a function ")
	end
  | Elet (v, ev, es) ->
	let typ_v = infer env ev in
	let nw_env = add_typenv v typ_v env in
	infer nw_env es
  (* Arithmetic *)
  | Econst c ->
      type_of_constant c
  | Eunop(op, e1) ->
      let (targ, tres) = type_of_unop op in
      check env e1 targ;
      tres
  | Ebinop(op, e1, e2) ->
      let (targ1, targ2, tres) = type_of_binop op in
      check env e1 targ1;
      check env e2 targ2;
      tres
  (* Records *)
  | Erecord field_list ->
	Record (List.map (fun x -> (fst x), (infer env (snd x))) field_list)
  | Efield (expr, label) ->
	begin
	match infer env expr with
	| Record fields -> 
	  begin
		try
		  let elt = List.find (fun x -> (fst x) = label) fields in
		  (snd elt)
		with Not_found -> type_error ("Label not in record") 
	  end
	  | _ -> type_error ("Not a record in field access")
	end
  (* Type constraint *)
  | Econstraint(e, t) ->
      check env e t; t

(* Check that expression [e] has type [t] in typing environment [env].
   Return [()] if true.  Raise [Type_error] if not. *)

and check env e t =
  let t1 = infer env e in
  if not (subtype t1 t) then
    type_error
      (sprintf "expected type %s, got %s" (pretty_typ t) (pretty_typ t1))
