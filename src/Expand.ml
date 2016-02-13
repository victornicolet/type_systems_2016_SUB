(* Expand coercions within IL expressions.  The result is an IL expression
   without coercions, suitable for compilation to abstract machine code. *)

open AST
open IL


(* Apply a coercion [c] to the expression [l].  The result is a 
   coercion-free Lambda expression. *)

let rec apply_coercion (c: coercion) (l: lam) : lam =
  match c with
  | Cid -> l
  | Cint2float -> Lunop(Ofloatofint, l)
  | Cfun (co1, co2) -> 
	let x = "co_"^(fresh_variable ()) in
	let lam_x =  Lapp(l, apply_coercion co1 (Lvar x))
	in Labstr( x, apply_coercion co2 lam_x)
  | Crecord i_co_list ->
	let rec coerce_list li =
	  match li with [] -> [] 
	  | hd::tl -> 
	    (apply_coercion (snd hd) (Lfield (l, (fst hd))))::(coerce_list tl)
	in
	Ltuple (coerce_list i_co_list)

(* Recursively expand the coercions by applying them. *)

let rec expand (l: lam): lam =
  match l with
  | Lvar v -> Lvar v
  | Labstr(v, l) -> Labstr(v, expand l)
  | Lapp(l1, l2) -> Lapp(expand l1, expand l2)
  | Llet(v, l1, l2) -> Llet(v, expand l1, expand l2)
  | Lconst c -> Lconst c
  | Lunop(op, l1) -> Lunop(op, expand l1)
  | Lbinop(op, l1, l2) -> Lbinop(op, expand l1, expand l2)
  | Ltuple ll -> Ltuple (List.map expand ll)
  | Lfield(l, n) -> Lfield(expand l, n)
  | Lcoerce(l, c) -> apply_coercion c (expand l)
