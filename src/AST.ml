open Printf

(* Abstract syntax for the source language SUB *)

type variable = string  (* Names of variables *)
type label = string     (* Names of record labels *)

(* Type expressions *)

type typ =
  | Top
  | Int
  | Float
  | Tvar of variable
  | Arrow of typ * typ
  | Record of rectyp
  | Parametric of(variable * typ)


and rectyp = (label * typ) list

(* Constants and arithmetic operators *)

type constant =
  | Cint of int
  | Cfloat of float

type unop =
  | Ointoffloat
  | Ofloatofint

type binop =
  | Oaddint
  | Oaddfloat

(* Expressions *)

type expr =
  (* The lambda-calculus *)
  | Evar of variable
  | Eabstr of variable * typ * expr
  | Eapp of expr * expr
  | Elet of variable * expr * expr
  (* Arithmetic *)
  | Econst of constant
  | Eunop of unop * expr
  | Ebinop of binop * expr * expr
  (* Records *)
  | Erecord of (label * expr) list
  | Efield of expr * label
  (* Type constraint *)
  | Econstraint of expr * typ
  (* Parametric polymorphism *)
  | ETabstr of variable * expr
  | ETapp of expr * typ

(* Utility functions *)

let rec pretty_typ = function
  | Arrow(t1, t2) -> pretty_typ1 t1 ^ " -> " ^ pretty_typ t2
  | t -> pretty_typ1 t

and pretty_typ1 = function
  | Top -> "T"
  | Int -> "int"
  | Float -> "float"
  | Tvar v -> v
  | Record rt -> "{" ^ String.concat "; " (List.map pretty_field rt) ^ "}"
  | Parametric (tl, t) -> "forall " ^ tl ^ " : " ^ pretty_typ t
  | t -> "(" ^ pretty_typ t ^ ")"

and pretty_field (lbl, ty) =
  lbl ^ ":" ^ pretty_typ ty

let type_of_constant = function
  | Cint _ -> Int
  | Cfloat _ -> Float

let type_of_unop = function
  | Ointoffloat -> (Float, Int)
  | Ofloatofint -> (Int, Float)

let type_of_binop = function
  | Oaddint -> (Int, Int, Int)
  | Oaddfloat -> (Float, Float, Float)

let var_counter = ref 0

let fresh_variable () =
  incr var_counter;
  "%" ^ string_of_int !var_counter

(* Typing environments *)

module StringMap = Map.Make(String)

type typenv = typ StringMap.t

let empty_typenv = StringMap.empty

let add_typenv = StringMap.add

let lookup_typenv x env =
  try Some(StringMap.find x env) with Not_found -> None

(* Other typing utilities *)
exception Typ_error of string

let	rec subst_type_var a ty_var ty =
  match ty with
  | Tvar v -> if v = a then ty_var else Tvar v
  | Int | Float | Top -> ty
  | Arrow (t1, t2) -> 
	Arrow (subst_type_var a ty_var t1,
		   subst_type_var a ty_var t2)
  | Record tlist ->
	Record (List.map (fun ft -> 
	  (fst ft, subst_type_var a ty_var (snd ft))) tlist)
  | Parametric (b, t) ->
	begin
	  if b = a then
		failwith "Type variable is already in use !" 
	  else
		Parametric(b, subst_type_var a ty_var t)
	end

let type_instance univ_type t =
  match univ_type with
  | Parametric (a, ty) ->
	subst_type_var a t ty
  | _ -> 
	raise (Typ_error (sprintf 
				  "Expected a parametric type but got %s" (pretty_typ univ_type)))

(* Exception used for error reporting *)

exception Duplicate_label of string


