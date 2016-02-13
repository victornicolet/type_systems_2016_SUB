(* Compilation of IL (without coercions) to abstract machine code *)

open Printf
open AST
open IL
open Mach

exception Error of string

let findnth x l =
  let rec aux x li c =
	match li with 
	  [] -> raise Not_found | hd :: tl -> if hd=x then c else aux x tl (c+1)
  in
  aux x l 0

let pp_env var_list = 
  List.fold_left (fun o v -> o^"::"^v)  "env " var_list


let rec compile_expression lexpr dbjn =
  match lexpr with 
  | Lvar x ->
	begin
	  try
		let i = (findnth x dbjn)+1  in  [Iaccess i]
	  with Not_found ->
		raise (Error (sprintf "Variable %s not found in %s" x (pp_env dbjn)))
	end
  | Labstr (x, e) ->
	[Iclosure (compile_tail_expression e (x::dbjn))]
  | Lapp (e1, e2) ->
	(compile_expression e1 dbjn)
	@(compile_expression e2 dbjn)
	@[Iapply]
  | Llet (x, e1, e2) ->
	(compile_expression e1 dbjn)
	@[Ilet]
	@(compile_expression e2 (x::dbjn))
	@[Iendlet]
  | Lconst c -> [Ipush c]
  | Lunop (op,e) ->
	let load_vars = compile_expression e dbjn in
	begin
	  match op with
	  | Ointoffloat -> load_vars@[Iintoffloat]
	  | Ofloatofint -> load_vars@[Ifloatofint]
	end
  | Lbinop (op, e1, e2) ->
	let instr1 = compile_expression e1 dbjn in
	let instr2 = compile_expression e2 dbjn in
	begin
	  match op with
	  | Oaddfloat -> instr1@instr2@[Iaddfloat]
	  | Oaddint -> instr1@instr2@[Iaddint]
	end
  | Ltuple t ->
	let len = List.length t in
	(List.fold_left 
	   (fun o list -> o@list) 
	   [] 
	   (List.map (fun ef -> compile_expression ef dbjn) t)
	)
	@[Imaketuple len]
  | Lfield (e, i) ->
	(compile_expression e dbjn)@[Ifield (i+1)]
  | Lcoerce (_,_) ->
	raise (Error "encountered a coercion during compilation.")

and compile_tail_expression lexpr dbjn =
  match lexpr with
  | Llet (x, e1, e2) ->	
	(compile_expression e1 dbjn)
	@[Ilet]
	@(compile_expression e2 (x::dbjn))
	@[Iendlet]
  | Lapp (e1, e2) ->
	(compile_expression e1 dbjn)
	@(compile_expression e2 dbjn)
	@[Itailapply]
  | _ -> (compile_expression lexpr dbjn)@[Ireturn]
	

let program (l: lam): code = compile_expression l []
