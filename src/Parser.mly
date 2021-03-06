/* An ocamlyacc parser for the SUB language */

%{
open Printf
open AST

let make_abstr params body =
  List.fold_right (fun (param, ty) e -> Eabstr(param, ty, e)) params body

let make_tabstr params body =
  List.fold_right (fun param e -> ETabstr (param, e)) params body


let make_univ_typ params typ = 
  List.fold_right (fun var ty -> Parametric (var, ty)) params typ

let make_tapp body typs =
  List.fold_left (fun body ty -> ETapp (body, ty)) body typs

let rec check_duplicates (l: (string * 'a) list) =
  match l with
  | [] -> ()
  | (s, _) :: l ->
      if List.mem_assoc s l then raise (Duplicate_label s);
      check_duplicates l

%}

/* Tokens */

%token COLON
%token COMMA
%token DOT
%token EOF
%token EQUAL
%token FLOAT
%token <float> FLOATCONST
%token FORALL
%token FUN
%token <string> IDENT
%token IN
%token INT
%token <int> INTCONST
%token LBRACE
%token LBRACKET
%token LCHEVRON
%token LET
%token LPAREN
%token MINUSGREATER
%token PLUS
%token PLUSDOT
%token RBRACE
%token RBRACKET
%token RCHEVRON
%token RPAREN
%token SEMI
%token SEMISEMI
%token TOP

/* Precedences and associativities */

%right MINUSGREATER
%right PLUS PLUSDOT

/* Entry points */

%start file
%type <AST.expr list> file
%start phrase
%type <AST.expr option> phrase

%%

/* Grammar of types */

typ:
  | TOP                   { Top }
  | INT                   { Int }
  | FLOAT                 { Float }
  | IDENT                 { Tvar $1}
  | typ MINUSGREATER typ  { Arrow($1,$3) }
  | LBRACE rectyp RBRACE  { check_duplicates $2; Record $2 }
  | LBRACE RBRACE         { Record [] }
  | LPAREN typ RPAREN     { $2 }
  | FORALL typvars COMMA typ { make_univ_typ $2 $4}
;

typvars:
  | IDENT { [$1] }
  | IDENT typvars { $1 :: $2 }

rectyp:
  | lbltyp                { [$1] }
  | lbltyp SEMI rectyp    { $1 :: $3 }
;

lbltyp:
    IDENT COLON typ       { ($1,$3) }
;

/* Grammar of expressions */

expr:
  | expr2                             { $1 }
  | FUN funparams MINUSGREATER expr   { make_abstr $2 $4 }
  | LCHEVRON typparams RCHEVRON expr  { make_tabstr $2 $4 }
  | LET IDENT EQUAL expr IN expr      { Elet($2,$4,$6) }
  | LET IDENT funparams EQUAL expr IN expr
                                      { Elet($2, make_abstr $3 $5, $7) }
  | LET IDENT LCHEVRON typparams RCHEVRON funparams EQUAL expr IN expr
	                                  { Elet($2, make_tabstr $4 (make_abstr $6 $8), $10) }
;

expr2:
  | expr2 PLUS expr2                  { Ebinop(Oaddint,$1,$3) }
  | expr2 PLUSDOT expr2               { Ebinop(Oaddfloat,$1,$3) }
  | expr1                             { $1 }
;

expr1:
  | expr1 expr0                       { Eapp($1, $2) }
  | expr1 LBRACKET typargs RBRACKET   { make_tapp $1 $3 }
  | INT expr0                         { Eunop(Ointoffloat, $2) }
  | FLOAT expr0                       { Eunop(Ofloatofint, $2) }
  | expr0                             { $1 }
;

expr0:
  | IDENT                             { Evar $1 }
  | INTCONST                          { Econst(Cint $1) }
  | FLOATCONST                        { Econst(Cfloat $1) }
  | LBRACE recexpr RBRACE             { check_duplicates $2; Erecord $2 }
  | LBRACE RBRACE                     { Erecord [] }
  | expr0 DOT IDENT                   { Efield($1,$3) }
  | LPAREN expr COLON typ RPAREN      { Econstraint($2,$4) }
  | LPAREN expr RPAREN                { $2 }
;

recexpr:
  | lblexpr                           { [$1] }
  | lblexpr SEMI recexpr              { $1 :: $3 }
;

lblexpr:
    IDENT EQUAL expr2                 { ($1,$3) }
;

funparams:
  | funparam                          { [$1] }
  | funparam funparams                { $1 :: $2 }
;

funparam:
    LPAREN IDENT COLON typ RPAREN     { ($2,$4) }
;

typargs:
  | typ { [$1] }
  | typ typargs { $1 :: $2 }

typparams:
  | IDENT { [$1] }
  | IDENT typparams { $1 :: $2 }

/* Entry points */

file:
  | EOF                 { [] }
  | expr SEMISEMI file  { $1 :: $3 }
;

phrase:
  | EOF                 { None }
  | expr SEMISEMI       { Some $1 }
;
