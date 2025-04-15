/*******************************************************************************
 * electrod - a model finder for relational first-order linear temporal logic
 * 
 * Copyright (C) 2016-2024 ONERA
 * Authors: Julien Brunel (ONERA), David Chemouil (ONERA)
 * 
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * SPDX-License-Identifier: MPL-2.0
 * License-Filename: LICENSE.md
 ******************************************************************************/

%{
    [@warning "-4"]

(* fixes issue between Menhir and dune *)
(* https://github.com/ocaml/dune/issues/2450 *)
module Libelectrod = struct end

(* Do not declare an alias [R] for the module [Raw], as this will cause
   Menhir >= 20200525 to infer types that refer to [R] instead of [Raw]. *)
(* module R = Raw *)

module G = Gen_goal

let exp_no_arity = G.exp (Some 0)


%}

%start <Raw.raw_urelements list
 * Raw.raw_declaration list
 * Raw.raw_paragraph list> parse_problem

%token UNIV NONE VAR COLON SEMI EOF EQ IN NEQ AND OR HISTORICALLY
%token IMPLIES IFF UNTIL RELEASES SINCE AFTER ONCE BEFORE LET
%token LPAREN RPAREN LBRACKET RBRACKET DOTDOT PLUS ARROW
%token ALL SOME DISJ ONE LONE SET NO COMMA LBRACE RBRACE BAR
%token GT GTE LT LTE TRUE FALSE EVENTUALLY ALWAYS NOT
%token TILDE HAT STAR IDEN ELSE CONST INVARIANT TRIGGERED
%token INTER OVERRIDE LPROJ RPROJ MINUS DOT PRIME
%token THEN NOT_IN RUN EXPECT SAT UNSAT
// for integer expressions
%token UMINUS ADD SUB MUL DIV REM LSHIFT SERSHIFT ZERSHIFT HASH SMALLINT BIGINT SUM IIMPLIES IELSE


%token SYM INST

/* plain ID */
%token <string> PLAIN_ID

/* "dollar" (indexed) ID */
%token <string> IDX_ID

/* colon immediately followed by a nonnegative integer representing the arity */
%token <int> COLON_ARITY

%token <int> NUMBER

/* in ascending order of priority */
%nonassoc BAR
%left OR
%left IFF
%right IMPLIES ELSE
%left AND
%nonassoc RELEASES SINCE UNTIL TRIGGERED
%nonassoc AFTER ALWAYS EVENTUALLY BEFORE HISTORICALLY ONCE
%nonassoc LT LTE GT GTE EQ NEQ IN NOT_IN
%nonassoc NOT
%nonassoc SOME SET LONE ONE      (* for formulas as 'some E' (= E != none) *)
%right IIMPLIES IELSE
%left MINUS PLUS
%nonassoc HASH
%left OVERRIDE
%left INTER
%left ARROW
%left LPROJ RPROJ
%left LBRACKET                  (* for box join *)
%left DOT
%nonassoc PRIME
%nonassoc TILDE HAT STAR

%%

%public parse_problem:
  urelts_list = universe decls = declaration* pars = paragraph+ EOF
	  { (urelts_list, decls, pars) }

paragraph:
    i = insts
    { Raw.ParInst i }
    | sy = syms
    { Raw.ParSym sy }
    | gs = goal
    { Raw.ParGoal gs }
    | f = invariant
    { Raw.ParInv f }

  ////////////////////////////////////////////////////////////////////////
  // universe
  ////////////////////////////////////////////////////////////////////////

universe:
	UNIV COLON urelts_list = braces(urelements*) ioption(SEMI)
	{ urelts_list }

urelements:
  i = interval
	{ Raw.uintvl i }
  | at = PLAIN_ID
  | at = IDX_ID
  { Raw.uplain @@ Raw_ident.ident at $startpos $endpos }
  | nb = NUMBER
  { Raw.uplain @@ Raw_ident.ident (string_of_int nb) $startpos $endpos }


declaration:
	CONST id = PLAIN_ID ar = colon_w_or_wo_arity sc = scope ioption(SEMI)
	{ Raw.dconst (Raw_ident.ident id $startpos(id) $endpos(id)) ar sc }
  |
  VAR id = PLAIN_ID ar = colon_w_or_wo_arity sc = scope
    fby = next_scope? ioption(SEMI)
	{ Raw.dvar (Raw_ident.ident id $startpos(id) $endpos(id)) ar sc fby }

colon_w_or_wo_arity:
  COLON
  { None }
  | ca = COLON_ARITY
  { Some ca }

next_scope: THEN sc = scope
  { sc }

%inline scope:
	b = bound
	{ Raw.sexact b }
	| b1 = bound b2 = bound
	{ Raw.sinexact b1 None b2 }
	| b1 = bound mult = boundmult b2 = bound
	{ Raw.sinexact b1 (mult) b2 }

bound:
	UNIV
	{ Raw.buniv }
  | id = PLAIN_ID
  { Raw.bref (Raw_ident.ident id $startpos(id) $endpos(id)) }
	| b = parens(bound)
	{ b }
    | b1 = bound ARROW b2 = bound
      { Raw.bprod b1 None None b2 }
    | b1 = bound mult1 = boundmult ARROW b2 = bound
      { Raw.bprod b1 (mult1) None b2 }
    | b1 = bound ARROW mult2 = boundmult b2 = bound
      { Raw.bprod b1 None (mult2) b2 }
    | b1 = bound mult1 = boundmult ARROW mult2 = boundmult b2 = bound
      { Raw.bprod b1 (mult1) (mult2) b2 }
	| b1 = bound PLUS b2 = bound
	{ Raw.bunion b1 b2  }
  | elts = braces(element*)
  { Raw.belts elts }

boundmult:
  LONE
   { Some `Lone }
   | ONE
   { Some `One }
   | SOME
   { Some `Some }
   | SET
   { None }

element:
  i = interval  /* necessarily: at least two 1-tuples */
  { Raw.eintvl i }
  | t = tuple    /* one parenthesised tuple of any arity >= 1 is possible */
  { Raw.etuple t }
  | at = atom    /* a single atom without parentheses */
  { Raw.etuple [at] }


tuple:
  ats = parens(atom+)
  { ats }

interval:
  at1 = IDX_ID
  DOTDOT
  at2 = IDX_ID
  {
    Raw.interval (Raw_ident.ident at1 $startpos(at1) $endpos(at1))
      (Raw_ident.ident at2 $startpos(at2) $endpos(at2))
 }

atom:
  at = PLAIN_ID
 | at = IDX_ID
 { Raw_ident.ident at $startpos $endpos }
 | nb = NUMBER
 { Raw_ident.ident (string_of_int nb) $startpos $endpos }




  ////////////////////////////////////////////////////////////////////////
  // instances
  ////////////////////////////////////////////////////////////////////////

insts:
  INST assignments = inst+
  { assignments }

inst:
 id = PLAIN_ID EQ tuples = braces(tuple*) ioption(SEMI)
 { (Raw_ident.ident id $startpos(id) $endpos(id), tuples) }




  ////////////////////////////////////////////////////////////////////////
  // symmetries
  ////////////////////////////////////////////////////////////////////////

 syms:
   SYM sy = bracketed_symmetry+
      { sy }

bracketed_symmetry:
 sy = brackets(symmetry) SEMI?
 {sy}

symmetry:
  syms1 = sym_element+ LTE syms2 = sym_element+
  {syms1, syms2}

sym_element:
  atoms = parens(atom+)
  {List.hd atoms, List.tl atoms}

  ////////////////////////////////////////////////////////////////////////
  // invariant
  ////////////////////////////////////////////////////////////////////////

%inline invariant:
	INVARIANT fs = specification
	{ fs }

specification:
	fs = formula_semi*
  { fs }

  ////////////////////////////////////////////////////////////////////////
  // goal
  ////////////////////////////////////////////////////////////////////////

%inline goal:
	RUN fs = formula_semi+ exp = ioption(expect_field)
{G.run fs exp }

expect_field:
	EXPECT exp_val = expected_value
	{ exp_val }

expected_value:
	SAT { true }
	| UNSAT { false }

formula_semi:
  f = formula ioption(SEMI)
  { f }

formula :
     TRUE
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.true_ }

	| FALSE
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.false_ }

	| qual = rqualify e = expr
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.qual qual e }

	| e1 = expr op = comp_op e2 = expr
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.rcomp e1 op e2 }

	| e1 = iexpr op = icomp_op e2 = iexpr
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.icomp e1 op e2 }

	| op = lunop f = formula
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.lunary op f }

  | f1 = formula op = lbinop f2 = formula
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.lbinary f1 op f2 }

	| q = quant decls = comma_sep1(ae_decl) block = f_block_or_bar
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.quant q decls block }

	| LET decls = comma_sep1(let_decl) block = f_block_or_bar
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.let_ decls block}

	|  f = formula IMPLIES t = formula ELSE e = formula
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.fite f t e }

	|  f = formula IMPLIES t = formula
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.lbinary f G.impl t  }

	| f = f_block
	{ G.fml (Location.from_positions $startpos $endpos)
    @@ G.block f }

	| f = parens(formula)
	    { f }


%inline quant:
	ALL
	{ G.all }
	| SOME
	{ G.some }
	| NO
	{ G.no_ }
	| ONE
	{ G.one }
  | LONE
	{ G.lone }

%inline ae_decl:
	disj = iboption(DISJ) ids = comma_sep1(plain_id) COLON range = expr
	{ (disj, ids, range) }

%inline plain_id:
  id = PLAIN_ID
 	{ Raw_ident.ident id $startpos(id) $endpos(id) }

%inline f_block_or_bar:
 	BAR f = formula
	{ [f] }
	| block = f_block
	{ block }

%inline f_block:
	 fs = braces(specification)
	{  fs }

%inline lbinop:
	AND
	{ G.and_ }
	| OR
	{ G.or_ }
/*	| IMPLIES
	{ G.impl }*/
	| IFF
	{ G.iff }
	| UNTIL
	{ G.until }
	| RELEASES
	{ G.releases }
	| SINCE
	{ G.since }
	| TRIGGERED
	{ G.triggered }

%inline lunop:
	| EVENTUALLY
	{ G.eventually }
	| ALWAYS
	{ G.always }
	| NOT
	{ G.not_ }
	| ONCE
	{ G.once }
	| AFTER
	{ G.next }
	| BEFORE
	{ G.previous }
	| HISTORICALLY
	{ G.historically }


    ////////////////////////////////////////////////////////////////////////
    // RELATIONAL EXPRESSIONS
    ////////////////////////////////////////////////////////////////////////

expr:
  NONE
	{ exp_no_arity (Location.from_positions $startpos $endpos)
    @@ G.none }

	| UNIV
	{ exp_no_arity (Location.from_positions $startpos $endpos)
    @@ G.univ}

	| IDEN
	{ exp_no_arity (Location.from_positions $startpos $endpos)
    @@ G.iden }

	| BIGINT e = brackets(iexpr)
	{ exp_no_arity (Location.from_positions $startpos $endpos)
    @@ G.big_int e }

  | id = PLAIN_ID
	{ exp_no_arity (Location.from_positions $startpos $endpos)
    @@ G.ident @@ Raw_ident.ident id $startpos $endpos}

	| op = runop e = expr
	{ exp_no_arity (Location.from_positions $startpos $endpos)
    @@ G.runary op e }

	| e1 = expr op  = rbinop e2 = expr
	{ exp_no_arity (Location.from_positions $startpos $endpos)
    @@ G.rbinary e1 op e2 }

	| f = formula IMPLIES t = expr ELSE e = expr
	{ exp_no_arity (Location.from_positions $startpos $endpos)
    @@ G.rite f t e}

	| exp = expr args = brackets(comma_sep1(expr))
	{ exp_no_arity (Location.from_positions $startpos $endpos)
    @@ G.boxjoin exp args }

	| compr = braces(compr_body)
	{ exp_no_arity (Location.from_positions $startpos $endpos)
    @@ compr}

	| e = expr PRIME
	{ exp_no_arity (Location.from_positions $startpos $endpos)
    @@ G.prime e}

	| e = parens(expr)
	    { e }



%inline comp_op:
 	NOT_IN
	{ G.not_in}
  | IN
	{ G.in_ }
  | EQ
	{ G.req }
  | NEQ
 	{ G.rneq }

%inline rqualify:
 	ONE
	{ G.rone }
  | LONE
	    { G.rlone }
  | SOME
	    { G.rsome }
  | NO
 	{ G.rno }

%inline runop:
	TILDE
	{ G.transpose }
  | HAT
	    { G.tclos }
  | STAR
	{ G.rtclos }

%inline rbinop:
	PLUS
	{ G.union }
	| INTER
	{ G.inter }
	| OVERRIDE
	{ G.over }
	| LPROJ
	{ G.lproj }
	| RPROJ
	{ G.rproj }
	| ARROW
	{ G.prod }
	| MINUS
	{ G.diff }
	| DOT
	{ G.join }

%inline compr_body:
	decls = comma_sep1(ae_decl) block = f_block_or_bar
	    { G.compr decls block }

%inline let_decl:
	id = PLAIN_ID EQ e = expr
	{ (Raw_ident.ident id $startpos(id) $endpos(id), e) }


    ////////////////////////////////////////////////////////////////////////
    // INTEGER EXPRESSIONS
     ////////////////////////////////////////////////////////////////////////

iexpr:
  n = NUMBER
  { G.iexp (Location.from_positions $startpos $endpos)
    @@ G.num n  }
  | HASH e = expr
  { G.iexp (Location.from_positions $startpos $endpos)
    @@ G.card e  }
| c = formula IIMPLIES t = iexpr IELSE e = iexpr { G.iexp (Location.from_positions $startpos $endpos)
    @@ G.ifthenelse_arith c t e }
  | SMALLINT e = brackets(expr)
	{ G.iexp (Location.from_positions $startpos $endpos)
	@@ G.small_int e }
  | UMINUS e = brackets(iexpr)
  { G.iexp (Location.from_positions $startpos $endpos)
    @@ G.(iunary neg e) }
  | op = arith_op LBRACKET e1 = iexpr COMMA e2 = iexpr RBRACKET
  { G.iexp (Location.from_positions $startpos $endpos)
    @@ G.(ibinary e1 op e2) }

	| e = parens(iexpr)
	        { e }

  | SUM bs = comma_sep1(sum_decl) e = braces(iexpr)
	{ G.iexp (Location.from_positions $startpos $endpos)
	@@ G.sum bs e }

  | SUM bs = comma_sep1(sum_decl) BAR  e = iexpr
	{ G.iexp (Location.from_positions $startpos $endpos)
	@@ G.sum bs e }


%inline sum_decl: 
	id = PLAIN_ID COLON e = expr
	{ (Raw_ident.ident id $startpos(id) $endpos(id), e) }

arith_op:
  | ADD { G.add }
  | SUB { G.sub }
  | MUL { G.mul }
  | DIV { G.div }
  | REM { G.rem }
  | LSHIFT { G.lshift }
  | SERSHIFT { G.sershift }
  | ZERSHIFT { G.zershift }

icomp_op:
  | LT
	{ G.lt}
	| LTE
	{ G.lte }
	| GT
	{ G.gt }
	| GTE
	{ G.gte }
  | EQ
	{ G.ieq }
  | NEQ
 	{ G.ineq }


    ////////////////////////////////////////////////////////////////////////
    // MENHIR MACROS
    ////////////////////////////////////////////////////////////////////////


%public %inline comma_sep1(X) :
  xs = separated_nonempty_list(COMMA, X)
    { xs }



%public %inline braces(X):
  x = delimited(LBRACE, X, RBRACE)
    { x }


%public %inline brackets(X):
  x = delimited(LBRACKET, X, RBRACKET)
    { x }

%public %inline parens(X):
  x = delimited(LPAREN, X, RPAREN)
    { x }


%public %inline iboption(X):
 (* empty *)
 { false }
 | X
 { true }
