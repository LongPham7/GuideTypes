%{
open Ast_types
open Guide_type_utility

let mkloc = Location.mkloc

let make_loc (start_pos, end_pos) = {
  Location.loc_start = start_pos;
  Location.loc_end = end_pos;
  Location.loc_ghost = false;
}

let mksty ~loc sty_desc = {
  sty_desc;
  sty_loc = make_loc loc;
}

let mkbty ~loc bty_desc = {
  bty_desc;
  bty_loc = make_loc loc;
}

let mkexp ~loc exp_desc = {
  exp_desc;
  exp_loc = make_loc loc;
}

let mkcmd ~loc cmd_desc = {
  cmd_desc;
  cmd_loc = make_loc loc;
}
%}

%token AMPERSAND
%token AND
%token ASTERISK
%token BAR
%token BER
%token BETA
%token BIN
%token BOOL
%token CAT
%token COLON
%token DISC
%token DIST
%token DOLLAR
%token DOT
%token ELSE
%token END
%token EOF
%token EQUAL
%token EXTERNAL
%token FALSE
%token <float> FLOATV
%token FN
%token GAMMA
%token GEO
%token GREATER
%token GREATEREQUAL
%token IF
%token IN
%token <int> INTV
%token ITER
%token LBRACE
%token LBRACKET
%token LET
%token LESS
%token LESSGREATER
%token LESSEQUAL
%token LESSMINUS
%token <string> LIDENT
%token LOOP
%token LPAREN
%token MINUS
%token MINUSGREATER
%token MINUSO
%token NAT
%token NORMAL
%token OBSERVE
%token OR
%token PLUS
%token POIS
%token PREAL
%token PROC
%token RBRACE
%token RBRACKET
%token RETURN
%token RPAREN
%token REAL
%token SAME
%token SAMPLE
%token SEMI
%token SIMPLEX
%token SLASH
%token SLASHBACKSLASH
%token STACK
%token TENSOR
%token THEN
%token TRUE
%token TYPE
%token <string> UIDENT
%token UNDERSCORE
%token UNIF
%token UNIT
%token UREAL

%token INITIAL_TYPE
%token GUIDE_COMPOSITION

%token BOOL_U
%token NAT_U
%token PREAL_U
%token REAL_U
%token UNIT_U
%token UREAL_U
%token TENSOR_U
%token SIMPLEX_U

%right OR
%right AND
%left EQUAL LESSGREATER LESS LESSEQUAL GREATER GREATEREQUAL
%left PLUS MINUS
%left ASTERISK SLASH

%start implementation
%type <Ast_types.prog> implementation

%%

%inline mkloc(symb): symb { mkloc $1 (make_loc $sloc) }
%inline mksty(symb): symb { mksty ~loc:$sloc $1 }
%inline mkbty(symb): symb { mkbty ~loc:$sloc $1 }
%inline mkexp(symb): symb { mkexp ~loc:$sloc $1 }
%inline mkcmd(symb): symb { mkcmd ~loc:$sloc $1 }

%public implementation:
  | prog = list(toplevel); EOF
    { prog }

toplevel:
  | TYPE; sty_name = mkloc(UIDENT); EQUAL; sty_body = sess_ty
    { Top_sess (sty_name, Some sty_body) }
  | TYPE; sty_name = mkloc(UIDENT)
    { Top_sess (sty_name, None) }
  | PROC; proc_name = mkloc(UIDENT); proc_sig = proc_sig; EQUAL; proc_body = cmd
    { Top_proc (proc_name, { proc_sig; proc_body; proc_loc = make_loc $sloc }) }
  | EXTERNAL; var_name = mkloc(LIDENT); COLON; ty = base_ty
    { Top_external (var_name, ty) }
  | INITIAL_TYPE; COLON; sty_body = sess_ty
    { Top_initial_type sty_body }
  | GUIDE_COMPOSITION; COLON; list_guides = separated_nonempty_list(SEMI, UIDENT)
    { Top_guide_composition list_guides }

proc_sig:
  | psig_theta_tys = proc_theta; LPAREN; psig_param_tys = separated_list(SEMI, param_ty); RPAREN; MINUSGREATER; psig_ret_ty = base_ty; BAR; psig_sess_left = chtype; BAR; psig_sess_right = chtype
    { { psig_theta_tys; psig_param_tys; psig_ret_ty; psig_sess_left; psig_sess_right } }

proc_theta:
  |
    { [] }
  | LBRACKET; theta_tys = separated_list(SEMI, theta_ty); RBRACKET
    { theta_tys }

theta_ty:
  | var_name = mkloc(LIDENT); COLON; pty = base_ty
    { (var_name, pty) }

param_ty:
  | var_name = mkloc(LIDENT); COLON; bty = base_ty
    { (var_name, bty) }

chtype:
  | DOT
    { None }
  | channel_name = mkloc(LIDENT); COLON; sty_name = mkloc(UIDENT)
    { Some (channel_name, sty_name) }

sess_ty:
  | mksty(
      DOLLAR
      { Sty_one }
    | bty = base_ty; SLASHBACKSLASH; sty = sess_ty
      { Sty_conj (bty, sty) }
    | bty = base_ty; MINUSO; sty = sess_ty
      { Sty_imply (bty, sty) }
    | PLUS; LBRACE; sty1 = sess_ty; BAR; sty2 = sess_ty; RBRACE
      { Sty_ichoice (sty1, sty2) }
    | AMPERSAND; LBRACE; sty1 = sess_ty; BAR; sty2 = sess_ty; RBRACE
      { Sty_echoice (sty1, sty2) }
    | sty_name = mkloc(UIDENT)
      { Sty_var (sty_name, None) }
    | sty_name = mkloc(UIDENT); LBRACKET; sty = sess_ty; RBRACKET
      { Sty_var (sty_name, Some sty) }
    )
    { $1 }

base_ty:
  | bty = base_prod_ty
    { bty }
  | mkbty(
      bty1 = base_prod_ty; MINUSGREATER; bty2 = base_ty
      { Bty_arrow (bty1, bty2) }
    )
    { $1 }

base_prod_ty:
  | bty = base_prim_ty
    { bty }
  | mkbty(
      bty1 = base_prim_ty; ASTERISK; bty2 = base_prod_ty
      { Bty_product (bty1, bty2) }
    )
    { $1 }

base_prim_ty:
  | LPAREN; bty = base_ty; RPAREN
    { bty }
  | mkbty(
      pty = prim_ty
      { Bty_prim pty }
    | pty = prim_ty_uncovered
      { Bty_prim_uncovered pty }
    | bty = base_prim_ty; DIST
      { Bty_dist bty }
    | LPAREN; pty = prim_ty; SEMI; LBRACKET; dims = separated_list(SEMI, INTV); RBRACKET; RPAREN; TENSOR
      { Bty_tensor (pty, dims) }
    | LPAREN; pty = prim_ty; SEMI; LBRACKET; dims = separated_list(SEMI, INTV); RBRACKET; RPAREN; TENSOR_U
      { Bty_tensor_uncovered (pty, dims) }
    | SIMPLEX; LBRACKET; n = INTV; RBRACKET
      { Bty_simplex n }
    | SIMPLEX_U; LBRACKET; n = INTV; RBRACKET
      { Bty_simplex_uncovered n }
    | type_name = mkloc(LIDENT)
      { Bty_external type_name }
    )
    { $1 }

prim_ty:
  | UNIT
    { Pty_unit }
  | BOOL
    { Pty_bool }
  | UREAL
    { Pty_ureal }
  | PREAL
    { Pty_preal }
  | REAL
    { Pty_real }
  | NAT; LBRACKET; n = INTV; RBRACKET
    { Pty_fnat n }
  | NAT
    { Pty_nat }

prim_ty_uncovered:
  | UNIT_U
    { Pty_unit }
  | BOOL_U
    { Pty_bool }
  | UREAL_U
    { Pty_ureal }
  | PREAL_U
    { Pty_preal }
  | REAL_U
    { Pty_real }
  | NAT_U; LBRACKET; n = INTV; RBRACKET
    { Pty_fnat n }
  | NAT_U
    { Pty_nat }

exp:
  | exp = arith_exp
    { exp }
  | mkexp(
      IF; exp0 = exp; THEN; exp1 = exp; ELSE; exp2 = exp
      { E_cond (exp0, exp1, exp2) }
    | FN; LPAREN; var_name = mkloc(LIDENT); COLON; bty = base_ty; RPAREN; MINUSGREATER; exp = exp
      { E_abs (var_name, bty, exp) }
    )
    { $1 }

arith_exp:
  | exp = app_exp
     { exp }
  | mkexp(
      exp1 = arith_exp; bop = mkloc(bop); exp2 = arith_exp
      { E_binop (bop, exp1, exp2) }
    )
    { $1 }

%inline bop:
  | PLUS
    { Bop_add }
  | MINUS
    { Bop_sub }
  | ASTERISK
    { Bop_mul }
  | SLASH
    { Bop_div }
  | EQUAL
    { Bop_eq }
  | LESSGREATER
    { Bop_ne }
  | LESS
    { Bop_lt }
  | LESSEQUAL
    { Bop_le }
  | GREATER
    { Bop_gt }
  | GREATEREQUAL
    { Bop_ge }
  | AND
    { Bop_and }
  | OR
    { Bop_or }

app_exp:
  | exp = prim_exp
    { exp }
  | mkexp(
      rator = app_exp; LPAREN; rand = exp; RPAREN
      { E_app (rator, rand) }
    )
    { $1 }

prim_exp:
  | LPAREN; exp = exp; RPAREN
    { exp }
  | mkexp(
      var_name = mkloc(LIDENT)
      { E_var var_name }
    | LPAREN; RPAREN
      { E_triv }
    | TRUE
      { E_bool true }
    | FALSE
      { E_bool false }
    | n = INTV
      { E_nat n }
    | r = FLOATV
      { E_real r }
    | MINUS; n = INTV
      { E_real (Float.of_int (-n)) }
    | MINUS; r = FLOATV
      { E_real (-. r) }
    | LET; var_name = mkloc(LIDENT); EQUAL; exp1 = exp; IN; exp2 = exp; END
      { E_let (exp1, var_name, exp2) }
    | dist = dist(exp)
      { E_dist dist }
    | SAME; LPAREN; bty = base_prim_ty; RPAREN
      { E_dist (D_same (eval_ty bty)) }
    | TENSOR; LPAREN; exp0 = exp; RPAREN
      { E_tensor exp0 }
    | STACK; LPAREN; exps = separated_nonempty_list(SEMI, exp); RPAREN
      { E_stack exps }
    | base_exp = prim_exp; LBRACKET; index_exps = separated_list(SEMI, exp); RBRACKET
      { E_index (base_exp, index_exps) }
    | LPAREN; exp1 = exp; SEMI; exp2 = exp; RPAREN
      { E_pair (exp1, exp2) }
    | exp = prim_exp; DOT; field = INTV
      { E_field (exp, field) }
    )
    { $1 }

dist(RHS):
  | BER; LPAREN; arg = RHS; RPAREN
    { D_ber arg }
  | UNIF
    { D_unif }
  | BETA; LPAREN; arg1 = RHS; SEMI; arg2 = RHS; RPAREN
    { D_beta (arg1, arg2) }
  | GAMMA; LPAREN; arg1 = RHS; SEMI; arg2 = RHS; RPAREN
    { D_gamma (arg1, arg2) }
  | NORMAL; LPAREN; arg1 = RHS; SEMI; arg2 = RHS; RPAREN
    { D_normal (arg1, arg2) }
  | CAT; LPAREN; args = separated_nonempty_list(SEMI, RHS); RPAREN
    { D_cat args }
  | DISC; LPAREN; arg = RHS; RPAREN
    { D_discrete arg }
  | BIN; LPAREN; n = INTV; SEMI; arg = RHS; RPAREN
    { D_bin (n, arg) }
  | GEO; LPAREN; arg = RHS; RPAREN
    { D_geo arg }
  | POIS; LPAREN; arg = RHS; RPAREN
    { D_pois arg }

cmd:
  | LBRACE; cmd = cmd; RBRACE
    { cmd }
  | mkcmd(
      RETURN; exp = exp
      { M_ret exp }
    | var_name = mkloc(LIDENT); LESSMINUS; cmd1 = cmd; SEMI; cmd2 = cmd
      { M_bnd (cmd1, Some var_name, cmd2) }
    | UNDERSCORE; LESSMINUS; cmd1 = cmd; SEMI; cmd2 = cmd
      { M_bnd (cmd1, None, cmd2) }
    | proc_name = mkloc(UIDENT); LPAREN; exps = separated_list(SEMI, exp); RPAREN
      { M_call (proc_name, exps) }
    | SAMPLE; LBRACE; channel_name = mkloc(LIDENT); RBRACE; LPAREN; exp = exp; RPAREN
      { M_sample_send (exp, channel_name) }
    | OBSERVE; LBRACE; channel_name = mkloc(LIDENT); RBRACE; LPAREN; exp = exp; RPAREN
      { M_sample_recv (exp, channel_name) }
    | IF; LBRACE; channel_name = mkloc(LIDENT); RBRACE; exp = exp; THEN; cmd1 = cmd; ELSE; cmd2 = cmd
      { M_branch_send (exp, cmd1, cmd2, channel_name) }
    | IF; LBRACE; channel_name = mkloc(LIDENT); RBRACE; DOT; THEN; cmd1 = cmd; ELSE; cmd2 = cmd
      { M_branch_recv (cmd1, cmd2, channel_name) }
    | IF; exp = exp; THEN; cmd1 = cmd; ELSE; cmd2 = cmd
      { M_branch_self (exp, cmd1, cmd2) }
    | LOOP; LBRACKET; n = INTV; SEMI; init_exp = exp; RBRACKET; LPAREN; FN; LPAREN; bind_name = mkloc(LIDENT); COLON; ty = base_ty; RPAREN; MINUSGREATER; cmd0 = cmd; RPAREN
      { M_loop (n, init_exp, bind_name, ty, cmd0) }
    | ITER; LBRACKET; iter_exp = exp; SEMI; init_exp = exp; RBRACKET; LPAREN; FN; iter_name = mkloc(LIDENT); LPAREN; bind_name = mkloc(LIDENT); COLON; ty = base_ty; RPAREN; MINUSGREATER; cmd0 = cmd; RPAREN
      { M_iter (iter_exp, init_exp, iter_name, bind_name, ty, cmd0) }
    )
    { $1 }
