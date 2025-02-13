{
open Core
open Lexing
open Parser

type error =
  | Illegal_character of char
  | Invalid_literal of string

exception Lexer_error of error * Location.t

(* The table of keywords *)

let keyword_table = Hashtbl.of_alist_exn (module String) [
  ("and", AND);
  ("bool", BOOL);
  ("dist", DIST);
  ("else", ELSE);
  ("end", END);
  ("external", EXTERNAL);
  ("false", FALSE);
  ("fn", FN);
  ("if", IF);
  ("in", IN);
  ("iter", ITER);
  ("let", LET);
  ("loop", LOOP);
  ("nat", NAT);
  ("observe", OBSERVE);
  ("or", OR);
  ("preal", PREAL);
  ("proc", PROC);
  ("return", RETURN);
  ("real", REAL);
  ("sample", SAMPLE);
  ("simplex", SIMPLEX);
  ("stack", STACK);
  ("tensor", TENSOR);
  ("then", THEN);
  ("true", TRUE);
  ("type", TYPE);
  ("unit", UNIT);
  ("ureal", UREAL);

  ("bool_u", BOOL_U);
  ("nat_u", NAT_U);
  ("preal_u", PREAL_U);
  ("real_u", REAL_U);
  ("unit_u", UNIT_U);
  ("ureal_u", UREAL_U);
  ("tensor_u", TENSOR_U);
  ("simplex_u", SIMPLEX_U);

  ("Initial_type", INITIAL_TYPE);
  ("Guide_composition", GUIDE_COMPOSITION);

  ("&", AMPERSAND);
  ("*", ASTERISK);
  ("|", BAR);
  (":", COLON);
  ("$", DOLLAR);
  (".", DOT);
  ("=", EQUAL);
  (">", GREATER);
  (">=", GREATEREQUAL);
  ("{", LBRACE);
  ("[", LBRACKET);
  ("<", LESS);
  ("<>", LESSGREATER);
  ("<=", LESSEQUAL);
  ("<-", LESSMINUS);
  ("(", LPAREN);
  ("-", MINUS);
  ("->", MINUSGREATER);
  ("-o", MINUSO);
  ("+", PLUS);
  ("}", RBRACE);
  ("]", RBRACKET);
  (")", RPAREN);
  (";", SEMI);
  ("/", SLASH);
  ("/\\", SLASHBACKSLASH);
  ("_", UNDERSCORE);

  ("BER", BER);
  ("BETA", BETA);
  ("BIN", BIN);
  ("CAT", CAT);
  ("DISC", DISC);
  ("GAMMA", GAMMA);
  ("GEO", GEO);
  ("NORMAL", NORMAL);
  ("POIS", POIS);
  ("UNIF", UNIF);
  ("SAME", SAME);
]

(* Update the current location with file name and line number. *)

let update_loc lexbuf file line absolute chars =
  let pos = lexbuf.lex_curr_p in
  let new_file = match file with
                 | None -> pos.pos_fname
                 | Some s -> s
  in
  lexbuf.lex_curr_p <- { pos with
    pos_fname = new_file;
    pos_lnum = if absolute then line else pos.pos_lnum + line;
    pos_bol = pos.pos_cnum - chars;
  }

(* Error report *)

let error lexbuf e = raise (Lexer_error (e, Location.curr lexbuf))

let prepare_error loc = function
  | Illegal_character c ->
    Location.errorf ~loc "illegal character (%s)" (Char.escaped c)
  | Invalid_literal s ->
    Location.errorf ~loc "invalid literal %s" s

let () =
  Location.register_error_of_exn
    (function
      | Lexer_error (err, loc) -> Some (prepare_error loc err)
      | _ -> None
    )
}

let newline = ('\013'* '\010')
let blank = [' ' '\009' '\012']
let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']

let decimal_literal = ['0'-'9'] ['0'-'9' '_']*
let hex_digit = ['0'-'9' 'A'-'F' 'a'-'f']
let hex_literal = '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']['0'-'9' 'A'-'F' 'a'-'f' '_']*
let oct_literal = '0' ['o' 'O'] ['0'-'7'] ['0'-'7' '_']*
let bin_literal = '0' ['b' 'B'] ['0'-'1'] ['0'-'1' '_']*
let int_literal = decimal_literal | hex_literal | oct_literal | bin_literal
let float_literal =
  ['0'-'9'] ['0'-'9' '_']*
  ('.' ['0'-'9' '_']* )?
  (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']* )?
let hex_float_literal =
  '0' ['x' 'X']
  ['0'-'9' 'A'-'F' 'a'-'f'] ['0'-'9' 'A'-'F' 'a'-'f' '_']*
  ('.' ['0'-'9' 'A'-'F' 'a'-'f' '_']* )?
  (['p' 'P'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']* )?

rule token = parse
  | newline
    { update_loc lexbuf None 1 false 0; token lexbuf }
  | blank+
    { token lexbuf }
  | "_"
    { Hashtbl.find_exn keyword_table (lexeme lexbuf) }
  | lowercase identchar* as name
    { match Hashtbl.find keyword_table name with
      | Some kwd -> kwd
      | None -> LIDENT name }
  | uppercase identchar* as name
    { match Hashtbl.find keyword_table name with
      | Some kwd -> kwd
      | None -> UIDENT name }
  | int_literal as lit
    { INTV (Int.of_string lit) }
  | (float_literal | hex_float_literal) as lit
    { FLOATV (Float.of_string lit) }
  | (float_literal | hex_float_literal | int_literal) identchar+ as invalid
    { error lexbuf (Invalid_literal invalid) }
  | "#"
    { comment lexbuf }
  | ">=" | "<>" | "<=" | "<-" | "->" | "-o" | "/\\"
    { Hashtbl.find_exn keyword_table (lexeme lexbuf) }
  | ['&' '*' '|' ':' '$' '.' '=' '>' '{' '[' '<' '(' '-' '+' '}' ']' ')' ';' '/']
    { Hashtbl.find_exn keyword_table (lexeme lexbuf) }
  | eof
    { EOF }
  | _ as illegal_char
    { error lexbuf (Illegal_character illegal_char) }

and comment = parse
  | newline
    { update_loc lexbuf None 1 false 0; token lexbuf }
  | _
    { comment lexbuf }
