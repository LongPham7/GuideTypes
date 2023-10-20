open Core

val tycheck_exp :
  (string, Ast_types.base_tyv, 'a) Map.t ->
  Ast_types.exp ->
  Ast_types.base_tyv Core.Or_error.t

val tycheck_prog : Ast_types.prog -> unit Core.Or_error.t
