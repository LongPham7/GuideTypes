val print_sess_tyv : Format.formatter -> Ast_types.sess_tyv -> unit

val print_sess_type_context :
  Format.formatter -> (string, Ast_types.sess_tyv option) Core.Hashtbl.t -> unit

val print_proc_sig : Format.formatter -> Ast_types.proc_sigv -> unit

val print_proc_signature_context :
  Format.formatter -> Ast_types.proc_sigv Core.String.Map.t -> unit
