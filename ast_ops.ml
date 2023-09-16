open Ast_types
open Core

let print_prim_ty fmt = function
  | Pty_unit -> Format.fprintf fmt "unit"
  | Pty_bool -> Format.fprintf fmt "bool"
  | Pty_ureal -> Format.fprintf fmt "ureal"
  | Pty_preal -> Format.fprintf fmt "preal"
  | Pty_real -> Format.fprintf fmt "real"
  | Pty_fnat n -> Format.fprintf fmt "nat[%d]" n
  | Pty_nat -> Format.fprintf fmt "nat"

let rec print_base_tyv fmt = function
  | Btyv_arrow (tyv1, tyv2) ->
      Format.fprintf fmt "%a -> %a" print_base_tyv_prod tyv1 print_base_tyv tyv2
  | tyv -> print_base_tyv_prod fmt tyv

and print_base_tyv_prod fmt = function
  | Btyv_product (tyv1, tyv2) ->
      Format.fprintf fmt "%a * %a" print_base_tyv_prim tyv1 print_base_tyv_prod
        tyv2
  | tyv -> print_base_tyv_prim fmt tyv

and print_base_tyv_prim fmt = function
  | Btyv_prim pty -> print_prim_ty fmt pty
  | Btyv_dist tyv -> Format.fprintf fmt "%a dist" print_base_tyv_prim tyv
  | Btyv_tensor (pty, dims) ->
      Format.fprintf fmt "(%a; [%a]) tensor" print_prim_ty pty
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
           (fun fmt n -> Format.fprintf fmt "%d" n))
        dims
  | Btyv_simplex n -> Format.fprintf fmt "simplex[%d]" n
  | Btyv_external name -> Format.fprintf fmt "%s" name
  | tyv -> Format.fprintf fmt "(%a)" print_base_tyv tyv

let rec print_sess_tyv fmt = function
  | Styv_one -> Format.fprintf fmt "$"
  | Styv_conj (tyv1, styv2) ->
      Format.fprintf fmt "%a /\\ %a" print_base_tyv tyv1 print_sess_tyv styv2
  | Styv_imply (tyv1, styv2) ->
      Format.fprintf fmt "%a -o %a" print_base_tyv tyv1 print_sess_tyv styv2
  | Styv_ichoice (styv1, styv2) ->
      Format.fprintf fmt "+{ %a | %a }" print_sess_tyv styv1 print_sess_tyv
        styv2
  | Styv_echoice (styv1, styv2) ->
      Format.fprintf fmt "&{ %a | %a }" print_sess_tyv styv1 print_sess_tyv
        styv2
  | Styv_var (type_name, styv0) ->
      Format.fprintf fmt "%s[%a]" type_name print_sess_tyv styv0

let print_session_type_context context =
  let print_type_name_definition ~key:type_name ~data:type_definition =
    match type_definition with
    | None -> Format.printf "(Type name, definition) = (%s, None) " type_name
    | Some definition ->
        let () = print_sess_tyv Format.str_formatter definition in
        let definition_string = Format.flush_str_formatter () in
        Format.printf "(Type name, definition) = (%s, %s) " type_name
          definition_string
  in
  let num_entries = Hashtbl.length context in
  Format.printf "Typing context has %i entries: " num_entries;
  Hashtbl.iteri context ~f:print_type_name_definition;
  Core.Out_channel.newline stdout

let print_proc_sig signature =
  let {
    psigv_theta_tys;
    psigv_param_tys;
    psigv_ret_ty;
    psigv_sess_left;
    psigv_sess_right;
  } =
    signature
  in
  let print_channel_type_name channel_and_type =
    match channel_and_type with
    | None -> printf "None "
    | Some (channel_name, type_name) ->
        printf "channel name = %s, type name = %s " channel_name type_name
  in
  print_string "Theta types: ";
  List.iter psigv_theta_tys ~f:(fun (s, _) -> printf "type = %s " s);
  Core.Out_channel.newline stdout;
  print_string "Param types: ";
  List.iter psigv_param_tys ~f:(fun (s, _) -> printf "type = %s " s);
  Core.Out_channel.newline stdout;
  print_string "Return type: ";
  print_base_tyv Format.std_formatter psigv_ret_ty;
  Core.Out_channel.newline stdout;
  print_string "Left session types: ";
  print_channel_type_name psigv_sess_left;
  Core.Out_channel.newline stdout;
  print_string "Right session types: ";
  print_channel_type_name psigv_sess_right;
  Core.Out_channel.newline stdout

let print_proc_signature_context context =
  let print_mapping ~key ~data =
    printf "Process name = %s\n" key;
    print_proc_sig data
  in
  String.Map.iteri context ~f:print_mapping;
  Core.Out_channel.newline stdout
