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
  | Btyv_prim_uncovered pty -> Format.fprintf fmt "%a_u" print_prim_ty pty
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

let print_sess_type_context fmt context =
  let print_type_name_definition ~key:type_name ~data:type_definition =
    match type_definition with
    | None ->
        Format.fprintf fmt "(Type name, definition) = (%s, None)\n" type_name
    | Some definition ->
        Format.fprintf fmt "(Type name, definition) = (%s, %a)\n" type_name
          print_sess_tyv definition
  in
  let num_entries = Hashtbl.length context in
  Format.fprintf fmt "Typing context has %i entries:\n" num_entries;
  Hashtbl.iteri context ~f:print_type_name_definition;
  Format.pp_print_newline fmt ()

let print_proc_sig fmt signature =
  let {
    psigv_theta_tys;
    psigv_param_tys;
    psigv_ret_ty;
    psigv_sess_left;
    psigv_sess_right;
  } =
    signature
  in
  let print_channel_type_name fmt channel_and_type =
    match channel_and_type with
    | None -> Format.fprintf fmt "None "
    | Some (channel_name, type_name) ->
        Format.fprintf fmt "channel name = %s, type name = %s " channel_name
          type_name
  in
  Format.pp_print_string fmt "Theta types: ";
  List.iter psigv_theta_tys ~f:(fun (s, _) -> Format.fprintf fmt "type = %s " s);
  Format.pp_print_newline fmt ();
  Format.pp_print_string fmt "Param types: ";
  List.iter psigv_param_tys ~f:(fun (s, _) -> Format.fprintf fmt "type = %s " s);
  Format.pp_print_newline fmt ();
  Format.fprintf fmt "Return type: %a\n" print_base_tyv psigv_ret_ty;
  Format.fprintf fmt "Left session types: %a\n" print_channel_type_name
    psigv_sess_left;
  Format.fprintf fmt "Right session types: %a\n" print_channel_type_name
    psigv_sess_right

let print_proc_signature_context fmt context =
  let print_mapping ~key ~data =
    Format.fprintf fmt "Process name = %s\n" key;
    print_proc_sig fmt data
  in
  String.Map.iteri context ~f:print_mapping;
  Format.pp_print_newline fmt ()

let rec equal_base_tyv_modulo_coverage btyv1 btyv2 =
  match (btyv1, btyv2) with
  | Btyv_prim pty1, Btyv_prim pty2 -> equal_prim_ty pty1 pty2
  | Btyv_prim_uncovered pty1, Btyv_prim pty2 -> equal_prim_ty pty1 pty2
  | Btyv_prim pty1, Btyv_prim_uncovered pty2 -> equal_prim_ty pty1 pty2
  | Btyv_prim_uncovered pty1, Btyv_prim_uncovered pty2 ->
      equal_prim_ty pty1 pty2
  | Btyv_dist bty1, Btyv_dist bty2 -> equal_base_tyv_modulo_coverage bty1 bty2
  | _, _ ->
      let () =
        print_endline
          "We don't support this feature yet in base-type equality modulo \
           coverage"
      in
      equal_base_tyv btyv1 btyv2

let rec join_base_tyv_modulo_coverage btyv1 btyv2 =
  assert (equal_base_tyv_modulo_coverage btyv1 btyv2);
  match (btyv1, btyv2) with
  | Btyv_prim pty1, Btyv_prim _ -> Btyv_prim pty1
  | Btyv_prim_uncovered pty1, Btyv_prim _ -> Btyv_prim_uncovered pty1
  | Btyv_prim pty1, Btyv_prim_uncovered _ -> Btyv_prim_uncovered pty1
  | Btyv_prim_uncovered pty1, Btyv_prim_uncovered _ -> Btyv_prim_uncovered pty1
  | Btyv_dist bty1, Btyv_dist bty2 ->
      Btyv_dist (join_base_tyv_modulo_coverage bty1 bty2)
  | _, _ ->
      let () =
        print_endline
          "We don't support this feature yet in base-type join modulo coverage"
      in
      btyv1
