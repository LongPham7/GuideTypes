open Core
open Ast_types

(* Utility functions for manipulating guide types *)

let rec eval_ty ty =
  match ty.bty_desc with
  | Bty_prim pty -> Btyv_prim pty
  | Bty_prim_uncovered pty -> Btyv_prim_uncovered pty
  | Bty_arrow (ty1, ty2) -> Btyv_arrow (eval_ty ty1, eval_ty ty2)
  | Bty_dist ty0 -> Btyv_dist (eval_ty ty0)
  | Bty_tensor (pty, dims) -> Btyv_tensor (pty, dims)
  | Bty_tensor_uncovered (pty, dims) -> Btyv_tensor_uncovered (pty, dims)
  | Bty_simplex n -> Btyv_simplex n
  | Bty_simplex_uncovered n -> Btyv_simplex_uncovered n
  | Bty_external type_name -> Btyv_external type_name.txt
  | Bty_product (ty1, ty2) -> Btyv_product (eval_ty ty1, eval_ty ty2)

let rec eval_sty sty =
  match sty.sty_desc with
  | Sty_one -> Styv_one
  | Sty_conj (ty1, sty2) -> Styv_conj (eval_ty ty1, eval_sty sty2)
  | Sty_imply (ty1, sty2) -> Styv_imply (eval_ty ty1, eval_sty sty2)
  | Sty_ichoice (sty1, sty2) -> Styv_ichoice (eval_sty sty1, eval_sty sty2)
  | Sty_echoice (sty1, sty2) -> Styv_echoice (eval_sty sty1, eval_sty sty2)
  | Sty_var (type_name, None) -> Styv_var (type_name.txt, Styv_one)
  | Sty_var (type_name, Some sty0) -> Styv_var (type_name.txt, eval_sty sty0)

let print_list_type_definitions fmt list_definitions =
  let print_type_name_definition fmt type_name type_definition =
    Format.fprintf fmt "(Type name, definition) = (%s, %a)\n" type_name
      Ast_ops.print_sess_tyv type_definition
  in
  let num_entries = List.length list_definitions in
  Format.fprintf fmt "The file has %i type definitions:\n" num_entries;
  List.iter list_definitions ~f:(fun (type_name, type_definition) ->
      print_type_name_definition fmt type_name type_definition);
  Format.pp_print_newline fmt ()

let rec substitute_into_type_definition target substituted_type =
  match target with
  | Styv_one -> substituted_type
  | Styv_conj (b, s) ->
      let substitution_result =
        substitute_into_type_definition s substituted_type
      in
      Styv_conj (b, substitution_result)
  | Styv_imply (b, s) ->
      let substitution_result =
        substitute_into_type_definition s substituted_type
      in
      Styv_conj (b, substitution_result)
  | Styv_ichoice (s1, s2) ->
      let substitution_result1 =
        substitute_into_type_definition s1 substituted_type
      in
      let substitution_result2 =
        substitute_into_type_definition s2 substituted_type
      in
      Styv_ichoice (substitution_result1, substitution_result2)
  | Styv_echoice (s1, s2) ->
      let substitution_result1 =
        substitute_into_type_definition s1 substituted_type
      in
      let substitution_result2 =
        substitute_into_type_definition s2 substituted_type
      in
      Styv_echoice (substitution_result1, substitution_result2)
  | Styv_var (name, continuation) ->
      let substitution_result =
        substitute_into_type_definition continuation substituted_type
      in
      Styv_var (name, substitution_result)

let get_covered_and_uncovered_distribution_base_types ?(only_dist = true) btyv =
  match btyv with
  | Btyv_prim x -> (true, Btyv_prim x, Btyv_prim_uncovered x)
  | Btyv_prim_uncovered x -> (false, Btyv_prim x, Btyv_prim_uncovered x)
  | Btyv_tensor (pty, dims) ->
      (true, Btyv_tensor (pty, dims), Btyv_tensor_uncovered (pty, dims))
  | Btyv_tensor_uncovered (pty, dims) ->
      (false, Btyv_tensor (pty, dims), Btyv_tensor_uncovered (pty, dims))
  | Btyv_simplex n -> (true, Btyv_simplex n, Btyv_simplex_uncovered n)
  | Btyv_simplex_uncovered n -> (false, Btyv_simplex n, Btyv_simplex_uncovered n)
  | _ ->
      if only_dist then
        failwith
          (Format.asprintf "The base type %a of a distribution is not supported"
             Ast_ops.print_base_tyv btyv)
      else (true, btyv, btyv)

(* Utility functions for processes *)

let eval_proc_sig psig =
  {
    psigv_theta_tys =
      List.map psig.psig_theta_tys ~f:(fun (var_name, pty) ->
          (var_name.txt, eval_ty pty));
    psigv_param_tys =
      List.map psig.psig_param_tys ~f:(fun (var_name, ty) ->
          (var_name.txt, eval_ty ty));
    psigv_ret_ty = eval_ty psig.psig_ret_ty;
    psigv_sess_left =
      Option.map psig.psig_sess_left ~f:(fun (channel_name, type_name) ->
          (channel_name.txt, type_name.txt));
    psigv_sess_right =
      Option.map psig.psig_sess_right ~f:(fun (channel_name, type_name) ->
          (channel_name.txt, type_name.txt));
  }

let extract_context_of_process ext_ctxt proc =
  let psigv = eval_proc_sig proc.proc_sig in
  let ctxt =
    String.Map.of_alist_or_error
      (List.concat
         [
           ext_ctxt;
           List.map psigv.psigv_theta_tys ~f:(fun (var_name, pty) ->
               (var_name, pty));
           psigv.psigv_param_tys;
         ])
  in
  match ctxt with
  | Ok context -> context
  | _ -> failwith "We fail to extract a context"

let collect_externals prog =
  List.filter_map prog ~f:(fun top ->
      match top with
      | Top_sess _ -> None
      | Top_proc _ -> None
      | Top_external (var_name, ty) -> Some (var_name.txt, eval_ty ty)
      | Top_initial_type _ -> None
      | Top_guide_composition _ -> None)

let get_right_channel_name proc =
  let psigv = eval_proc_sig proc.proc_sig in
  match psigv.psigv_sess_right with
  | None -> failwith "The given process does not have a right channel"
  | Some (channel_name, _) -> channel_name

(* Utility functions for extracting information from programs *)

let collect_proc_sigs prog =
  String.Map.of_alist_or_error
    (List.filter_map prog ~f:(fun top ->
         match top with
         | Top_sess _ -> None
         | Top_proc (proc_name, { proc_sig; _ }) ->
             Some (proc_name.txt, eval_proc_sig proc_sig)
         | Top_external _ -> None
         | Top_initial_type _ -> None
         | Top_guide_composition _ -> None))

let collect_type_definitions prog =
  List.filter_map prog ~f:(fun top ->
      match top with
      | Top_proc _ -> None
      | Top_sess (type_name, sty) -> (
          match sty with
          | Some x -> Some (type_name.txt, eval_sty x)
          | None -> None)
      | Top_external _ -> None
      | Top_initial_type _ -> None
      | Top_guide_composition _ -> None)

let collect_function_definitions prog =
  List.filter_map prog ~f:(fun top ->
      match top with
      | Top_proc (f_id, process) -> Some (f_id.txt, process)
      | Top_sess _ -> None
      | Top_external _ -> None
      | Top_initial_type _ -> None
      | Top_guide_composition _ -> None)

let collect_initial_uncovered_type prog =
  let list_init_types =
    List.filter_map prog ~f:(fun top ->
        match top with Top_initial_type x -> Some x | _ -> None)
  in
  match list_init_types with
  | [] -> failwith "No initial uncovered type is given"
  | [ x ] -> x
  | _ -> failwith "Multiple initial uncovered types are given"

let collect_guide_composition prog =
  let list_guide_compositions =
    List.filter_map prog ~f:(fun top ->
        match top with Top_guide_composition x -> Some x | _ -> None)
  in
  match list_guide_compositions with
  | [] -> failwith "No sequential composition of guides is given"
  | [ x ] -> x
  | _ -> failwith "Multiple sequential compositions of guides are given"
