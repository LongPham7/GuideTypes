open Core
open Ast_types

(* Extract a list of type definitions from a program *)

let collect_type_definitions prog =
  List.filter_map prog ~f:(fun top ->
      match top with
      | Top_proc _ -> None
      | Top_sess (type_name, sty) -> (
          match sty with
          | Some x -> Some (type_name.txt, Typecheck_common.eval_sty x)
          | None -> None)
      | Top_external _ -> None)

(* Print a list of type definitions *)

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

(* Substitute a type into every occurrence of $ in a guide type *)

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
