open Core
open Ast_types
(* open Or_error.Let_syntax *)

let collect_type_definitions prog =
  List.filter_map prog ~f:(fun top ->
      match top with
      | Top_proc _ -> None
      | Top_sess (type_name, sty) -> (
          match sty with
          | Some x -> Some (type_name.txt, Typecheck.eval_sty x)
          | None -> None)
      | Top_external _ -> None)

module TypeNameSet = Set.Make (String)

let rec extract_type_names type_definition =
  match type_definition with
  | Styv_one -> TypeNameSet.empty
  | Styv_conj (_, s) -> extract_type_names s
  | Styv_imply (_, s) -> extract_type_names s
  | Styv_ichoice (s1, s2) ->
      TypeNameSet.union (extract_type_names s1) (extract_type_names s2)
  | Styv_echoice (s1, s2) ->
      TypeNameSet.union (extract_type_names s1) (extract_type_names s2)
  | Styv_var (name, s) -> TypeNameSet.add (extract_type_names s) name

let all_names_defined list_definitions =
  let defined_type_names =
    TypeNameSet.of_list (List.map list_definitions ~f:(fun (name, _) -> name))
  in
  let list_mentioned_type_names =
    List.map list_definitions ~f:(fun (_, definition) ->
        extract_type_names definition)
  in
  let mentioned_type_names =
    List.fold list_mentioned_type_names ~init:TypeNameSet.empty ~f:(fun acc x ->
        TypeNameSet.union acc x)
  in
  if TypeNameSet.is_subset mentioned_type_names ~of_:defined_type_names then
    true
  else false

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

let detect_cycle acc definition1 definition2 =
  let type_pair_matched (s, t) =
    equal_sess_tyv s definition1 && equal_sess_tyv t definition2
  in
  List.exists acc ~f:type_pair_matched

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

let expand_type_name list_type_definitions (name, continuation) =
  let type_definition =
    List.Assoc.find_exn list_type_definitions
      ~equal:(fun x y -> String.equal x y)
      name
  in
  substitute_into_type_definition type_definition continuation

let regular_type_equality list_type_definitions definition1 definition2 =
  let rec recursively_check_equality acc definition1 definition2 =
    if detect_cycle acc definition1 definition2 then true
    else
      let acc_updated = (definition1, definition2) :: acc in
      match (definition1, definition2) with
      | Styv_one, Styv_one -> true
      | Styv_conj (b1, s), Styv_conj (b2, t) ->
          if equal_base_tyv b1 b2 then
            recursively_check_equality acc_updated s t
          else false
      | Styv_imply (b1, s), Styv_imply (b2, t) ->
          if equal_base_tyv b1 b2 then
            recursively_check_equality acc_updated s t
          else false
      | Styv_ichoice (s1, s2), Styv_ichoice (t1, t2) ->
          recursively_check_equality acc_updated s1 t1
          && recursively_check_equality acc_updated s2 t2
      | Styv_echoice (s1, s2), Styv_echoice (t1, t2) ->
          recursively_check_equality acc_updated s1 t1
          && recursively_check_equality acc_updated s2 t2
      | Styv_var (name, s), _ ->
          let definition1_expanded =
            expand_type_name list_type_definitions (name, s)
          in
          recursively_check_equality acc definition1_expanded definition2
      | _, Styv_var (name, s) ->
          let definition2_expanded =
            expand_type_name list_type_definitions (name, s)
          in
          recursively_check_equality acc definition1 definition2_expanded
      | _ -> false
  in
  recursively_check_equality [] definition1 definition2

let type_equality_check prog first_type_name second_type_name =
  let list_type_definitions = collect_type_definitions prog in
  (* For debugging *)
  let () =
    if all_names_defined list_type_definitions then
      print_endline "All mentioned type names are defined"
    else print_endline "Some type names are mentioned but undefined"
  in
  let () =
    print_list_type_definitions Format.std_formatter list_type_definitions
  in
  let first_type_definition =
    List.Assoc.find_exn list_type_definitions ~equal:String.equal
      first_type_name
  in
  let second_type_definition =
    List.Assoc.find_exn list_type_definitions ~equal:String.equal
      second_type_name
  in
  let equality_result =
    regular_type_equality list_type_definitions first_type_definition
      second_type_definition
  in
  let () =
    match equality_result with
    | false -> print_endline "The result is false"
    | true -> print_endline "The result is true"
  in
  Ok ()
