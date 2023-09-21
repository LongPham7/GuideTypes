open Core
open Ast_types

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

(* Make sure that we do not have multple definitions for the same type name *)

let detect_duplicated_definitions list_definitions =
  let contains_duplicated_definitions =
    List.contains_dup list_definitions ~compare:(fun (name1, _) (name2, _) ->
        String.compare name1 name2)
  in
  if contains_duplicated_definitions then
    failwith "We have multiple definitions for the same type name"
  else list_definitions

(* Check that all type names mentioned inside type definitions are actually
   defined *)

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

let check_all_names_defined list_definitions =
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
    list_definitions
  else failwith "Some type names are mentioned but undefined"

(* Eliminate type names defined as $. Such type names are redundant and can be
   eliminated. *)

let rec eliminate_redundant_type_names redundant_type_names definition =
  match definition with
  | Styv_one -> Styv_one
  | Styv_conj (b, s) ->
      let s_updated = eliminate_redundant_type_names redundant_type_names s in
      Styv_conj (b, s_updated)
  | Styv_imply (b, s) ->
      let s_updated = eliminate_redundant_type_names redundant_type_names s in
      Styv_imply (b, s_updated)
  | Styv_ichoice (s1, s2) ->
      let s1_updated = eliminate_redundant_type_names redundant_type_names s1 in
      let s2_updated = eliminate_redundant_type_names redundant_type_names s2 in
      Styv_ichoice (s1_updated, s2_updated)
  | Styv_echoice (s1, s2) ->
      let s1_updated = eliminate_redundant_type_names redundant_type_names s1 in
      let s2_updated = eliminate_redundant_type_names redundant_type_names s2 in
      Styv_echoice (s1_updated, s2_updated)
  | Styv_var (name, continuation) ->
      let name_is_edundant =
        List.exists redundant_type_names ~f:(fun redundant_name ->
            String.equal redundant_name name)
      in
      if name_is_edundant then
        eliminate_redundant_type_names redundant_type_names continuation
      else
        let continuation_updated =
          eliminate_redundant_type_names redundant_type_names continuation
        in
        Styv_var (name, continuation_updated)

let eliminate_redundant_type_names_from_all_definitions list_definitions =
  let is_termination definition =
    match definition with Styv_one -> true | _ -> false
  in
  let redundant_type_names =
    List.filter_map list_definitions ~f:(fun (name, definition) ->
        if is_termination definition then Some name else None)
  in
  let remaining_definitions =
    List.filter list_definitions ~f:(fun (_, definition) ->
        not (is_termination definition))
  in
  List.map remaining_definitions ~f:(fun (name, definition) ->
      (name, eliminate_redundant_type_names redundant_type_names definition))

(* Elimiante type names whose definitions are also type names. We also check if
   there is any circular definition of type names. *)

let substitute_equivalent_type_names_into_pair (name1, name2) (target1, target2)
    =
  if String.equal target2 name1 then (target1, name2) else (target1, target2)

let normalize_list_equivalent_type_names list_pairs =
  let rec normalize_with_acc acc remaining_pairs =
    match remaining_pairs with
    | [] -> acc
    | hd_pair :: tl_pairs ->
        let acc_substituted =
          List.map acc ~f:(substitute_equivalent_type_names_into_pair hd_pair)
        in
        let tl_pairs_substituted =
          List.map tl_pairs
            ~f:(substitute_equivalent_type_names_into_pair hd_pair)
        in
        normalize_with_acc (hd_pair :: acc_substituted) tl_pairs_substituted
  in
  normalize_with_acc [] list_pairs

let rec substitute_equivalent_type_names_into_definition list_equivalent_names
    definition =
  match definition with
  | Styv_one -> Styv_one
  | Styv_conj (b, s) ->
      let s_substituted =
        substitute_equivalent_type_names_into_definition list_equivalent_names s
      in
      Styv_conj (b, s_substituted)
  | Styv_imply (b, s) ->
      let s_substituted =
        substitute_equivalent_type_names_into_definition list_equivalent_names s
      in
      Styv_imply (b, s_substituted)
  | Styv_ichoice (s1, s2) ->
      let s1_substituted =
        substitute_equivalent_type_names_into_definition list_equivalent_names
          s1
      in
      let s2_substituted =
        substitute_equivalent_type_names_into_definition list_equivalent_names
          s2
      in
      Styv_ichoice (s1_substituted, s2_substituted)
  | Styv_echoice (s1, s2) ->
      let s1_substituted =
        substitute_equivalent_type_names_into_definition list_equivalent_names
          s1
      in
      let s2_substituted =
        substitute_equivalent_type_names_into_definition list_equivalent_names
          s2
      in
      Styv_ichoice (s1_substituted, s2_substituted)
  | Styv_var (name, continuation) -> (
      let continuation_substituted =
        substitute_equivalent_type_names_into_definition list_equivalent_names
          continuation
      in
      match List.Assoc.find list_equivalent_names ~equal:String.equal name with
      | None -> Styv_var (name, continuation_substituted)
      | Some new_name -> Styv_var (new_name, continuation_substituted))

let eliminate_unguarded_type_names list_definitions =
  let extract_equivalent_type_name (name, definition) =
    match definition with
    | Styv_var (equivalent_name, _) -> Some (name, equivalent_name)
    | _ -> None
  in
  let list_equivalent_names =
    list_definitions
    |> List.filter_map ~f:extract_equivalent_type_name
    |> normalize_list_equivalent_type_names
  in
  let is_guarded definition =
    match definition with Styv_var _ -> false | _ -> true
  in
  if
    List.exists list_equivalent_names ~f:(fun (name1, name2) ->
        String.equal name1 name2)
  then failwith "Circular definition of type names is detected"
  else
    let list_remaining_definitions =
      List.filter list_definitions ~f:(fun (_, definition) ->
          is_guarded definition)
    in
    List.map list_remaining_definitions ~f:(fun (name, definition) ->
        ( name,
          substitute_equivalent_type_names_into_definition list_equivalent_names
            definition ))

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

(* Type-equality checking for regular guide types *)

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

(* Create fresh type names *)

let counter_fresh_type_name = ref 0

let create_fresh_type_name type_name () =
  let fresh_number = !counter_fresh_type_name in
  let () = counter_fresh_type_name := fresh_number + 1 in
  type_name ^ "_temp_" ^ Int.to_string fresh_number

(* Normalize type name definitions *)

let rec normalize_type_definition type_name definition =
  match definition with
  | Styv_one -> (Styv_one, [])
  | Styv_conj (b, s) ->
      let s_compact, list_new_definitions_recursive =
        normalize_type_definition type_name s
      in
      let definition_transformed = Styv_conj (b, s_compact) in
      let fresh_type_name = create_fresh_type_name type_name () in
      let current_definition_compact = Styv_var (fresh_type_name, Styv_one) in
      ( current_definition_compact,
        (fresh_type_name, definition_transformed)
        :: list_new_definitions_recursive )
  | Styv_imply (b, s) ->
      let s_compact, list_new_definitions_recursive =
        normalize_type_definition type_name s
      in
      let definition_transformed = Styv_imply (b, s_compact) in
      let fresh_type_name = create_fresh_type_name type_name () in
      let current_definition_compact = Styv_var (fresh_type_name, Styv_one) in
      ( current_definition_compact,
        (fresh_type_name, definition_transformed)
        :: list_new_definitions_recursive )
  | Styv_ichoice (s1, s2) ->
      let s1_compact, list_new_definitions_recursive1 =
        normalize_type_definition type_name s1
      in
      let s2_compact, list_new_definitions_recursive2 =
        normalize_type_definition type_name s2
      in
      let definition_transformed = Styv_ichoice (s1_compact, s2_compact) in
      let fresh_type_name = create_fresh_type_name type_name () in
      let current_definition_compact = Styv_var (fresh_type_name, Styv_one) in
      ( current_definition_compact,
        (fresh_type_name, definition_transformed)
        :: list_new_definitions_recursive1
        @ list_new_definitions_recursive2 )
  | Styv_echoice (s1, s2) ->
      let s1_compact, list_new_definitions_recursive1 =
        normalize_type_definition type_name s1
      in
      let s2_compact, list_new_definitions_recursive2 =
        normalize_type_definition type_name s2
      in
      let definition_transformed = Styv_echoice (s1_compact, s2_compact) in
      let fresh_type_name = create_fresh_type_name type_name () in
      let current_definition_compact = Styv_var (fresh_type_name, Styv_one) in
      ( current_definition_compact,
        (fresh_type_name, definition_transformed)
        :: list_new_definitions_recursive1
        @ list_new_definitions_recursive2 )
  | Styv_var (name, continuation) ->
      let continuation_compact, list_new_definitions_recursive =
        normalize_type_definition type_name continuation
      in
      let current_definition_compact = Styv_var (name, continuation_compact) in
      (current_definition_compact, list_new_definitions_recursive)

let normalize_type_name_and_definition (name, definition) =
  match definition with
  | Styv_one -> failwith "Some type name is defined as immediate termination"
  | Styv_conj (b, s) ->
      let s_compact, list_new_definitions = normalize_type_definition name s in
      let name_and_definition_transformed = (name, Styv_conj (b, s_compact)) in
      name_and_definition_transformed :: list_new_definitions
  | Styv_imply (b, s) ->
      let s_compact, list_new_definitions = normalize_type_definition name s in
      let name_and_definition_transformed = (name, Styv_imply (b, s_compact)) in
      name_and_definition_transformed :: list_new_definitions
  | Styv_ichoice (s1, s2) ->
      let s1_compact, list_new_definitions1 =
        normalize_type_definition name s1
      in
      let s2_compact, list_new_definitions2 =
        normalize_type_definition name s2
      in
      let name_and_definition_transformed =
        (name, Styv_ichoice (s1_compact, s2_compact))
      in
      (name_and_definition_transformed :: list_new_definitions1)
      @ list_new_definitions2
  | Styv_echoice (s1, s2) ->
      let s1_compact, list_new_definitions1 =
        normalize_type_definition name s1
      in
      let s2_compact, list_new_definitions2 =
        normalize_type_definition name s2
      in
      let name_and_definition_transformed =
        (name, Styv_echoice (s1_compact, s2_compact))
      in
      (name_and_definition_transformed :: list_new_definitions1)
      @ list_new_definitions2
  | Styv_var _ -> failwith "Some type name is defined as a type name"

let normalize_list_definitions list_definitions =
  list_definitions
  |> List.map ~f:normalize_type_name_and_definition
  |> List.concat

(* Mainf function for checking type equality *)

let type_equality_check prog first_type_name second_type_name =
  let list_type_definitions =
    collect_type_definitions prog
    |> detect_duplicated_definitions |> check_all_names_defined
    |> eliminate_redundant_type_names_from_all_definitions
    |> eliminate_unguarded_type_names |> normalize_list_definitions
  in
  (* For debugging *)
  let () =
    print_list_type_definitions Format.std_formatter list_type_definitions
  in
  let first_type_definition =
    List.Assoc.find_exn list_type_definitions ~equal:String.equal
      first_type_name
  and second_type_definition =
    List.Assoc.find_exn list_type_definitions ~equal:String.equal
      second_type_name
  in
  let equality_result =
    regular_type_equality list_type_definitions first_type_definition
      second_type_definition
  in
  let () =
    match equality_result with
    | false ->
        printf "Types %s and %s are unequal\n" first_type_name second_type_name
    | true ->
        printf "Types %s and %s are equal\n" first_type_name second_type_name
  in
  Ok ()
