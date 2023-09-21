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
  let () = counter_fresh_type_name := 0 in
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

(* Compute norms of type names *)

let print_list_names_optinal_norms list_names_norms =
  let print_norm (name, counter) =
    match counter with
    | None -> printf "Type %s has infinite norm\n" name
    | Some n -> printf "Type %s has norm %i\n" name n
  in
  List.iter list_names_norms ~f:print_norm

let rec compute_norm_definition_from_current_norms list_names_norms definition =
  match definition with
  | Styv_one -> Some 0
  | Styv_conj (_, s) -> (
      let recursive_result =
        compute_norm_definition_from_current_norms list_names_norms s
      in
      match recursive_result with None -> None | Some n -> Some (1 + n))
  | Styv_imply (_, s) -> (
      let recursive_result =
        compute_norm_definition_from_current_norms list_names_norms s
      in
      match recursive_result with None -> None | Some n -> Some (1 + n))
  | Styv_ichoice (s1, s2) -> (
      let s1_norm =
        compute_norm_definition_from_current_norms list_names_norms s1
      in
      let s2_norm =
        compute_norm_definition_from_current_norms list_names_norms s2
      in
      match (s1_norm, s2_norm) with
      | None, None -> None
      | Some n1, None -> Some (1 + n1)
      | None, Some n2 -> Some (1 + n2)
      | Some n1, Some n2 -> Some (1 + min n1 n2))
  | Styv_echoice (s1, s2) -> (
      let s1_norm =
        compute_norm_definition_from_current_norms list_names_norms s1
      in
      let s2_norm =
        compute_norm_definition_from_current_norms list_names_norms s2
      in
      match (s1_norm, s2_norm) with
      | None, None -> None
      | Some n1, None -> Some (1 + n1)
      | None, Some n2 -> Some (1 + n2)
      | Some n1, Some n2 -> Some (1 + min n1 n2))
  | Styv_var (name, continuation) -> (
      let continuation_norm =
        compute_norm_definition_from_current_norms list_names_norms continuation
      in
      let name_norm =
        List.Assoc.find_exn list_names_norms ~equal:String.equal name
      in
      match (name_norm, continuation_norm) with
      | None, None -> None
      | Some _, None -> None
      | None, Some _ -> None
      | Some n1, Some n2 -> Some (n1 + n2))

let refine_norms list_definitions list_names_norms =
  let compute_new_counter (name, old_counter) =
    let definition =
      List.Assoc.find_exn list_definitions ~equal:String.equal name
    in
    let new_counter =
      compute_norm_definition_from_current_norms list_names_norms definition
    in
    let any_update =
      match (old_counter, new_counter) with
      | None, None -> false
      | Some _, None ->
          failwith "The new counter value is larger than the current counter"
      | None, Some _ -> true
      | Some n1, Some n2 -> n1 > n2
    in
    (any_update, (name, new_counter))
  in
  let list_change, map_list_new =
    List.unzip (List.map list_names_norms ~f:compute_new_counter)
  in
  let any_change = List.exists list_change ~f:(fun b -> b) in
  (any_change, map_list_new)

let compute_norms_of_type_names list_definitions =
  let initial_list_names_norms =
    List.map list_definitions ~f:(fun (name, _) -> (name, None))
  in
  let rec recursively_refine_map map_list =
    let any_change, map_list_updated = refine_norms list_definitions map_list in
    if any_change then recursively_refine_map map_list_updated
    else map_list_updated
  in
  let list_names_norms_saturated =
    recursively_refine_map initial_list_names_norms
  in
  let extract_finite_norm (name, norm) =
    match norm with None -> None | Some n -> Some (name, n)
  in
  let list_names_finite_norms =
    List.map list_names_norms_saturated ~f:extract_finite_norm
  in
  if List.exists list_names_finite_norms ~f:Option.is_none then
    failwith "Some type name has an infinite norm"
  else List.filter_opt list_names_finite_norms

let print_list_names_norms list_names_norms =
  let print_norm (name, norm) = printf "Type %s has norm %i\n" name norm in
  List.iter list_names_norms ~f:print_norm

(* Create the initial full base *)

let rec get_norm_of_name_string list_names_norms definition =
  match definition with
  | Styv_one -> 0
  | Styv_var (name, continuation) ->
      let name_norm =
        List.Assoc.find_exn list_names_norms ~equal:String.equal name
      in
      let continuation_norm =
        get_norm_of_name_string list_names_norms continuation
      in
      name_norm + continuation_norm
  | _ -> failwith "The given definition is not a string of type names"

let make_single_norm_reducing_step list_names_norms definition =
  match definition with
  | Styv_one -> failwith "We cannot make a norm-reducing step"
  | Styv_conj (_, s) -> s
  | Styv_imply (_, s) -> s
  | Styv_ichoice (s1, s2) ->
      let s1_norm = get_norm_of_name_string list_names_norms s1 in
      let s2_norm = get_norm_of_name_string list_names_norms s2 in
      if s1_norm <= s2_norm then s1 else s2
  | Styv_echoice (s1, s2) ->
      let s1_norm = get_norm_of_name_string list_names_norms s1 in
      let s2_norm = get_norm_of_name_string list_names_norms s2 in
      if s1_norm <= s2_norm then s1 else s2
  | Styv_var _ -> failwith "The given definition is a string of type names"

let rec substitute_into_type_name_string target type_name_string =
  match target with
  | Styv_one -> type_name_string
  | Styv_var (name, continuation) ->
      let continuation_substituted =
        substitute_into_type_name_string continuation type_name_string
      in
      Styv_var (name, continuation_substituted)
  | _ -> failwith "The target of substitution is not a string of type names"

let rec make_norm_reducing_steps list_definitions list_names_norms definition
    num_steps =
  assert (num_steps >= 0);
  if num_steps = 0 then definition
  else
    match definition with
    | Styv_one ->
        failwith "The given n is larger than the norm of the definition"
    | Styv_conj (_, s) ->
        make_norm_reducing_steps list_definitions list_names_norms s
          (num_steps - 1)
    | Styv_imply (_, s) ->
        make_norm_reducing_steps list_definitions list_names_norms s
          (num_steps - 1)
    | Styv_ichoice (s1, s2) ->
        let s1_norm = get_norm_of_name_string list_names_norms s1 in
        let s2_norm = get_norm_of_name_string list_names_norms s2 in
        if s1_norm <= s2_norm then
          make_norm_reducing_steps list_definitions list_names_norms s1
            (num_steps - 1)
        else
          make_norm_reducing_steps list_definitions list_names_norms s2
            (num_steps - 1)
    | Styv_echoice (s1, s2) ->
        let s1_norm = get_norm_of_name_string list_names_norms s1 in
        let s2_norm = get_norm_of_name_string list_names_norms s2 in
        if s1_norm <= s2_norm then
          make_norm_reducing_steps list_definitions list_names_norms s1
            (num_steps - 1)
        else
          make_norm_reducing_steps list_definitions list_names_norms s2
            (num_steps - 1)
    | Styv_var (name, continuation) ->
        let name_norm =
          List.Assoc.find_exn list_names_norms ~equal:String.equal name
        in
        if name_norm <= num_steps then
          make_norm_reducing_steps list_definitions list_names_norms
            continuation (num_steps - name_norm)
        else
          let definition =
            List.Assoc.find_exn list_definitions ~equal:String.equal name
          in
          let definition_continuation =
            make_single_norm_reducing_step list_names_norms definition
          in
          let definition_reduced =
            make_norm_reducing_steps list_definitions list_names_norms
              definition_continuation (num_steps - 1)
          in
          substitute_into_type_name_string definition_reduced continuation

let create_initial_full_base list_definitions list_names_norms =
  let list_type_names = List.map list_definitions ~f:(fun (name, _) -> name) in
  let list_pairs_type_names =
    List.cartesian_product list_type_names list_type_names
  in
  let create_corresponding_type (name1, name2) =
    let norm1 =
      List.Assoc.find_exn list_names_norms ~equal:String.equal name1
    in
    let norm2 =
      List.Assoc.find_exn list_names_norms ~equal:String.equal name2
    in
    if norm1 < norm2 then None
    else
      let definition1 =
        List.Assoc.find_exn list_definitions ~equal:String.equal name1
      in
      let name1_norm_reduced =
        make_norm_reducing_steps list_definitions list_names_norms definition1
          norm2
      in
      let corresponding_type = Styv_var (name2, name1_norm_reduced) in
      Some (name1, corresponding_type)
  in
  List.filter_map list_pairs_type_names ~f:create_corresponding_type

let print_base base =
  let print_candidate_decomposition pair =
    let name, decomposition = pair in
    Format.fprintf Format.std_formatter
      "(Type name, decomposition) = (%s, %a)\n" name Ast_ops.print_sess_tyv
      decomposition
  in
  List.iter base ~f:print_candidate_decomposition

(* Main function for checking type equality *)

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
  let list_names_norms = compute_norms_of_type_names list_type_definitions in
  let initial_full_base =
    create_initial_full_base list_type_definitions list_names_norms
  in
  let () =
    print_list_names_norms list_names_norms;
    print_base initial_full_base
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
