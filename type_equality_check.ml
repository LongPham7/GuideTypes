open Core
open Ast_types
open Ast_ops
open Guide_type_utility

(* The type-equality checking algorithm for context-free guide types implemented
   in this module is explained in the paper "A Fast Algorithm for Deciding
   Bisimilarity of Normed Context-Free Processes" by Hirshfeld and Moller.

   This algorithm checks bisimilarity of two context-free processes. Informally,
   context-free processes are obtained by viewing context-free grammars as
   transition systems. The algebra formed by context-free processes is called
   Basic Process Algebra (BPA). *)

(* Make sure that we do not have multiple definitions for the same type name *)

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

(* Eliminate type names defined as $ (i.e., termination). It is important to
   eliminate such type names because in Greibach normal form (GNF) of
   context-free processes in BAP, every variable should be able to make a
   transition step. That is, a variable cannot be equal to the empty string.
   Hence, if a variable is defined as the empty string, we should eliminate it.
   In the context of guide types, variables in context-free processes correspond
   to guide type names. *)

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
      let name_is_redundant =
        List.exists redundant_type_names ~f:(fun redundant_name ->
            String.equal redundant_name name)
      in
      if name_is_redundant then
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
  let redundant_definitions =
    List.filter list_definitions ~f:(fun (_, definition) ->
        is_termination definition)
  in
  let redundant_type_names =
    List.map redundant_definitions ~f:(fun (name, _) -> name)
  in
  let remaining_definitions =
    List.filter list_definitions ~f:(fun (_, definition) ->
        not (is_termination definition))
  in
  let remaining_definitions_updated =
    List.map remaining_definitions ~f:(fun (name, definition) ->
        (name, eliminate_redundant_type_names redundant_type_names definition))
  in
  (remaining_definitions_updated, redundant_definitions)

(* Detect a cycle of type names. For example, consider three mutually recursive
   definitions of type names: T1 = T2[$], T2 = T3[$], and T3 = T1[$]. These
   definitions are problematic because their transitive closure yields T1 =
   T1[$], where T1 reduces to itself without making any transition step.
   Consequently, we cannot transform these context-free processes into GNF where
   every variable (i.e., type name) must be able to make a transition. *)

let propagate_head_type_name_pair (name1, name2) (target1, target2) =
  if String.equal target2 name1 then (target1, name2) else (target1, target2)

let saturate_list_head_type_name_pairs list_pairs =
  let rec saturate_with_acc acc remaining_pairs =
    match remaining_pairs with
    | [] -> acc
    | hd_pair :: tl_pairs ->
        let acc_substituted =
          List.map acc ~f:(propagate_head_type_name_pair hd_pair)
        in
        let tl_pairs_substituted =
          List.map tl_pairs ~f:(propagate_head_type_name_pair hd_pair)
        in
        saturate_with_acc (hd_pair :: acc_substituted) tl_pairs_substituted
  in
  saturate_with_acc [] list_pairs

let detect_cycle_type_names list_definitions =
  (* Head name refers to the first type name in the unguarded type definition.
     For example, if we have T1 = T2[...], T2 is the head name of T1's type
     definition. *)
  let extract_head_type_names (name, definition) =
    match definition with
    | Styv_var (head_name, _) -> Some (name, head_name)
    | _ -> None
  in
  let list_head_name_pairs_saturated =
    list_definitions
    |> List.filter_map ~f:extract_head_type_names
    |> saturate_list_head_type_name_pairs
  in
  if
    List.exists list_head_name_pairs_saturated ~f:(fun (name1, name2) ->
        String.equal name1 name2)
  then true
  else false

(* Eliminate type names whose definitions are also type names. When a type name
   is defined in such a way that the first transition is unclear, it is called
   unguarded. For example, consider a type definition T1 = T2[...] and T2 = A,
   where T1 and T2 are type names and A is the type definition of T2. Here, T1
   is unguarded because it is defined as T2[...], where the first transition is
   unclear, rather than something like real /\ T2[...], where the first
   transition is clearly real /\. To eliminate unguarded type definitions, we
   repeatedly make substitutions. In the above example, we substitute T2 = A
   into T1's definition. We keep doing this until all type definitions are
   guarded. This procedure should terminate as long as there is no cycle of type
   names. *)

let expand_unguarded_type_definitions list_definitions =
  let expand_unguarded_type_definition definition =
    match definition with
    | Styv_var (head_name, continuation) -> (
        match
          List.Assoc.find list_definitions ~equal:String.equal head_name
        with
        | None ->
            failwith
              (sprintf
                 "Type name %s has no definition in \
                  expand_unguarded_type_definitions"
                 head_name)
        | Some head_name_definition ->
            ( substitute_into_type_definition head_name_definition continuation,
              true ))
    | _ -> (definition, false)
  in
  let list_definitions_substituted_and_change =
    List.map list_definitions ~f:(fun (name, definition) ->
        let definition_substituted, any_change =
          expand_unguarded_type_definition definition
        in
        (name, definition_substituted, any_change))
  in
  let list_definitions_substituted =
    List.map list_definitions_substituted_and_change ~f:(fun (x, y, _) ->
        (x, y))
  in
  let any_change =
    List.exists list_definitions_substituted_and_change ~f:(fun (_, _, z) -> z)
  in
  (list_definitions_substituted, any_change)

let rec recursively_expand_unguarded_type_definitions list_definitions =
  let list_definitions_substituted, any_change =
    expand_unguarded_type_definitions list_definitions
  in
  if any_change then
    recursively_expand_unguarded_type_definitions list_definitions_substituted
  else list_definitions_substituted

let eliminate_unguarded_type_names list_definitions =
  let any_cycle_type_names = detect_cycle_type_names list_definitions in
  if any_cycle_type_names then failwith "A cycle of type names is detected"
  else recursively_expand_unguarded_type_definitions list_definitions

(* Type-equality checking for regular guide types. It incrementally builds up a
   tree of type equivalence while recording pairs of types whose equality are
   currently being checked. These pairs of types are used to detect cycles. This
   algorithm only works for finite-state types (i.e., regular types). If we perform
   this algorithm on infinite-state types (e.g., context-free types), the algorithm
   may not terminate, because it fails to detect a cycle. *)

let detect_cycle acc definition1 definition2 =
  let type_pair_matched (s, t) =
    equal_sess_tyv s definition1 && equal_sess_tyv t definition2
  in
  List.exists acc ~f:type_pair_matched

let expand_type_name list_type_definitions (name, continuation) =
  match
    List.Assoc.find list_type_definitions
      ~equal:(fun x y -> String.equal x y)
      name
  with
  | None ->
      failwith
        (sprintf "Type name %s has no definition in expand_type_name" name)
  | Some type_definition ->
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
  | Styv_one ->
      failwith (sprintf "Type name %s is defined as immediate termination" name)
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
  | Styv_var _ ->
      failwith (sprintf "Type name %s is defined as a type name" name)

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
        match List.Assoc.find list_names_norms ~equal:String.equal name with
        | None ->
            failwith
              (sprintf
                 "Type name %s has no norm in \
                  compute_norm_definition_from_current_norms"
                 name)
        | Some x -> x
      in
      match (name_norm, continuation_norm) with
      | None, None -> None
      | Some _, None -> None
      | None, Some _ -> None
      | Some n1, Some n2 -> Some (n1 + n2))

let refine_norms list_definitions list_names_norms =
  let compute_new_counter (name, old_counter) =
    let definition =
      match List.Assoc.find list_definitions ~equal:String.equal name with
      | None ->
          failwith
            (sprintf "Type name %s has no definition in refine_norms" name)
      | Some x -> x
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

let rec get_norm_of_type_name_string list_names_norms type_name_string =
  match type_name_string with
  | Styv_one -> 0
  | Styv_var (name, continuation) ->
      let name_norm =
        match List.Assoc.find list_names_norms ~equal:String.equal name with
        | None ->
            failwith
              (sprintf
                 "Type name %s has no norm in get_norm_of_type_name_string" name)
        | Some x -> x
      in
      let continuation_norm =
        get_norm_of_type_name_string list_names_norms continuation
      in
      name_norm + continuation_norm
  | _ ->
      failwith
        "The given definition is not a string of type names in the function \
         get_norm_of_type_name_string"

let make_single_norm_reducing_step list_names_norms definition =
  match definition with
  | Styv_one -> failwith "We cannot make a norm-reducing step"
  | Styv_conj (_, s) -> s
  | Styv_imply (_, s) -> s
  | Styv_ichoice (s1, s2) ->
      let s1_norm = get_norm_of_type_name_string list_names_norms s1 in
      let s2_norm = get_norm_of_type_name_string list_names_norms s2 in
      if s1_norm <= s2_norm then s1 else s2
  | Styv_echoice (s1, s2) ->
      let s1_norm = get_norm_of_type_name_string list_names_norms s1 in
      let s2_norm = get_norm_of_type_name_string list_names_norms s2 in
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
        let s1_norm = get_norm_of_type_name_string list_names_norms s1 in
        let s2_norm = get_norm_of_type_name_string list_names_norms s2 in
        if s1_norm <= s2_norm then
          make_norm_reducing_steps list_definitions list_names_norms s1
            (num_steps - 1)
        else
          make_norm_reducing_steps list_definitions list_names_norms s2
            (num_steps - 1)
    | Styv_echoice (s1, s2) ->
        let s1_norm = get_norm_of_type_name_string list_names_norms s1 in
        let s2_norm = get_norm_of_type_name_string list_names_norms s2 in
        if s1_norm <= s2_norm then
          make_norm_reducing_steps list_definitions list_names_norms s1
            (num_steps - 1)
        else
          make_norm_reducing_steps list_definitions list_names_norms s2
            (num_steps - 1)
    | Styv_var (name, continuation) ->
        let name_norm =
          match List.Assoc.find list_names_norms ~equal:String.equal name with
          | None ->
              failwith
                (sprintf "Type name %s has no norm in make_norm_reducing_steps"
                   name)
          | Some x -> x
        in
        if name_norm <= num_steps then
          make_norm_reducing_steps list_definitions list_names_norms
            continuation (num_steps - name_norm)
        else
          let definition =
            match List.Assoc.find list_definitions ~equal:String.equal name with
            | None ->
                failwith
                  (sprintf
                     "Type name %s has no definition in \
                      make_norm_reducing_steps"
                     name)
            | Some x -> x
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
      match List.Assoc.find list_names_norms ~equal:String.equal name1 with
      | None ->
          failwith
            (sprintf "Type name %s has no norm in create_initial_full_base"
               name1)
      | Some x -> x
    in
    let norm2 =
      match List.Assoc.find list_names_norms ~equal:String.equal name2 with
      | None ->
          failwith
            (sprintf "Type name %s has no norm in create_initial_full_base"
               name2)
      | Some x -> x
    in
    if norm1 < norm2 then None
    else
      let definition1 =
        match List.Assoc.find list_definitions ~equal:String.equal name1 with
        | None ->
            failwith
              (sprintf
                 "Type name %s has no definition in create_initial_full_base"
                 name1)
        | Some x -> x
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

(* Test equality of two strings of type names according to a given base *)

let head_and_tail_of_type_name_string type_name_string =
  match type_name_string with
  | Styv_var (name, continuation) -> (name, continuation)
  | _ ->
      failwith
        "The given definition is not a string of type names in the function \
         head_and_tail_of_type_name_string"

let rec search_for_matching_pair_of_type_names base name1 name2 =
  match base with
  | [] -> None
  | (name, decomposition) :: tl ->
      if String.equal name name1 then
        let decomposition_head, _ =
          head_and_tail_of_type_name_string decomposition
        in
        if String.equal decomposition_head name2 then Some (name, decomposition)
        else search_for_matching_pair_of_type_names tl name1 name2
      else search_for_matching_pair_of_type_names tl name1 name2

let rec equal_by_decomposition list_names_norms base type_name_string1
    type_name_string2 =
  match (type_name_string1, type_name_string2) with
  | Styv_one, Styv_one -> true
  | Styv_one, _ -> false
  | _, Styv_one -> false
  | _, _ ->
      let head_name1, continuation1 =
        head_and_tail_of_type_name_string type_name_string1
      in
      let head_name2, continuation2 =
        head_and_tail_of_type_name_string type_name_string2
      in
      let head_name1_norm =
        match
          List.Assoc.find list_names_norms ~equal:String.equal head_name1
        with
        | None ->
            failwith
              (sprintf "Type name %s has no norm in equal_by_decomposition"
                 head_name1)
        | Some x -> x
      in
      let head_name2_norm =
        match
          List.Assoc.find list_names_norms ~equal:String.equal head_name2
        with
        | None ->
            failwith
              (sprintf "Type name %s has no norm in equal_by_decomposition"
                 head_name2)
        | Some x -> x
      in
      let decompose (large_head, small_continuation)
          (small_head, large_continuation) =
        match
          search_for_matching_pair_of_type_names base large_head small_head
        with
        | None -> false
        | Some (_, decomposition) ->
            let _, decomposition_tail =
              head_and_tail_of_type_name_string decomposition
            in
            let new_type_name_string =
              substitute_into_type_name_string decomposition_tail
                small_continuation
            in
            equal_by_decomposition list_names_norms base new_type_name_string
              large_continuation
      in
      if head_name1_norm >= head_name2_norm then
        decompose (head_name1, continuation1) (head_name2, continuation2)
      else decompose (head_name2, continuation2) (head_name1, continuation1)

(* Refine a full base while maintaining its fullness *)

let bisimulate_name_and_candidate_decomposition list_definitions
    list_names_norms base (name, decomposition) =
  let definition =
    match List.Assoc.find list_definitions ~equal:String.equal name with
    | None ->
        failwith
          (sprintf
             "Type name %s has no definition in \
              bisimulate_name_and_candidate_decomposition"
             name)
    | Some x -> x
  in
  let decomposition_hd, decomposition_tl =
    head_and_tail_of_type_name_string decomposition
  in
  let decomposition_hd_definition =
    match
      List.Assoc.find list_definitions ~equal:String.equal decomposition_hd
    with
    | None ->
        failwith
          (sprintf
             "Type name %s has no definition in \
              bisimulate_name_and_candidate_decomposition"
             decomposition_hd)
    | Some x -> x
  in
  match (definition, decomposition_hd_definition) with
  | Styv_one, Styv_one -> true
  | Styv_conj (b1, s1), Styv_conj (b2, s2) ->
      let decomposition_continuation =
        substitute_into_type_name_string s2 decomposition_tl
      in
      let equal_base_type = equal_base_tyv_modulo_coverage b1 b2 in
      let equal_continuation =
        equal_by_decomposition list_names_norms base s1
          decomposition_continuation
      in
      equal_base_type && equal_continuation
  | Styv_imply (b1, s1), Styv_imply (b2, s2) ->
      let decomposition_continuation =
        substitute_into_type_name_string s2 decomposition_tl
      in
      let equal_base_type = equal_base_tyv b1 b2 in
      let equal_continuation =
        equal_by_decomposition list_names_norms base s1
          decomposition_continuation
      in
      equal_base_type && equal_continuation
  | Styv_ichoice (s1, s2), Styv_ichoice (t1, t2) ->
      let decomposition_continuation1 =
        substitute_into_type_name_string t1 decomposition_tl
      in
      let decomposition_continuation2 =
        substitute_into_type_name_string t2 decomposition_tl
      in
      let equal_continuation1 =
        equal_by_decomposition list_names_norms base s1
          decomposition_continuation1
      in
      let equal_continuation2 =
        equal_by_decomposition list_names_norms base s2
          decomposition_continuation2
      in
      equal_continuation1 && equal_continuation2
  | Styv_echoice (s1, s2), Styv_echoice (t1, t2) ->
      let decomposition_continuation1 =
        substitute_into_type_name_string t1 decomposition_tl
      in
      let decomposition_continuation2 =
        substitute_into_type_name_string t2 decomposition_tl
      in
      let equal_continuation1 =
        equal_by_decomposition list_names_norms base s1
          decomposition_continuation1
      in
      let equal_continuation2 =
        equal_by_decomposition list_names_norms base s2
          decomposition_continuation2
      in
      equal_continuation1 && equal_continuation2
  | _, _ -> false

let rec refine_base list_definitions list_names_norms base =
  let base_refined =
    List.filter base
      ~f:
        (bisimulate_name_and_candidate_decomposition list_definitions
           list_names_norms base)
  in
  let any_change = List.length base_refined < List.length base in
  if any_change then refine_base list_definitions list_names_norms base_refined
  else base_refined

(* Main function for checking type equality *)

let create_type_from_type_name list_removed_names name =
  match List.Assoc.find list_removed_names ~equal:String.equal name with
  | None -> Styv_var (name, Styv_one)
  | Some def -> def

(* Check the equality of two given type names *)
let type_equality_check list_type_definitions_raw first_type_name
    second_type_name =
  let list_type_definitions_without_termination, list_removed_names =
    list_type_definitions_raw |> detect_duplicated_definitions
    |> check_all_names_defined
    |> eliminate_redundant_type_names_from_all_definitions
  in
  let list_type_definitions =
    list_type_definitions_without_termination |> eliminate_unguarded_type_names
    |> normalize_list_definitions
  in
  let list_names_norms = compute_norms_of_type_names list_type_definitions in
  let initial_full_base =
    create_initial_full_base list_type_definitions list_names_norms
  in
  let final_base =
    refine_base list_type_definitions list_names_norms initial_full_base
  in
  (* For debugging *)
  let () =
    print_list_type_definitions Format.std_formatter list_type_definitions;
    print_list_names_norms list_names_norms;
    print_base final_base
  in
  (* Type-equality checking for regular guide types *)
  (* regular_type_equality list_type_definitions first_type second_type *)
  (* Type-equality checking for context-free guide types *)
  equal_by_decomposition list_names_norms final_base
    (create_type_from_type_name list_removed_names first_type_name)
    (create_type_from_type_name list_removed_names second_type_name)

let convert_type_definitions_to_names list_pairs =
  let create_new_type_name i definition =
    ("T_new_" ^ Int.to_string i, definition)
  in
  List.mapi list_pairs ~f:(fun i (x, y) ->
      (create_new_type_name (2 * i) x, create_new_type_name ((2 * i) + 1) y))

(* Given a list of pairs of types, check the equality of each pair. Types are
   not required to be type names. If a type is not a type name, a fresh type
   name is created and is bound to it. *)
let type_equality_check_list_type_pairs list_type_definitions_raw list_pairs =
  let list_pairs_with_fresh_type_names =
    convert_type_definitions_to_names list_pairs
  in
  let list_new_type_definitions =
    list_pairs_with_fresh_type_names
    |> List.map ~f:(fun (name_def1, name_def2) -> [ name_def1; name_def2 ])
    |> List.concat
  in
  let list_type_definitions_without_termination, list_removed_names =
    list_new_type_definitions @ list_type_definitions_raw
    |> detect_duplicated_definitions |> check_all_names_defined
    |> eliminate_redundant_type_names_from_all_definitions
  in
  let list_type_definitions =
    list_type_definitions_without_termination |> eliminate_unguarded_type_names
    |> normalize_list_definitions
  in
  let list_names_norms = compute_norms_of_type_names list_type_definitions in
  let initial_full_base =
    create_initial_full_base list_type_definitions list_names_norms
  in
  let final_base =
    refine_base list_type_definitions list_names_norms initial_full_base
  in
  (* For debugging *)
  (* let () =
       print_list_type_definitions Format.std_formatter list_type_definitions;
       print_endline "The list of norms of type names:";
       print_list_names_norms list_names_norms;
       print_endline "Final base:";
       print_base final_base
     in *)
  List.map list_pairs_with_fresh_type_names
    ~f:(fun ((name1, def1), (name2, def2)) ->
      ( def1,
        def2,
        equal_by_decomposition list_names_norms final_base
          (create_type_from_type_name list_removed_names name1)
          (create_type_from_type_name list_removed_names name2) ))

let type_equality_check_prog prog first_type_name second_type_name =
  let equality_result =
    type_equality_check
      (collect_type_definitions prog)
      first_type_name second_type_name
  in
  let () =
    match equality_result with
    | false ->
        printf "Types %s and %s are unequal\n" first_type_name second_type_name
    | true ->
        printf "Types %s and %s are equal\n" first_type_name second_type_name
  in
  Ok ()
