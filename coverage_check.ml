open Core
open Guide_type_utility
open Typecheck
open Ast_types

(* Access function definitions *)

let get_function_definition list_function_definitions f_id =
  match List.Assoc.find list_function_definitions ~equal:String.equal f_id with
  | Some x -> x
  | None ->
      failwith
        (Format.asprintf
           "Function %s has no definition in get_function_definition" f_id)

(* Expand a type name to its definition so that it becomes clear what the first
   transition step of the type is *)

let expand_type_name list_type_definitions (name, continuation) =
  match List.Assoc.find list_type_definitions ~equal:String.equal name with
  | None ->
      failwith
        (Format.asprintf "Type name %s has no definition in expand_type_name"
           name)
  | Some name_definition ->
      substitute_into_type_definition name_definition continuation

let rec recursively_expand_type_name list_type_definitions definition =
  match definition with
  | Styv_var (name, continuation) ->
      let expanded_type =
        expand_type_name list_type_definitions (name, continuation)
      in
      recursively_expand_type_name list_type_definitions expanded_type
  | _ -> definition

let expand_list_input_types list_type_definitions list_input_types =
  List.map list_input_types
    ~f:(recursively_expand_type_name list_type_definitions)

(* Detect a cycle during coverage checking *)

let detect_cycle_coverage_checking acc (f_id, list_input_types) =
  let equal_list_input_types list1 list2 =
    let list1_sorted = List.dedup_and_sort list1 ~compare:compare_sess_tyv
    and list2_sorted = List.dedup_and_sort list2 ~compare:compare_sess_tyv in
    if List.length list1_sorted <> List.length list2_sorted then false
    else
      let list_zipped = List.zip_exn list1_sorted list2_sorted in
      List.for_all list_zipped ~f:(fun (x, y) -> equal_sess_tyv x y)
  in
  let rec traverse_acc acc =
    match acc with
    | [] -> None
    | (current_f_id, current_list, (current_type_name, _)) :: tl ->
        if
          String.equal current_f_id f_id
          && equal_list_input_types current_list list_input_types
        then Some current_type_name
        else traverse_acc tl
  in
  traverse_acc acc

let rec update_type_definition_in_acc acc (type_name, definition) =
  match acc with
  | [] -> []
  | (hd_f_id, hd_list_types, (hd_type_name, hd_definition)) :: tl ->
      if String.equal hd_type_name type_name then
        let () = assert (Option.is_none hd_definition) in
        (hd_f_id, hd_list_types, (hd_type_name, Some definition)) :: tl
      else
        let tl_updated =
          update_type_definition_in_acc tl (type_name, definition)
        in
        (hd_f_id, hd_list_types, (hd_type_name, hd_definition)) :: tl_updated

(* Counter for generating fresh type names *)

let counter_fresh_type_name = ref 0

let create_fresh_type_name () =
  let fresh_number = !counter_fresh_type_name in
  let () = counter_fresh_type_name := fresh_number + 1 in
  "T_temp_" ^ Int.to_string fresh_number

(* Determine if a given expression in a sampling statement is covered (i.e., it
   draws a fresh sample) *)

let distribution_base_type exp ctxt =
  match tycheck_exp ctxt exp with
  | Ok (Btyv_dist x) -> x
  | error ->
      let () =
        Or_error.iter_error error ~f:(fun e -> Error.pp Format.std_formatter e)
      in
      failwith "The given expression is not a distribution in line 94"

let get_covered_and_uncovered_distribution_base_types bty =
  match bty with
  | Btyv_prim x -> (true, Btyv_prim x, Btyv_prim_uncovered x)
  | Btyv_prim_uncovered x -> (false, Btyv_prim x, Btyv_prim_uncovered x)
  | Btyv_tensor (pty, dims) ->
      (true, Btyv_tensor (pty, dims), Btyv_tensor_uncovered (pty, dims))
  | Btyv_tensor_uncovered (pty, dims) ->
      (false, Btyv_tensor (pty, dims), Btyv_tensor_uncovered (pty, dims))
  | Btyv_simplex n -> (true, Btyv_simplex n, Btyv_simplex_uncovered n)
  | Btyv_simplex_uncovered n -> (false, Btyv_simplex n, Btyv_simplex_uncovered n)
  | _ -> failwith "The base type of the distribution is not supported"

(* Check the coverage of Styv_conj. This is used as a helper function inside
   simulate_type_with_command. *)

let covered_by_list_conj_types covered_dist_base_type list_input_types =
  let covered_by_conj_type definition =
    match definition with
    | Styv_conj (b, _) -> equal_base_tyv b covered_dist_base_type
    | _ ->
        failwith
          "The given type is not of the form Styv_conj in \
           covered_by_list_conj_types"
  in
  List.for_all list_input_types ~f:covered_by_conj_type

(* Simulate an input type alongside a command. It returns (i) a type constructed
   by simulating the input type alongside the command, (ii) the list of
   continuations after the simulation, and (iii) the list of newly created type
   names and their definitions that are introduced during coverage checking.

   ctxt is a context used to infer the type of an expression. channel_id_target
   is the name of the channel between the subguide and the model.*)

let simulate_type_with_command list_function_definitions list_type_definitions
    cmd psig_ctxt ctxt channel_id_target input_type =
  (* acc records the pairs of (function ID, list of guide types) that the
     coverage checking has encountered so far. acc is used to detect a cycle.
     Additionally, each pair also comes with a freshly generate type name such
     that we can refer to it when we encounter it for the second time (i.e.,
     when a cycle is detected). *)
  let rec simulate ctxt cmd list_input_types acc =
    let list_input_types =
      expand_list_input_types list_type_definitions list_input_types
    in
    match cmd.cmd_desc with
    | M_ret _ -> (Styv_one, list_input_types, acc)
    | M_bnd (cmd1, var_name, cmd2) ->
        let tyv1 = Or_error.ok_exn (forward_wrapper psig_ctxt ctxt cmd1) in
        let ctxt' =
          match var_name with
          | None -> ctxt
          | Some var_name -> Map.set ctxt ~key:var_name.txt ~data:tyv1
        in
        let type1, list_continuations1, acc1 =
          simulate ctxt cmd1 list_input_types acc
        in
        let type2, list_continuations2, acc2 =
          simulate ctxt' cmd2 list_continuations1 acc1
        in
        (substitute_into_type_definition type1 type2, list_continuations2, acc2)
    | M_call (f_id, _) -> (
        match
          detect_cycle_coverage_checking acc (f_id.txt, list_input_types)
        with
        | Some type_name -> (Styv_var (type_name, Styv_one), [], acc)
        | None ->
            let f_fresh_type_name = create_fresh_type_name () in
            let f_def =
              get_function_definition list_function_definitions f_id.txt
            in
            let acc_augmented =
              (f_id.txt, list_input_types, (f_fresh_type_name, None)) :: acc
            in
            let f_type, list_continuations, acc_intermediate =
              simulate ctxt f_def.proc_body list_input_types acc_augmented
            in
            let acc_updated =
              update_type_definition_in_acc acc_intermediate
                (f_fresh_type_name, f_type)
            in
            ( Styv_var (f_fresh_type_name, Styv_one),
              list_continuations,
              acc_updated ))
    | M_sample_recv (_, channel_id) ->
        if String.equal channel_id_target channel_id.txt then
          failwith
            "The subguide cannot contain M_sample_recv for the channel between \
             the subguide and model"
        else (Styv_one, list_input_types, acc)
    | M_sample_send (exp, channel_id) ->
        let dist_base_type = distribution_base_type exp ctxt in
        let is_covered, covered_dist_base_type, uncovered_dist_base_type =
          get_covered_and_uncovered_distribution_base_types dist_base_type
        in
        if String.equal channel_id_target channel_id.txt then
          let list_continuations =
            List.map list_input_types ~f:(fun definition ->
                match definition with
                | Styv_conj (tyv, continuation) ->
                    assert (
                      equal_base_tyv tyv covered_dist_base_type
                      || equal_base_tyv tyv uncovered_dist_base_type);
                    continuation
                | _ ->
                    failwith
                      (Format.asprintf
                         "The given type %a is not of the form Styv_conj"
                         Ast_ops.print_sess_tyv definition))
          in
          let is_covered_by_input_types =
            covered_by_list_conj_types covered_dist_base_type list_input_types
          in
          (* If the sampling statement of the current command or all input types
             cover the random variable, it is deemed covered. *)
          if is_covered || is_covered_by_input_types then
            ( Styv_conj (covered_dist_base_type, Styv_one),
              list_continuations,
              acc )
          else
            ( Styv_conj (uncovered_dist_base_type, Styv_one),
              list_continuations,
              acc )
        else (Styv_one, list_input_types, acc)
    | M_branch_recv (cmd1, cmd2, channel_id) ->
        if String.equal channel_id_target channel_id.txt then
          let list_input_types_branch_swapped =
            List.map list_input_types ~f:(fun definition ->
                match definition with
                | Styv_echoice (s1, s2) -> Styv_echoice (s2, s1)
                | _ ->
                    failwith
                      "Because the given type is not of the form Styv_echoice, \
                       we cannot swap the two branches")
          in
          let type1, result1, acc1 = simulate ctxt cmd1 list_input_types acc in
          let type2, result2, acc2 =
            simulate ctxt cmd2 list_input_types_branch_swapped acc1
          in
          let list_continuations =
            List.dedup_and_sort (result1 @ result2) ~compare:compare_sess_tyv
          in
          (Styv_echoice (type1, type2), list_continuations, acc2)
        else
          let list_first_branch_continuations =
            List.map list_input_types ~f:(fun definition ->
                match definition with
                | Styv_echoice (s1, _) -> s1
                | _ -> failwith "The given type is not of the form Styv_echoice")
          in
          (* We only enter the first branch because the second branch
             corresponds to the case where the previous subguide diverges from
             the current subguide. *)
          simulate ctxt cmd1 list_first_branch_continuations acc
    | M_branch_send _ -> failwith "A guide program cannot contain M_branch_send"
    | M_branch_self (_, cmd1, cmd2) ->
        let type1, list_continuations1, acc1 =
          simulate ctxt cmd1 list_input_types acc
        in
        let type2, list_continuations2, acc2 =
          simulate ctxt cmd2 list_input_types acc1
        in
        (* For simplicity, we require the two types constructed for the two
           internal branches should be syntactically identical. *)
        assert (equal_sess_tyv type1 type2);
        (type1, list_continuations1 @ list_continuations2, acc2)
    | M_loop (n, _, bind_name, bind_ty, loop_body) ->
        let bind_tyv = eval_ty bind_ty in
        let ctxt' = Map.set ctxt ~key:bind_name.txt ~data:bind_tyv in
        let insert_into_acc (type_acc, list_continuations_acc, acc_acc) () =
          let type_updated, list_continuations_updated, acc_updated =
            simulate ctxt' loop_body list_continuations_acc acc_acc
          in
          ( substitute_into_type_definition type_acc type_updated,
            list_continuations_updated,
            acc_updated )
        in
        List.fold
          (List.init n ~f:(fun _ -> ()))
          ~init:(Styv_one, list_input_types, acc)
          ~f:insert_into_acc
    | M_iter (iter_exp, _, iter_name, bind_name, bind_ty, loop_body) -> (
        let iter_tyv = Or_error.ok_exn (tycheck_exp ctxt iter_exp) in
        match iter_tyv with
        | Btyv_tensor (pty, dims) when List.length dims > 0 ->
            let elem_tyv = Btyv_tensor (pty, List.tl_exn dims) in
            let bind_tyv = eval_ty bind_ty in
            let ctxt' = Map.set ctxt ~key:iter_name.txt ~data:elem_tyv in
            let ctxt'' = Map.set ctxt' ~key:bind_name.txt ~data:bind_tyv in
            let insert_into_acc (type_acc, list_continuations_acc, acc_acc) () =
              let type_updated, list_continuations_updated, acc_updated =
                simulate ctxt'' loop_body list_continuations_acc acc_acc
              in
              ( substitute_into_type_definition type_acc type_updated,
                list_continuations_updated,
                acc_updated )
            in
            List.fold
              (List.init (List.hd_exn dims) ~f:(fun _ -> ()))
              ~init:(Styv_one, list_input_types, acc)
              ~f:insert_into_acc
        | _ -> failwith "The given M_iter is not iterable")
  in
  simulate ctxt cmd [ input_type ] []

let simulate_type_with_proc list_function_definitions list_type_definitions proc
    psig_ctxt ext_ctxt channel_id_target input_type =
  let cmd = proc.proc_body in
  let ctxt = extract_context_of_process ext_ctxt proc in
  simulate_type_with_command list_function_definitions list_type_definitions cmd
    psig_ctxt ctxt channel_id_target input_type

(* Simulate a type alongside each process in the sequential composition of
   subguides. The input initial type is simulated alongside the first subguide.
   Its output type is then simulated alongside the second subguide. We repeat it
   until we obtain the final type after simulating the last subguide. *)

let successively_simulate_type_with_guide_composition list_function_definitions
    list_type_definitions guide_composition psig_ctxt ext_ctxt
    initial_uncovered_type =
  let simulate acc (proc, channel_name) =
    let cumulative_covered_type, list_type_definitions = acc in
    let final_type, _, acc_output =
      simulate_type_with_proc list_function_definitions list_type_definitions
        proc psig_ctxt ext_ctxt channel_name cumulative_covered_type
    in
    let list_new_type_definitions =
      List.map acc_output ~f:(fun (_, _, possible_definition) ->
          match possible_definition with
          | type_name, None ->
              failwith
                (Format.asprintf
                   "Type name %s has no definition in the output acc" type_name)
          | type_name, Some x -> (type_name, x))
    in
    (final_type, list_new_type_definitions @ list_type_definitions)
  in
  List.fold guide_composition
    ~init:(initial_uncovered_type, list_type_definitions)
    ~f:simulate

(* Check if a given type is fully covered *)

let is_base_type_covered base_type =
  match base_type with
  | Btyv_prim _ -> true
  | Btyv_prim_uncovered _ -> false
  | Btyv_tensor _ -> true
  | Btyv_tensor_uncovered _ -> false
  | Btyv_simplex _ -> true
  | Btyv_simplex_uncovered _ -> false
  | _ ->
      failwith
        "The given base type is not a (covered or uncovered) primitive type"

(* Extract all type names mentioned in a given type. We also return whether the
   type only mentions covered base types (except inside type names). The first
   output is a Boolean flag indicating that the input type only mentions covered
   base types (except possibly inside other type names). The second output is
   the list of type names mentioned. *)
let rec extract_all_type_names_mentioned definition =
  match definition with
  | Styv_one -> (true, [])
  | Styv_conj (b, s) ->
      if not (is_base_type_covered b) then (false, [])
      else extract_all_type_names_mentioned s
  | Styv_imply (b, s) ->
      if not (is_base_type_covered b) then (false, [])
      else extract_all_type_names_mentioned s
  | Styv_ichoice (s1, s2) ->
      let is_covered1, list_type_names1 = extract_all_type_names_mentioned s1 in
      let is_covered2, list_type_names2 = extract_all_type_names_mentioned s2 in
      if is_covered1 && is_covered2 then
        ( true,
          List.dedup_and_sort
            (list_type_names1 @ list_type_names2)
            ~compare:String.compare )
      else (false, [])
  | Styv_echoice (s1, s2) ->
      let is_covered1, list_type_names1 = extract_all_type_names_mentioned s1 in
      let is_covered2, list_type_names2 = extract_all_type_names_mentioned s2 in
      if is_covered1 && is_covered2 then
        ( true,
          List.dedup_and_sort
            (list_type_names1 @ list_type_names2)
            ~compare:String.compare )
      else (false, [])
  | Styv_var (type_name, continuation) ->
      let is_continuation_covered, list_type_names =
        extract_all_type_names_mentioned continuation
      in
      if is_continuation_covered then
        ( true,
          List.dedup_and_sort
            (type_name :: list_type_names)
            ~compare:String.compare )
      else (false, [])

(* Create an initial mapping from type names to their full-coverage statuses *)
let create_initial_full_coverage_map list_definitions =
  let list_type_names =
    List.map list_definitions ~f:(fun (type_name, _) -> type_name)
  in
  let get_all_type_names_mentioned type_name =
    let type_definition =
      match List.Assoc.find list_definitions ~equal:String.equal type_name with
      | None ->
          failwith
            (Format.asprintf
               "Type name %s has no definition in is_type_name_fully_covered"
               type_name)
      | Some x -> x
    in
    extract_all_type_names_mentioned type_definition
  in
  let create_initial_entry type_name =
    let is_covered, all_types_names_mentioned =
      get_all_type_names_mentioned type_name
    in
    (type_name, (all_types_names_mentioned, is_covered))
  in
  List.map list_type_names ~f:create_initial_entry

let is_type_name_covered_in_coverage_map coverage_map type_name =
  let _, is_covered =
    match List.Assoc.find coverage_map ~equal:String.equal type_name with
    | None ->
        failwith
          (Format.asprintf
             "Type name %s has no entry in refine_map_full_coverage_checking"
             type_name)
    | Some x -> x
  in
  is_covered

(* Refine the coverage map (i.e., mapping from type names to their current
   full-coverage statuses) by one step *)
let refine_full_coverage_map coverage_map =
  let refine_single_entry (type_name, (all_types_names_mentioned, is_covered)) =
    let still_full_covered =
      List.for_all all_types_names_mentioned ~f:(fun x ->
          is_type_name_covered_in_coverage_map coverage_map x)
    in
    let any_change = Bool.( <> ) is_covered still_full_covered in
    (any_change, (type_name, (all_types_names_mentioned, still_full_covered)))
  in
  let list_change, result_refinement =
    coverage_map |> List.map ~f:refine_single_entry |> List.unzip
  in
  let any_change = List.exists list_change ~f:(fun x -> x) in
  (any_change, result_refinement)

(* Recursively refine the coverage map until it is saturated *)
let is_type_name_fully_covered list_definitions =
  let initial_coverage_map =
    create_initial_full_coverage_map list_definitions
  in
  let rec recursively_refine_map_full_coverage_checking coverage_map =
    let any_change, result_refinement = refine_full_coverage_map coverage_map in
    if any_change then
      recursively_refine_map_full_coverage_checking result_refinement
    else result_refinement
  in
  recursively_refine_map_full_coverage_checking initial_coverage_map

let check_full_coverage list_definitions definition =
  let is_covered, all_type_names_mentioned =
    extract_all_type_names_mentioned definition
  in
  let coverage_map = is_type_name_fully_covered list_definitions in
  let all_type_names_covered =
    List.for_all all_type_names_mentioned ~f:(fun x ->
        is_type_name_covered_in_coverage_map coverage_map x)
  in
  if is_covered && all_type_names_covered then true else false

(* Main function for coverage checking *)

let coverage_check_prog prog =
  let list_type_definitions = collect_type_definitions prog in
  let ext_ctxt = collect_externals prog in
  let psig_ctxt = Or_error.ok_exn (collect_proc_sigs prog) in
  let list_function_definitions = collect_function_definitions prog in
  let list_guides = collect_guide_composition prog in
  let list_guide_defs_right_channels =
    let extract_function_def function_name =
      match
        List.Assoc.find list_function_definitions ~equal:String.equal
          function_name
      with
      | Some x -> x
      | None -> failwith "The provided function name does not exist in the file"
    in
    let extract_function_def_and_right_channel function_name =
      let function_def = extract_function_def function_name in
      let right_channel_name = get_right_channel_name function_def in
      (function_def, right_channel_name)
    in
    List.map list_guides ~f:extract_function_def_and_right_channel
  in
  let initial_uncovered_type =
    prog |> collect_initial_uncovered_type |> eval_sty
  in
  let final_type, acc =
    successively_simulate_type_with_guide_composition list_function_definitions
      list_type_definitions list_guide_defs_right_channels psig_ctxt ext_ctxt
      initial_uncovered_type
  in
  (* Print out the result of coverage checking *)
  let () =
    Format.printf "Final type of coverage checking = %a\n"
      Ast_ops.print_sess_tyv final_type;
    (* List.iter list_continuations ~f:(fun definition ->
        Format.printf "Continuation = %a\n" Ast_ops.print_sess_tyv definition); *)
    print_endline "New types introduced by coverage checking:";
    List.iter acc ~f:(fun (type_name, definition) ->
        Format.printf "(Type name, definition) = (%s, %a)\n" type_name
          Ast_ops.print_sess_tyv definition);
    if check_full_coverage acc final_type then
      print_endline "The final type is fully covered"
    else print_endline "The final type is not fully covered"
  in
  Ok ()
