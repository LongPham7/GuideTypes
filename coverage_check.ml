open Core
open Type_equality_check_common
open Typecheck_common
open Typecheck
open Ast_types

(* Access function definitions *)

let collect_function_definitions prog =
  List.filter_map prog ~f:(fun top ->
      match top with
      | Top_proc (f_id, process) -> Some (f_id.txt, process)
      | Top_sess _ -> None
      | Top_external _ -> None)

let get_function_definition list_function_definitions f_id =
  List.Assoc.find_exn list_function_definitions ~equal:String.equal f_id

(* Expand a type name to its definition so that it becomes clear what the first
   transition step of the type is *)

let expand_type_name list_type_definitions (name, continuation) =
  let name_definition =
    List.Assoc.find_exn list_type_definitions ~equal:String.equal name
  in
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

(* Simulate an input type alongside a command. It returns (i) a type constructed
   by simulating the input type alongside the command, (ii) the list of
   continuations after the simulation, and (iii) the list of newly created type
   names and their definitions that are introduced during coverage checking. *)

let distribution_base_type exp ctxt =
  let dist_base_type =
    match tycheck_exp ctxt exp with
    | Ok (Btyv_dist x) -> x
    | _ -> failwith "The given expression is not a distribution"
  in
  match dist_base_type with
  | Btyv_prim x -> (true, x)
  | Btyv_prim_uncovered x -> (false, x)
  | _ -> failwith "The base type of the distribution is not supported"

let covered_by_list_conj_types prim_type list_input_types =
  let covered_by_conj_type definition =
    match definition with
    | Styv_conj (b, _) -> (
        match b with
        | Btyv_prim p ->
            assert (equal_prim_ty p prim_type);
            true
        | Btyv_prim_uncovered p ->
            assert (equal_prim_ty p prim_type);
            false
        | _ ->
            failwith
              "The given type is not a (covered or uncovered) primitive type")
    | _ -> failwith "The given type is not of the form Styv_conj"
  in
  List.for_all list_input_types ~f:covered_by_conj_type

(* Simulate an input type alongside a command. ctxt is a context used to infer
   the type of an expression. channel_id_target is the name of the channel
   between the subguide and the model. *)
let simulate_type_with_command list_function_definitions list_type_definitions
    cmd ctxt channel_id_target input_type =
  (* acc records the pairs of (function ID, list of guide types) that the
     coverage checking has encountered so far. acc is used to detect a cycle.
     Additionally, each pair also comes with a freshly generate type name such
     that we can refer to it when we encounter it for the second time (i.e.,
     when a cycle is detected). *)
  let rec simulate cmd list_input_types acc =
    let list_input_types =
      expand_list_input_types list_type_definitions list_input_types
    in
    match cmd.cmd_desc with
    | M_ret _ -> (Styv_one, list_input_types, acc)
    | M_bnd (cmd1, _, cmd2) ->
        let type1, list_continuations1, acc1 =
          simulate cmd1 list_input_types acc
        in
        let type2, list_continuations2, acc2 =
          simulate cmd2 list_continuations1 acc1
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
              simulate f_def.proc_body list_input_types acc_augmented
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
        let is_covered, dist_base_type = distribution_base_type exp ctxt in
        if String.equal channel_id_target channel_id.txt then
          let list_continuations =
            List.map list_input_types ~f:(fun definition ->
                match definition with
                | Styv_conj (tyv, continuation) ->
                    assert (
                      equal_base_tyv tyv (Btyv_prim dist_base_type)
                      || equal_base_tyv tyv (Btyv_prim_uncovered dist_base_type));
                    continuation
                | _ -> failwith "The given type is not of the form Styv_conj")
          in
          let is_covered_by_input_types =
            covered_by_list_conj_types dist_base_type list_input_types
          in
          (* If the sampling statement of the current command or all input types
             cover the random variable, it is deemed covered. *)
          if is_covered || is_covered_by_input_types then
            ( Styv_conj (Btyv_prim dist_base_type, Styv_one),
              list_continuations,
              acc )
          else
            ( Styv_conj (Btyv_prim_uncovered dist_base_type, Styv_one),
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
          let type1, result1, acc1 = simulate cmd1 list_input_types acc in
          let type2, result2, acc2 =
            simulate cmd2 list_input_types_branch_swapped acc1
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
          simulate cmd1 list_first_branch_continuations acc
    | M_branch_send _ -> failwith "A guide program cannot contain M_branch_send"
    | M_branch_self (_, cmd1, cmd2) ->
        let type1, list_continuations1, acc1 =
          simulate cmd1 list_input_types acc
        in
        let type2, list_continuations2, acc2 =
          simulate cmd2 list_input_types acc1
        in
        (* For simplicity, we require the two types constructed for the two
           internal branches should be syntactically identical. *)
        assert (equal_sess_tyv type1 type2);
        (type1, list_continuations1 @ list_continuations2, acc2)
    | M_loop (n, e, v_id, btyv, cmd) ->
        if n <= 0 then (Styv_one, list_input_types, acc)
        else
          let type_one_iter, list_continuations_one_iter, acc_one_iter =
            simulate cmd list_input_types acc
          in
          let decremented_cmd =
            { cmd with cmd_desc = M_loop (n - 1, e, v_id, btyv, cmd) }
          in
          let type_remaining_iters, list_continuations, acc_remaining_iters =
            simulate decremented_cmd list_continuations_one_iter acc_one_iter
          in
          ( substitute_into_type_definition type_one_iter type_remaining_iters,
            list_continuations,
            acc_remaining_iters )
    | M_iter _ -> failwith "M_iter is not supported in coverage checking"
  in
  simulate cmd [ input_type ] []

let simulate_type_with_proc list_function_definitions list_type_definitions proc
    ext_ctxt channel_id_target input_type =
  let cmd = proc.proc_body in
  let ctxt = extract_context_of_process ext_ctxt proc in
  simulate_type_with_command list_function_definitions list_type_definitions cmd
    ctxt channel_id_target input_type

let coverage_check_prog prog type_name =
  let list_type_definitions = collect_type_definitions prog in
  (* Print out the type definitions *)
  let () =
    print_list_type_definitions Format.std_formatter list_type_definitions
  in
  let ext_ctxt = collect_externals prog in
  let list_function_definitions = collect_function_definitions prog in
  let function_name = "Guide" in
  let function_def =
    match
      List.Assoc.find list_function_definitions ~equal:String.equal
        function_name
    with
    | Some x -> x
    | None -> failwith "The provided function name does not exist in the file"
  in
  let final_type, list_continuations, acc =
    simulate_type_with_proc list_function_definitions list_type_definitions
      function_def ext_ctxt "lat"
      (Styv_var (type_name, Styv_one))
  in
  let list_new_type_definitions = List.map acc ~f:(fun (_, _, x) -> x) in
  (* Print out the new types introduced by coverage checking *)
  let () =
    print_endline "New types introduced by coverage checking:";
    List.iter list_new_type_definitions ~f:(fun (type_name, definition) ->
        match definition with
        | None -> failwith "Some type name has no definition"
        | Some definition ->
            Format.printf "(Type name, definition) = (%s, %a)\n" type_name
              Ast_ops.print_sess_tyv definition)
  in
  (* Print out the type constructed *)
  let () =
    Format.printf "Final type of coverage checking = %a\n"
      Ast_ops.print_sess_tyv final_type
  in
  let () =
    List.iter list_continuations ~f:(fun definition ->
        Format.printf "Continuation = %a\n" Ast_ops.print_sess_tyv definition)
  in
  Ok ()
