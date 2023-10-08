open Core
open Type_equality_check_common
open Ast_types

let collect_function_definitions prog =
  List.filter_map prog ~f:(fun top ->
      match top with
      | Top_proc (f_id, process) -> Some (f_id.txt, process.proc_body)
      | Top_sess _ -> None
      | Top_external _ -> None)

let get_function_definition list_function_definitions f_id =
  List.Assoc.find_exn list_function_definitions ~equal:String.equal f_id

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

let detect_cycle_coverage_checking acc (f_id, list_input_types) =
  let equal_list_input_types list1 list2 =
    let list1_sorted = List.dedup_and_sort list1 ~compare:compare_sess_tyv
    and list2_sorted = List.dedup_and_sort list2 ~compare:compare_sess_tyv in
    if List.length list1_sorted <> List.length list2_sorted then false
    else
      let list_zipped = List.zip_exn list1_sorted list2_sorted in
      List.for_all list_zipped ~f:(fun (x, y) -> equal_sess_tyv x y)
  in
  List.exists acc ~f:(fun (current_f_id, current_list) ->
      String.equal current_f_id f_id
      && equal_list_input_types current_list list_input_types)

let simulate_type_with_command list_function_definitions list_type_definitions
    cmd old_channel_id input_type =
  let rec simulate acc cmd list_input_types =
    let list_input_types =
      expand_list_input_types list_type_definitions list_input_types
    in
    match cmd.cmd_desc with
    | M_ret _ -> list_input_types
    | M_bnd (cmd1, _, cmd2) ->
        let list_continuations = simulate acc cmd1 list_input_types in
        simulate acc cmd2 list_continuations
    | M_call (f_id, _) ->
        if detect_cycle_coverage_checking acc (f_id.txt, list_input_types) then
          (* If a cycle is detected, the currently explored execution path of
             the command has already been explored. So we simply return the empty
             list of continuations. *)
          []
        else
          let f_def =
            get_function_definition list_function_definitions f_id.txt
          in
          let acc_updated = (f_id.txt, list_input_types) :: acc in
          simulate acc_updated f_def list_input_types
    | M_sample_recv (_, channel_id) ->
        if String.equal old_channel_id channel_id.txt then
          List.map list_input_types ~f:(fun definition ->
              match definition with
              | Styv_conj (_, continuation) -> continuation
              | _ ->
                  Format.printf "Input type = %a\n" Ast_ops.print_sess_tyv
                    definition;
                  failwith "The given type is not of the form Styv_conj")
        else list_input_types
    | M_sample_send (_, channel_id) ->
        if String.equal old_channel_id channel_id.txt then
          List.map list_input_types ~f:(fun definition ->
              match definition with
              | Styv_imply (_, continuation) -> continuation
              | _ -> failwith "The given type is not of the form Styv_imply")
        else list_input_types
    | M_branch_recv (cmd1, cmd2, channel_id) ->
        if String.equal old_channel_id channel_id.txt then
          let list_first_branch_continuations =
            List.map list_input_types ~f:(fun definition ->
                match definition with
                | Styv_ichoice (s1, _) -> s1
                | _ -> failwith "The given type is not of the form Styv_ichoice")
          in
          (* We only enter the first branch because the second branch
             corresponds to the case where the previous subguide diverges from the
             current subiguide. *)
          simulate acc cmd1 list_first_branch_continuations
        else
          let list_input_types_branch_swapped =
            List.map list_input_types ~f:(fun definition ->
                match definition with
                | Styv_ichoice (s1, s2) -> Styv_ichoice (s2, s1)
                | _ ->
                    failwith
                      "Because the given type is not of the form Styv_ichoice, \
                       we cannot swap the two branches")
          in
          let result1 = simulate acc cmd1 list_input_types in
          let result2 = simulate acc cmd2 list_input_types_branch_swapped in
          List.dedup_and_sort (result1 @ result2) ~compare:compare_sess_tyv
    | M_branch_send _ -> failwith "A guide program cannot contain M_branch_send"
    | M_branch_self (_, cmd1, cmd2) ->
        let result1 = simulate acc cmd1 list_input_types in
        let result2 = simulate acc cmd2 list_input_types in
        result1 @ result2
    | M_loop (n, e, v_id, btyv, cmd) ->
        if n <= 0 then list_input_types
        else
          let intermediate_result = simulate acc cmd list_input_types in
          let decremented_cmd =
            { cmd with cmd_desc = M_loop (n - 1, e, v_id, btyv, cmd) }
          in
          simulate acc decremented_cmd intermediate_result
    | M_iter _ -> failwith "M_iter is not supported in coverage checking"
  in
  simulate [] cmd [ input_type ]

let coverage_check_prog prog type_name =
  let list_type_definitions = collect_type_definitions prog in
  let list_function_definitions = collect_function_definitions prog in
  let () =
    print_list_type_definitions Format.std_formatter list_type_definitions
  in
  let function_name = "Guide" in
  let function_def =
    List.Assoc.find_exn list_function_definitions ~equal:String.equal
      function_name
  in
  let list_continuations =
    simulate_type_with_command list_function_definitions list_type_definitions
      function_def "old"
      (Styv_var (type_name, Styv_one))
  in
  let () =
    List.iter list_continuations ~f:(fun definition ->
        Format.printf "Continuation = %a\n" Ast_ops.print_sess_tyv definition);
    print_endline "This is the main function for coverage checking"
  in
  Ok ()
