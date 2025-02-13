open Core
open Ast_types
open Ir_types

let genvar =
  let cnt = ref 0 in
  fun () ->
    let res = "_temp_" ^ Int.to_string !cnt in
    incr cnt;
    res

let rec normalize_exp exp cont =
  match exp.exp_desc with
  | E_var var_name -> cont (Either.first (AE_var var_name.txt))

  | E_triv -> cont (Either.first AE_triv)

  | E_bool b -> cont (Either.first (AE_bool b))

  | E_real f -> cont (Either.first (AE_real f))

  | E_nat n -> cont (Either.first (AE_nat n))

  | E_let (exp1, var_name, exp2) ->
    normalize_exp exp1 (fun nexp1 ->
        IE_let (nexp1, var_name.txt, normalize_exp exp2 cont)
      )

  | E_cond (exp0, exp1, exp2) ->
    normalize_exp_name exp0 (fun nexp0 ->
        cont (Either.second (CE_cond (nexp0, normalize_exp_term exp1, normalize_exp_term exp2)))
      )

  | E_abs (var_name, _, exp0) ->
    cont (Either.second (CE_abs (var_name.txt, normalize_exp_term exp0)))

  | E_app (exp1, exp2) ->
    normalize_exp_name exp1 (fun nexp1 ->
        normalize_exp_name exp2 (fun nexp2 ->
            cont (Either.second (CE_app (nexp1, nexp2)))
          )
      )

  | E_binop (bop, exp1, exp2) ->
    normalize_exp_name exp1 (fun nexp1 ->
        normalize_exp_name exp2 (fun nexp2 ->
            cont (Either.first (AE_binop (bop.txt, nexp1, nexp2)))
          )
      )

  | E_dist dist ->
    normalize_dist dist (fun ndist -> cont (Either.first (AE_dist ndist)))

  | E_tensor exp0 ->
    normalize_exp_name exp0 (fun nexp0 -> cont (Either.first (AE_tensor nexp0)))

  | E_stack exps ->
    let rec inner l c =
      match l with
      | [] -> c []
      | h :: t ->
        normalize_exp_name h (fun nh ->
            inner t (fun nt ->
                c (nh :: nt)
              )
          )
    in
    inner exps (fun nexps -> cont (Either.first (AE_stack nexps)))

  | E_index (base_exp, index_exps) ->
    normalize_exp_name base_exp (fun base_nexp ->
        let rec inner l c =
          match l with
          | [] -> c []
          | h :: t ->
            normalize_exp_name h (fun nh ->
                inner t (fun nt ->
                    c (nh :: nt)
                  )
              )
        in
        inner index_exps (fun index_nexps -> cont (Either.first (AE_index (base_nexp, index_nexps))))
      )

  | E_pair (exp1, exp2) ->
    normalize_exp_name exp1 (fun nexp1 ->
        normalize_exp_name exp2 (fun nexp2 ->
            cont (Either.first (AE_pair (nexp1, nexp2)))
          )
      )

  | E_field (exp0, field) ->
    normalize_exp_name exp0 (fun nexp0 ->
        cont (Either.first (AE_field (nexp0, field)))
      )

and normalize_dist dist cont =
  match dist with
  | D_ber exp ->
    normalize_exp_name exp (fun nexp ->
        cont (D_ber nexp)
      )
  | D_unif ->
    cont D_unif
  | D_beta (exp1, exp2) ->
    normalize_exp_name exp1 (fun nexp1 ->
        normalize_exp_name exp2 (fun nexp2 ->
            cont (D_beta (nexp1, nexp2))
          )
      )
  | D_gamma (exp1, exp2) ->
    normalize_exp_name exp1 (fun nexp1 ->
        normalize_exp_name exp2 (fun nexp2 ->
            cont (D_gamma (nexp1, nexp2))
          )
      )
  | D_normal (exp1, exp2) ->
    normalize_exp_name exp1 (fun nexp1 ->
        normalize_exp_name exp2 (fun nexp2 ->
            cont (D_normal (nexp1, nexp2))
          )
      )
  | D_cat exps ->
    let rec inner l c =
      match l with
      | [] -> c []
      | h :: t ->
        normalize_exp_name h (fun nh ->
            inner t (fun nt ->
                c (nh :: nt)
              )
          )
    in
    inner exps (fun nexps -> cont (D_cat nexps))
  | D_discrete exp ->
    normalize_exp_name exp (fun nexp ->
        cont (D_discrete nexp)
      )
  | D_bin (n, exp) ->
    normalize_exp_name exp (fun nexp ->
        cont (D_bin (n, nexp))
      )
  | D_geo exp ->
    normalize_exp_name exp (fun nexp ->
        cont (D_geo nexp)
      )
  | D_pois exp ->
    normalize_exp_name exp (fun nexp ->
        cont (D_pois nexp)
      )
  | D_same bty -> cont (D_same bty)

and normalize_exp_name exp cont =
  normalize_exp exp (fun nexp ->
      Either.value_map nexp
        ~first:(fun aexp -> cont aexp)
        ~second:(fun _ ->
            let var_name = genvar () in
            IE_let (nexp, var_name, cont (AE_var var_name))))

and normalize_exp_term exp =
  normalize_exp exp (fun nexp -> IE_tail nexp)

let rec normalize_cmd cmd cont =
  match cmd.cmd_desc with
  | M_ret exp ->
    normalize_exp exp cont

  | M_bnd (cmd1, var_name, cmd2) ->
    normalize_cmd cmd1 (fun nexp1 ->
        IE_let (nexp1, (match var_name with Some var_name -> var_name.txt | None -> genvar ()), normalize_cmd cmd2 cont)
      )

  | M_call (proc_name, exps) ->
    let rec inner l c =
      match l with
      | [] -> c []
      | h :: t ->
        normalize_exp_name h (fun nh ->
            inner t (fun nt ->
                c (nh :: nt)
              )
          )
    in
    inner exps (fun nexps -> cont (Either.second (CE_call (proc_name.txt, nexps))))

  | M_sample_recv (exp, channel_name) ->
    normalize_exp_name exp (fun nexp -> cont (Either.second (CE_sample_recv (nexp, channel_name.txt))))

  | M_sample_send (exp, channel_name) ->
    normalize_exp_name exp (fun nexp -> cont (Either.second (CE_sample_send (nexp, channel_name.txt))))

  | M_branch_recv (cmd1, cmd2, channel_name) ->
    cont (Either.second (CE_cond_recv (normalize_cmd_term cmd1, normalize_cmd_term cmd2, channel_name.txt)))

  | M_branch_send (exp0, cmd1, cmd2, channel_name) ->
    normalize_exp_name exp0 (fun nexp0 ->
        cont (Either.second (CE_cond_send (nexp0, normalize_cmd_term cmd1, normalize_cmd_term cmd2, channel_name.txt)))
      )

  | M_branch_self (exp0, cmd1, cmd2) ->
    normalize_exp_name exp0 (fun nexp0 ->
        cont (Either.second (CE_cond (nexp0, normalize_cmd_term cmd1, normalize_cmd_term cmd2)))
      )

  | M_loop (n, exp1, bind_name, _, cmd2) ->
    normalize_exp_name exp1 (fun nexp1 ->
        cont (Either.second (CE_loop (n, nexp1, bind_name.txt, normalize_cmd_term cmd2)))
      )

  | M_iter (exp1, exp2, iter_name, bind_name, _, cmd3) ->
    normalize_exp_name exp1 (fun nexp1 ->
        normalize_exp_name exp2 (fun nexp2 ->
            cont (Either.second (CE_iter (nexp1, nexp2, iter_name.txt, bind_name.txt, normalize_cmd_term cmd3)))
          )
      )

and normalize_cmd_term cmd =
  normalize_cmd cmd (fun nexp -> IE_tail nexp)

let normalize_proc_sig psig =
  { ipsig_params = List.map (List.append psig.psig_theta_tys psig.psig_param_tys) ~f:(fun (param_name, _) -> param_name.txt);
    ipsig_sess_left = Option.map psig.psig_sess_left ~f:(fun (channel_name, _) -> channel_name.txt);
    ipsig_sess_right = Option.map psig.psig_sess_right ~f:(fun (channel_name, _) -> channel_name.txt);
  }

let normalize_proc proc =
  { iproc_sig = normalize_proc_sig proc.proc_sig;
    iproc_body = normalize_cmd_term proc.proc_body;
  }

let normalize_prog prog =
  List.filter_map prog ~f:(function
      | Top_sess _ -> None
      | Top_proc (proc_name, proc) -> Some (proc_name.txt, normalize_proc proc)
      | Top_external _ -> None
      | Top_initial_type _ -> None
      | Top_guide_composition _ -> None
    )
