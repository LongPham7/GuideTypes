open Core
open Ast_types
open Guide_type_utility
open Or_error.Let_syntax

exception Type_error of string * Location.t

let is_prim_numeric = function
  | Pty_ureal | Pty_preal | Pty_real | Pty_fnat _ | Pty_nat -> true
  | _ -> false

let is_prim_subtype pty1 pty2 =
  match (pty1, pty2) with
  | Pty_unit, Pty_unit -> true
  | Pty_bool, Pty_bool -> true
  | Pty_ureal, Pty_ureal | Pty_ureal, Pty_preal | Pty_ureal, Pty_real -> true
  | Pty_preal, Pty_preal | Pty_preal, Pty_real -> true
  | Pty_real, Pty_real -> true
  | Pty_fnat n, Pty_fnat m -> n <= m
  | Pty_fnat _, Pty_nat -> true
  | Pty_fnat n, Pty_ureal -> n <= 2
  | Pty_fnat _, Pty_preal | Pty_fnat _, Pty_real -> true
  | Pty_nat, Pty_nat | Pty_nat, Pty_preal | Pty_nat, Pty_real -> true
  | _ -> false

let rec is_subtype tyv1 tyv2 =
  match (tyv1, tyv2) with
  | Btyv_prim pty1, Btyv_prim pty2 -> is_prim_subtype pty1 pty2
  | Btyv_prim_uncovered pty1, Btyv_prim_uncovered pty2 ->
      is_prim_subtype pty1 pty2
  | Btyv_prim pty1, Btyv_prim_uncovered pty2 -> is_prim_subtype pty1 pty2
  | Btyv_dist tyv1', Btyv_dist tyv2' -> equal_base_tyv tyv1' tyv2'
  | Btyv_arrow (tyv11, tyv12), Btyv_arrow (tyv21, tyv22) ->
      is_subtype tyv21 tyv11 && is_subtype tyv12 tyv22
  | Btyv_tensor (pty1, dims1), Btyv_tensor (pty2, dims2)
    when Poly.(dims1 = dims2) ->
      is_prim_subtype pty1 pty2
  | Btyv_tensor_uncovered (pty1, dims1), Btyv_tensor_uncovered (pty2, dims2)
    when Poly.(dims1 = dims2) ->
      is_prim_subtype pty1 pty2
  | Btyv_tensor (pty1, dims1), Btyv_tensor_uncovered (pty2, dims2)
    when Poly.(dims1 = dims2) ->
      is_prim_subtype pty1 pty2
  | Btyv_simplex n1, Btyv_simplex n2 when n1 = n2 -> true
  | Btyv_simplex_uncovered n1, Btyv_simplex_uncovered n2 when n1 = n2 -> true
  | Btyv_simplex n1, Btyv_simplex_uncovered n2 when n1 = n2 -> true
  | Btyv_simplex n1, Btyv_tensor (pty2, dims2) when Poly.([ n1 ] = dims2) ->
      is_prim_subtype Pty_ureal pty2
  | Btyv_tensor (pty1, dims1), Btyv_simplex n2 when Poly.(dims1 = [ n2 ]) ->
      is_prim_subtype pty1 Pty_ureal
  | Btyv_external name1, Btyv_external name2 -> String.(name1 = name2)
  | Btyv_product (tyv11, tyv12), Btyv_product (tyv21, tyv22) ->
      is_subtype tyv11 tyv21 && is_subtype tyv12 tyv22
  | _ -> false

let join_prim ~loc pty1 pty2 =
  if is_prim_subtype pty1 pty2 then Ok pty2
  else if is_prim_subtype pty2 pty1 then Ok pty1
  else Or_error.of_exn (Type_error ("join error", loc))

let meet_prim ~loc pty1 pty2 =
  if is_prim_subtype pty1 pty2 then Ok pty1
  else if is_prim_subtype pty2 pty1 then Ok pty2
  else Or_error.of_exn (Type_error ("meet error", loc))

let rec join_type ~loc tyv1 tyv2 =
  match (tyv1, tyv2) with
  | Btyv_prim pty1, Btyv_prim pty2 ->
      let%bind pty = join_prim ~loc pty1 pty2 in
      Ok (Btyv_prim pty)
  | Btyv_dist tyv1', Btyv_dist tyv2' ->
      if Ast_ops.equal_base_tyv_modulo_coverage tyv1' tyv2' then
        Ok (Btyv_dist (Ast_ops.join_base_tyv_modulo_coverage tyv1' tyv2'))
      else Or_error.of_exn (Type_error ("join error", loc))
  | Btyv_arrow (tyv11, tyv12), Btyv_arrow (tyv21, tyv22) ->
      let%bind tyv1' = meet_type ~loc tyv11 tyv21 in
      let%bind tyv2' = join_type ~loc tyv12 tyv22 in
      Ok (Btyv_arrow (tyv1', tyv2'))
  | Btyv_tensor (pty1, dims1), Btyv_tensor (pty2, dims2)
    when Poly.(dims1 = dims2) ->
      let%bind pty = join_prim ~loc pty1 pty2 in
      Ok (Btyv_tensor (pty, dims1))
  | Btyv_simplex n1, Btyv_simplex n2 when n1 = n2 -> Ok (Btyv_simplex n1)
  | Btyv_simplex n1, Btyv_tensor (pty2, dims2) when Poly.([ n1 ] = dims2) ->
      let%bind pty = join_prim ~loc Pty_ureal pty2 in
      Ok (Btyv_tensor (pty, [ n1 ]))
  | Btyv_tensor (pty1, dims1), Btyv_simplex n2 when Poly.(dims1 = [ n2 ]) ->
      let%bind pty = join_prim ~loc pty1 Pty_ureal in
      Ok (Btyv_tensor (pty, dims1))
  | Btyv_external name1, Btyv_external name2 when String.(name1 = name2) ->
      Ok (Btyv_external name1)
  | Btyv_product (tyv11, tyv12), Btyv_product (tyv21, tyv22) ->
      let%bind tyv1' = join_type ~loc tyv11 tyv21 in
      let%bind tyv2' = join_type ~loc tyv12 tyv22 in
      Ok (Btyv_product (tyv1', tyv2'))
  | _ -> Or_error.of_exn (Type_error ("join error", loc))

and meet_type ~loc tyv1 tyv2 =
  match (tyv1, tyv2) with
  | Btyv_prim pty1, Btyv_prim pty2 ->
      let%bind pty = meet_prim ~loc pty1 pty2 in
      Ok (Btyv_prim pty)
  | Btyv_dist tyv1', Btyv_dist tyv2' ->
      if equal_base_tyv tyv1' tyv2' then Ok (Btyv_dist tyv1')
      else Or_error.of_exn (Type_error ("meet error", loc))
  | Btyv_arrow (tyv11, tyv12), Btyv_arrow (tyv21, tyv22) ->
      let%bind tyv1' = join_type ~loc tyv11 tyv21 in
      let%bind tyv2' = meet_type ~loc tyv12 tyv22 in
      Ok (Btyv_arrow (tyv1', tyv2'))
  | Btyv_tensor (pty1, dims1), Btyv_tensor (pty2, dims2)
    when Poly.(dims1 = dims2) ->
      let%bind pty = meet_prim ~loc pty1 pty2 in
      Ok (Btyv_tensor (pty, dims1))
  | Btyv_simplex n1, Btyv_simplex n2 when n1 = n2 -> Ok (Btyv_simplex n1)
  | Btyv_simplex n1, Btyv_tensor (pty2, dims2) when Poly.([ n1 ] = dims2) ->
      let%bind pty = meet_prim ~loc Pty_ureal pty2 in
      Ok (Btyv_tensor (pty, [ n1 ]))
  | Btyv_tensor (pty1, dims1), Btyv_simplex n2 when Poly.(dims1 = [ n2 ]) ->
      let%bind pty = meet_prim ~loc pty1 Pty_ureal in
      Ok (Btyv_tensor (pty, dims1))
  | Btyv_external name1, Btyv_external name2 when String.(name1 = name2) ->
      Ok (Btyv_external name1)
  | Btyv_product (tyv11, tyv12), Btyv_product (tyv21, tyv22) ->
      let%bind tyv1' = meet_type ~loc tyv11 tyv21 in
      let%bind tyv2' = meet_type ~loc tyv12 tyv22 in
      Ok (Btyv_product (tyv1', tyv2'))
  | _ -> Or_error.of_exn (Type_error ("meet error", loc))

let tycheck_bop_prim bop pty1 pty2 =
  match (bop.txt, pty1, pty2) with
  | Bop_add, Pty_ureal, Pty_ureal | Bop_add, Pty_ureal, Pty_preal ->
      Ok Pty_preal
  | Bop_add, Pty_ureal, Pty_real -> Ok Pty_real
  | Bop_add, Pty_preal, Pty_ureal | Bop_add, Pty_preal, Pty_preal ->
      Ok Pty_preal
  | Bop_add, Pty_preal, Pty_real -> Ok Pty_real
  | Bop_add, Pty_real, Pty_ureal
  | Bop_add, Pty_real, Pty_preal
  | Bop_add, Pty_real, Pty_real ->
      Ok Pty_real
  | Bop_add, Pty_fnat n, Pty_fnat m -> Ok (Pty_fnat (n + m))
  | Bop_add, Pty_fnat _, Pty_nat -> Ok Pty_nat
  | Bop_add, Pty_nat, Pty_fnat _ | Bop_add, Pty_nat, Pty_nat -> Ok Pty_nat
  | Bop_sub, Pty_ureal, Pty_ureal
  | Bop_sub, Pty_ureal, Pty_preal
  | Bop_sub, Pty_ureal, Pty_real ->
      Ok Pty_real
  | Bop_sub, Pty_preal, Pty_ureal
  | Bop_sub, Pty_preal, Pty_preal
  | Bop_sub, Pty_preal, Pty_real ->
      Ok Pty_real
  | Bop_sub, Pty_real, Pty_ureal
  | Bop_sub, Pty_real, Pty_preal
  | Bop_sub, Pty_real, Pty_real ->
      Ok Pty_real
  | Bop_mul, Pty_ureal, Pty_ureal -> Ok Pty_ureal
  | Bop_mul, Pty_ureal, Pty_preal -> Ok Pty_preal
  | Bop_mul, Pty_ureal, Pty_real -> Ok Pty_real
  | Bop_mul, Pty_preal, Pty_ureal | Bop_mul, Pty_preal, Pty_preal ->
      Ok Pty_preal
  | Bop_mul, Pty_preal, Pty_real -> Ok Pty_real
  | Bop_mul, Pty_real, Pty_ureal
  | Bop_mul, Pty_real, Pty_preal
  | Bop_mul, Pty_real, Pty_real ->
      Ok Pty_real
  | Bop_mul, Pty_fnat n, Pty_fnat m -> Ok (Pty_fnat (n * m))
  | Bop_mul, Pty_fnat _, Pty_nat -> Ok Pty_nat
  | Bop_mul, Pty_nat, Pty_fnat _ | Bop_mul, Pty_nat, Pty_nat -> Ok Pty_nat
  | Bop_div, Pty_ureal, Pty_ureal | Bop_div, Pty_ureal, Pty_preal ->
      Ok Pty_preal
  | Bop_div, Pty_ureal, Pty_real -> Ok Pty_real
  | Bop_div, Pty_preal, Pty_ureal | Bop_div, Pty_preal, Pty_preal ->
      Ok Pty_preal
  | Bop_div, Pty_preal, Pty_real -> Ok Pty_real
  | Bop_div, Pty_real, Pty_ureal
  | Bop_div, Pty_real, Pty_preal
  | Bop_div, Pty_real, Pty_real ->
      Ok Pty_real
  | (Bop_eq, pty1, pty2 | Bop_ne, pty1, pty2)
    when is_prim_subtype pty1 pty2 || is_prim_subtype pty2 pty1 ->
      Ok Pty_bool
  | Bop_lt, pty1, pty2
  | Bop_le, pty1, pty2
  | Bop_gt, pty1, pty2
  | Bop_ge, pty1, pty2
    when is_prim_numeric pty1
         && (is_prim_subtype pty1 pty2 || is_prim_subtype pty2 pty1) ->
      Ok Pty_bool
  | Bop_and, Pty_bool, Pty_bool | Bop_or, Pty_bool, Pty_bool -> Ok Pty_bool
  | _ -> Or_error.of_exn (Type_error ("mismatched operand types", bop.loc))

let tycheck_bop bop arg1 arg2 =
  match (arg1, arg2) with
  | Btyv_prim pty1, Btyv_prim pty2 ->
      let%bind res = tycheck_bop_prim bop pty1 pty2 in
      Ok (Btyv_prim res)
  | Btyv_tensor (pty1, dims1), Btyv_tensor (pty2, dims2)
    when Poly.(dims1 = dims2) ->
      let%bind res = tycheck_bop_prim bop pty1 pty2 in
      Ok (Btyv_tensor (res, dims1))
  | Btyv_simplex n1, Btyv_simplex n2 when n1 = n2 ->
      Ok (Btyv_tensor (Pty_preal, [ n1 ]))
  | Btyv_simplex n1, Btyv_tensor (pty2, dims2) when Poly.([ n1 ] = dims2) ->
      let%bind pty = tycheck_bop_prim bop Pty_ureal pty2 in
      Ok (Btyv_tensor (pty, [ n1 ]))
  | Btyv_tensor (pty1, dims1), Btyv_simplex n2 when Poly.(dims1 = [ n2 ]) ->
      let%bind pty = tycheck_bop_prim bop pty1 Pty_ureal in
      Ok (Btyv_tensor (pty, dims1))
  | _ -> Or_error.of_exn (Type_error ("mismatched operand types", bop.loc))

let rec tycheck_exp ctxt exp =
  match exp.exp_desc with
  | E_var var_name -> (
      match Map.find ctxt var_name.txt with
      | Some tyv -> Ok tyv
      | None ->
          print_endline "ctxt in function tycheck_exp:";
          Map.iteri ctxt ~f:(fun ~key ~data ->
              Format.printf "(var, type) = (%s, %a)\n" key
                Ast_ops.print_base_tyv data);
          Or_error.of_exn
            (Type_error ("undefined variable " ^ var_name.txt, exp.exp_loc)))
  | E_triv -> Ok (Btyv_prim Pty_unit)
  | E_bool _ -> Ok (Btyv_prim Pty_bool)
  | E_cond (exp0, exp1, exp2) ->
      let%bind tyv0 = tycheck_exp ctxt exp0 in
      if is_subtype tyv0 (Btyv_prim Pty_bool) then
        let%bind tyv1 = tycheck_exp ctxt exp1 in
        let%bind tyv2 = tycheck_exp ctxt exp2 in
        join_type ~loc:exp.exp_loc tyv1 tyv2
      else
        Or_error.of_exn
          (Type_error ("non-boolean condition type", exp0.exp_loc))
  | E_real r ->
      if Float.(r >= 0. && r <= 1.) then Ok (Btyv_prim Pty_ureal)
      else if Float.(r >= 0.) then Ok (Btyv_prim Pty_preal)
      else Ok (Btyv_prim Pty_real)
  | E_nat n ->
      if n >= 0 then Ok (Btyv_prim (Pty_fnat (n + 1)))
      else Or_error.of_exn (Type_error ("negative integers", exp.exp_loc))
  | E_binop (bop, exp1, exp2) ->
      let%bind tyv1 = tycheck_exp ctxt exp1 in
      let%bind tyv2 = tycheck_exp ctxt exp2 in
      tycheck_bop bop tyv1 tyv2
  | E_abs (var_name, ty, exp0) ->
      let tyv = eval_ty ty in
      let%bind tyv0 =
        tycheck_exp (Map.set ctxt ~key:var_name.txt ~data:tyv) exp0
      in
      Ok (Btyv_arrow (tyv, tyv0))
  | E_app (exp1, exp2) -> (
      let%bind tyv1 = tycheck_exp ctxt exp1 in
      let%bind tyv2 = tycheck_exp ctxt exp2 in
      match tyv1 with
      | Btyv_arrow (tyv11, tyv12) ->
          if is_subtype tyv2 tyv11 then Ok tyv12
          else
            Or_error.of_exn
              (Type_error ("mismatched argument types in E_app", exp2.exp_loc))
      | _ ->
          Or_error.of_exn (Type_error ("non-arrow function type", exp.exp_loc)))
  | E_let (exp1, var_name, exp2) ->
      let%bind tyv1 = tycheck_exp ctxt exp1 in
      let%bind ctxt' =
        Or_error.try_with (fun () ->
            Map.add_exn ctxt ~key:var_name.txt ~data:tyv1)
      in
      tycheck_exp ctxt' exp2
  | E_dist dist ->
      let%bind tyv = tycheck_dist ~loc:exp.exp_loc ctxt dist in
      Ok (Btyv_dist tyv)
  | E_tensor exp0 -> (
      let%bind tyv0 = tycheck_exp ctxt exp0 in
      match tyv0 with
      | Btyv_prim pty -> Ok (Btyv_tensor (pty, []))
      | _ ->
          Or_error.of_exn
            (Type_error ("non-primitive element type", exp0.exp_loc)))
  | E_stack exps ->
      let n = List.length exps in
      let%bind ptys =
        List.fold_result exps ~init:[] ~f:(fun acc exp ->
            let%bind tyv = tycheck_exp ctxt exp in
            match tyv with
            | Btyv_tensor (pty, dims) -> Ok ((pty, dims) :: acc)
            | _ -> Or_error.of_exn (Type_error ("non-tensor type", exp.exp_loc)))
      in
      let pty, dims = List.hd_exn ptys in
      let%bind join_pty =
        List.fold_result ptys ~init:pty ~f:(fun acc (pty', dims') ->
            if Poly.(dims = dims') then join_prim ~loc:exp.exp_loc acc pty'
            else Or_error.of_exn (Type_error ("not stackable", exp.exp_loc)))
      in
      Ok (Btyv_tensor (join_pty, n :: dims))
  | E_index (base_exp, index_exps) -> (
      let%bind base_tyv = tycheck_exp ctxt base_exp in
      match base_tyv with
      | Btyv_tensor (pty, dims) ->
          if List.length dims <> List.length index_exps then
            Or_error.of_exn (Type_error ("mismatched dimension", exp.exp_loc))
          else
            let%bind () =
              List.fold_result (List.zip_exn dims index_exps) ~init:()
                ~f:(fun () (dim, index_exp) ->
                  let%bind index_tyv = tycheck_exp ctxt index_exp in
                  match index_tyv with
                  | Btyv_prim pty when is_prim_subtype pty (Pty_fnat dim) ->
                      Ok ()
                  | _ ->
                      Or_error.of_exn
                        (Type_error ("invalid index", index_exp.exp_loc)))
            in
            Ok (Btyv_prim pty)
      | _ -> Or_error.of_exn (Type_error ("not indexable", base_exp.exp_loc)))
  | E_pair (exp1, exp2) ->
      let%bind tyv1 = tycheck_exp ctxt exp1 in
      let%bind tyv2 = tycheck_exp ctxt exp2 in
      Ok (Btyv_product (tyv1, tyv2))
  | E_field (exp0, field) -> (
      let%bind tyv0 = tycheck_exp ctxt exp0 in
      match tyv0 with
      | Btyv_product (tyv1, tyv2) ->
          if field = 0 then Ok tyv1
          else if field = 1 then Ok tyv2
          else Or_error.of_exn (Type_error ("invalid field", exp.exp_loc))
      | _ ->
          Or_error.of_exn (Type_error ("non-projectable value", exp0.exp_loc)))

and tycheck_dist ~loc ctxt dist =
  let lift tars goal curs =
    let tcs = List.zip_exn tars curs in
    let%bind res =
      List.fold_result tcs ~init:None ~f:(fun acc (tar, cur) ->
          match cur with
          | Btyv_prim pty when is_prim_subtype pty tar -> (
              match acc with
              | None -> Ok (Some None)
              | Some None -> Ok (Some None)
              | _ ->
                  Or_error.of_exn
                    (Type_error ("mixed tensors and scalars", loc)))
          | Btyv_tensor (pty, dims) when is_prim_subtype pty tar -> (
              match acc with
              | None -> Ok (Some (Some dims))
              | Some None ->
                  Or_error.of_exn
                    (Type_error ("mixed tensors and scalars", loc))
              | Some (Some dims') ->
                  if Poly.(dims = dims') then Ok (Some (Some dims))
                  else
                    Or_error.of_exn
                      (Type_error ("inconsistent tensor dims", loc)))
          | _ ->
              Or_error.of_exn (Type_error ("mismatched parameter types", loc)))
    in
    let res = Option.value_exn res in
    match res with
    | None -> Ok (Btyv_prim goal)
    | Some dims -> Ok (Btyv_tensor (goal, dims))
  in

  match dist with
  | D_ber exp ->
      let%bind tyv = tycheck_exp ctxt exp in
      lift [ Pty_ureal ] Pty_bool [ tyv ]
  | D_unif -> Ok (Btyv_prim Pty_ureal)
  | D_beta (exp1, exp2) ->
      let%bind tyv1 = tycheck_exp ctxt exp1 in
      let%bind tyv2 = tycheck_exp ctxt exp2 in
      lift [ Pty_preal; Pty_preal ] Pty_ureal [ tyv1; tyv2 ]
  | D_gamma (exp1, exp2) ->
      let%bind tyv1 = tycheck_exp ctxt exp1 in
      let%bind tyv2 = tycheck_exp ctxt exp2 in
      lift [ Pty_preal; Pty_preal ] Pty_preal [ tyv1; tyv2 ]
  | D_normal (exp1, exp2) ->
      let%bind tyv1 = tycheck_exp ctxt exp1 in
      let%bind tyv2 = tycheck_exp ctxt exp2 in
      lift [ Pty_real; Pty_preal ] Pty_real [ tyv1; tyv2 ]
  | D_cat exps ->
      let n = List.length exps in
      let%bind () =
        List.fold_result exps ~init:() ~f:(fun () exp ->
            let%bind tyv = tycheck_exp ctxt exp in
            if is_subtype tyv (Btyv_prim Pty_preal) then Ok ()
            else
              Or_error.of_exn (Type_error ("mismatched parameter types", loc)))
      in
      Ok (Btyv_prim (Pty_fnat n))
  | D_discrete exp -> (
      let%bind tyv = tycheck_exp ctxt exp in
      match tyv with
      | Btyv_simplex n -> Ok (Btyv_prim (Pty_fnat n))
      | _ -> Or_error.of_exn (Type_error ("mismatched parameter types", loc)))
  | D_bin (n, exp) ->
      let%bind tyv = tycheck_exp ctxt exp in
      lift [ Pty_ureal ] (Pty_fnat n) [ tyv ]
  | D_geo exp ->
      let%bind tyv = tycheck_exp ctxt exp in
      lift [ Pty_ureal ] Pty_nat [ tyv ]
  | D_pois exp ->
      let%bind tyv = tycheck_exp ctxt exp in
      lift [ Pty_preal ] Pty_nat [ tyv ]
  | D_same bty -> (
      match bty with
      | Btyv_prim pty -> Ok (Btyv_prim_uncovered pty)
      | Btyv_tensor (pty, dims) -> Ok (Btyv_tensor_uncovered (pty, dims))
      | Btyv_simplex n -> Ok (Btyv_simplex_uncovered n)
      | _ ->
          Or_error.of_exn
            (Invalid_argument "D_same applied to an invalid base type"))

let collect_sess_tys prog =
  Hashtbl.of_alist_or_error
    (module String)
    (List.filter_map prog ~f:(fun top ->
         match top with
         | Top_proc _ -> None
         | Top_sess (type_name, sty) ->
             Some (type_name.txt, Option.map ~f:eval_sty sty)
         | Top_external _ -> None
         | Top_initial_type _ -> None
         | Top_guide_composition _ -> None))

let channel_direction_is_left dir =
  match dir with `Left -> true | `Right -> false

(* We have two branches for a message (i.e., branch selection) from the
   model and another two branches for a branch selection in the old trace.
   Therefore, we have a total of four branches/cases. The first case is
   where both the current and previous subguides choose the first branch.
   The second case is where the current subguide chooses the first branch,
   but the previous subguide chooses the second branch. The third case is
   where both subguides choose the second branch. Lastly, the fourth case
   is where the current subguide chooses the second branch, but the
   previous subguide chooses the first branch.

   An advantage of this design is that, during type inference, when we merge two
   guide types from the first and second (or the third and fourth) cases, it is
   easy to tell which of the two branches is for the case where both the current
   and previous subguides are present. A drawback is that, when we simulate a
   command with a guide type during coverage checking, a problem arises. For
   instance, suppose we want to simulate a command with a guide type T = +{ A1 |
   A2 } for some guide types A1 and A2. We first receive a branch selection from
   the model and then receive a branch selection from the previous subguide.
   Hence, type A1 corresponds to the first branch if we enter the first branch
   selection from model. However, if we enter the second branch selection from
   the model, A1 corresponds to the second branch. Therefore, which inner branch
   (i.e., a branch selection from the previous subguide) corresponds to A1
   depends on which outer branch (i.e., branch selection from the model) we
   enter. This makes the coverage checking challenging. *)

let merge_session_types_outer_conditional_branches styv1 styv2 =
  (* For debugging *)
  (* let () =
       Format.printf
         "Merge two session types across branches of the outer conditional \
          statement: styv1 = %a, styv2 = %a\n"
         Ast_ops.print_sess_tyv styv1 Ast_ops.print_sess_tyv styv2
     in *)
  match (styv1, styv2) with
  | Styv_ichoice (s1, _), Styv_ichoice (s2, _) ->
      (* assert (equal_sess_tyv t1 Styv_one && equal_sess_tyv t2 Styv_one); *)
      Some (`Left, Styv_ichoice (s1, s2), [])
  | _, _ ->
      failwith
        (Format.asprintf
           "The two session types %a and %a don't have internal choice"
           Ast_ops.print_sess_tyv styv1 Ast_ops.print_sess_tyv styv2)

let forward_wrapper psig_ctxt =
  let rec forward ctxt cmd =
    match cmd.cmd_desc with
    | M_ret exp -> tycheck_exp ctxt exp
    | M_bnd (cmd1, var_name, cmd2) ->
        let%bind tyv1 = forward ctxt cmd1 in
        let%bind ctxt' =
          Or_error.try_with (fun () ->
              match var_name with
              | None -> ctxt
              | Some var_name -> Map.add_exn ctxt ~key:var_name.txt ~data:tyv1)
        in
        forward ctxt' cmd2
    | M_call (proc_name, exps) -> (
        match Map.find psig_ctxt proc_name.txt with
        | None ->
            Or_error.of_exn
              (Type_error ("unknown procedure " ^ proc_name.txt, proc_name.loc))
        | Some psigv ->
            if List.length psigv.psigv_param_tys <> List.length exps then
              Or_error.of_exn (Type_error ("mismatched arity", cmd.cmd_loc))
            else
              let%bind tyvs =
                List.fold_result (List.rev exps) ~init:[] ~f:(fun acc exp ->
                    let%bind tyv = tycheck_exp ctxt exp in
                    Ok (tyv :: acc))
              in
              if
                not
                  (List.for_all2_exn tyvs psigv.psigv_param_tys
                     ~f:(fun tyv (_, tyv') -> is_subtype tyv tyv'))
              then
                Or_error.of_exn
                  (Type_error
                     ("mismatched argument types in M_call", cmd.cmd_loc))
              else Ok psigv.psigv_ret_ty)
    | M_sample_recv (exp, _) | M_sample_send (exp, _) -> (
        let%bind tyv = tycheck_exp ctxt exp in
        match tyv with
        | Btyv_dist tyv0 ->
            let _, tyv0_covered, _ =
              get_covered_and_uncovered_distribution_base_types tyv0
            in
            Ok tyv0_covered
        | _ ->
            Or_error.of_exn (Type_error ("non-distribution types", exp.exp_loc))
        )
    | M_branch_recv (cmd1, cmd2, _) ->
        let%bind tyv1 = forward ctxt cmd1 in
        let%bind tyv2 = forward ctxt cmd2 in
        join_type ~loc:cmd.cmd_loc tyv1 tyv2
    | M_branch_send (exp, cmd1, cmd2, _) | M_branch_self (exp, cmd1, cmd2) -> (
        let%bind tyv = tycheck_exp ctxt exp in
        match tyv with
        | Btyv_prim Pty_bool ->
            let%bind tyv1 = forward ctxt cmd1 in
            let%bind tyv2 = forward ctxt cmd2 in
            join_type ~loc:cmd.cmd_loc tyv1 tyv2
        | _ ->
            Or_error.of_exn
              (Type_error ("non-boolean condition type", exp.exp_loc)))
    | M_loop (_, init_exp, bind_name, bind_ty, cmd0) ->
        let%bind tyv = tycheck_exp ctxt init_exp in
        let bind_tyv = eval_ty bind_ty in
        if is_subtype tyv bind_tyv then
          let ctxt' = Map.set ctxt ~key:bind_name.txt ~data:bind_tyv in
          let%bind tyv' = forward ctxt' cmd0 in
          if is_subtype tyv' bind_tyv then Ok bind_tyv
          else
            Or_error.of_exn
              (Type_error ("inconsistent result type in loop", cmd0.cmd_loc))
        else
          Or_error.of_exn
            (Type_error ("inconsistent initial value for loop", init_exp.exp_loc))
    | M_iter (iter_exp, init_exp, iter_name, bind_name, bind_ty, cmd0) -> (
        let%bind iter_tyv = tycheck_exp ctxt iter_exp in
        match iter_tyv with
        | Btyv_tensor (pty, dims) when List.length dims > 0 ->
            let elem_tyv = Btyv_tensor (pty, List.tl_exn dims) in
            let%bind init_tyv = tycheck_exp ctxt init_exp in
            let bind_tyv = eval_ty bind_ty in
            if is_subtype init_tyv bind_tyv then
              let ctxt' = Map.set ctxt ~key:iter_name.txt ~data:elem_tyv in
              let ctxt'' = Map.set ctxt' ~key:bind_name.txt ~data:bind_tyv in
              let%bind tyv' = forward ctxt'' cmd0 in
              if is_subtype tyv' bind_tyv then Ok bind_tyv
              else
                Or_error.of_exn
                  (Type_error ("inconsistent result type in iter", cmd0.cmd_loc))
            else
              Or_error.of_exn
                (Type_error
                   ("inconsistent initial value for iter", init_exp.exp_loc))
        | _ -> Or_error.of_exn (Type_error ("not iterable", iter_exp.exp_loc)))
  in
  forward

let tycheck_cmd psig_ctxt =
  let rec backward ~access_to_old_trace ctxt sess_and_acc_sess_eq_constrs cmd =
    let sess, acc_sess_eq_constrs = sess_and_acc_sess_eq_constrs in
    match cmd.cmd_desc with
    | M_ret _ -> Ok sess_and_acc_sess_eq_constrs
    | M_bnd (cmd1, var_name, cmd2) ->
        let%bind tyv1 = forward_wrapper psig_ctxt ctxt cmd1 in
        let%bind ctxt' =
          Or_error.try_with (fun () ->
              match var_name with
              | None -> ctxt
              | Some var_name -> Map.add_exn ctxt ~key:var_name.txt ~data:tyv1)
        in
        let%bind sess_and_acc' =
          backward ~access_to_old_trace ctxt' sess_and_acc_sess_eq_constrs cmd2
        in
        backward ~access_to_old_trace ctxt sess_and_acc' cmd1
    | M_sample_recv (_, channel_name) -> (
        let%bind tyv = forward_wrapper psig_ctxt ctxt cmd in
        match Map.find sess channel_name.txt with
        | None ->
            Or_error.of_exn
              (Type_error
                 ("unknown channel " ^ channel_name.txt, channel_name.loc))
        | Some (`Left, sty) ->
            Ok
              ( Map.set sess ~key:channel_name.txt
                  ~data:(`Left, Styv_conj (tyv, sty)),
                acc_sess_eq_constrs )
        | Some (`Right, sty) ->
            Ok
              ( Map.set sess ~key:channel_name.txt
                  ~data:(`Right, Styv_imply (tyv, sty)),
                acc_sess_eq_constrs ))
    | M_sample_send (_, channel_name) -> (
        let%bind tyv = forward_wrapper psig_ctxt ctxt cmd in
        match Map.find sess channel_name.txt with
        | None ->
            Or_error.of_exn
              (Type_error
                 ("unknown channel " ^ channel_name.txt, channel_name.loc))
        | Some (`Left, sty) ->
            Ok
              ( Map.set sess ~key:channel_name.txt
                  ~data:(`Left, Styv_imply (tyv, sty)),
                acc_sess_eq_constrs )
        | Some (`Right, sty) ->
            Ok
              ( Map.set sess ~key:channel_name.txt
                  ~data:(`Right, Styv_conj (tyv, sty)),
                acc_sess_eq_constrs ))
    | M_branch_recv (cmd1, cmd2, channel_name) ->
        let%bind sess1, acc_sess_eq_constrs1 =
          backward ~access_to_old_trace ctxt sess_and_acc_sess_eq_constrs cmd1
        in
        let%bind sess2, acc_sess_eq_constrs2 =
          (* If we are in the second branch of the channel for the old trace,
             this branch has no access to the old trace. Hence, we set the flag
             access_to_old_trace to false. *)
          if String.equal channel_name.txt "old" then
            backward ~access_to_old_trace:false ctxt
              sess_and_acc_sess_eq_constrs cmd2
          else
            backward ~access_to_old_trace ctxt sess_and_acc_sess_eq_constrs cmd2
        in
        let merge_result =
          Map.merge sess1 sess2 ~f:(fun ~key -> function
            | `Left _ | `Right _ -> assert false
            | `Both ((dir1, styv1), (_, styv2)) ->
                if String.(key = channel_name.txt) then
                  match dir1 with
                  | `Left -> Some (`Left, Styv_ichoice (styv1, styv2), [])
                  | `Right -> Some (`Right, Styv_echoice (styv1, styv2), [])
                else if access_to_old_trace then
                  if
                    (* This is the outer layer of the double-nested conditional
                       statement in the presence of the old channel. The current
                       channel should be the one between the guide and model. *)
                    String.(key = "old")
                    && channel_direction_is_left dir1
                    && String.(channel_name.txt <> "old")
                  then
                    merge_session_types_outer_conditional_branches styv1 styv2
                  else if
                    (* This is the inner layer of the double-nested conditional
                       statement in the presence of the old channel. *)
                    String.(key <> "old")
                    && (not (channel_direction_is_left dir1))
                    && String.(channel_name.txt = "old")
                    (* We return the first session type because it corresponds
                       to the branch where both channels (i.e., the channel
                       between the current subguide and the model and another
                       channel for the previous trace) are present. Put
                       differently, the first session type is for the case where
                       both the current and previous subguides choose the same
                       branch.

                       Therefore, styv1 may contain uncovered random variables.
                       On the other hand, styv2 must be free of uncovered random
                       variables - it must draw fresh samples for all random
                       variables. Hence, when we merge styv1 and styv2, the
                       result must be styv1, provided that they are equivalent
                       modulo coverage (i.e., they are bisimilar to each other
                       if we ignore covered and uncovered random variables). To
                       check that styv1 and styv2 are indeed equivalent modulo
                       coverage, we store them in an output list. This list of
                       session-type pairs will be aggregated and will be checked
                       for equivalence later. *)
                  then Some (dir1, styv1, [ (styv1, styv2) ])
                  else
                    (* For debugging *)
                    let () =
                      Format.printf "styv1 = %a, styv2 = %a\n"
                        Ast_ops.print_sess_tyv styv1 Ast_ops.print_sess_tyv
                        styv2
                    in
                    raise
                      (Type_error
                         ( "Because the old trace is accessible, we must have \
                            a conditional statement on the old channel",
                           cmd.cmd_loc ))
                else (
                  assert (String.(channel_name.txt <> "old"));
                  Some (dir1, styv1, [ (styv1, styv2) ])))
        in
        let new_sess_eqs =
          merge_result |> Map.data
          |> List.map ~f:(fun (_, _, z) -> z)
          |> List.concat
        in
        let merge_type_only =
          Map.map merge_result ~f:(fun (x, y, _) -> (x, y))
        in
        Or_error.try_with (fun () ->
            ( merge_type_only,
              new_sess_eqs @ acc_sess_eq_constrs1 @ acc_sess_eq_constrs2 ))
    | M_branch_send (_, cmd1, cmd2, channel_name) ->
        let%bind sess1, acc_sess_eq_constrs1 =
          backward ~access_to_old_trace ctxt sess_and_acc_sess_eq_constrs cmd1
        in
        let%bind sess2, acc_sess_eq_constrs2 =
          backward ~access_to_old_trace ctxt sess_and_acc_sess_eq_constrs cmd2
        in
        Or_error.try_with (fun () ->
            ( Map.merge sess1 sess2 ~f:(fun ~key -> function
                | `Left _ | `Right _ -> assert false
                | `Both ((dir1, styv1), (_, styv2)) ->
                    if String.(key = channel_name.txt) then
                      match dir1 with
                      | `Left -> Some (`Left, Styv_echoice (styv1, styv2))
                      | `Right -> Some (`Right, Styv_ichoice (styv1, styv2))
                    else if equal_sess_tyv styv1 styv2 then Some (dir1, styv1)
                    else
                      raise
                        (Type_error
                           ( Format.asprintf
                               "mismatched sessions %a and %a in M_branch_send"
                               Ast_ops.print_sess_tyv styv1
                               Ast_ops.print_sess_tyv styv2,
                             cmd.cmd_loc ))),
              acc_sess_eq_constrs1 @ acc_sess_eq_constrs2 ))
    | M_branch_self (_, cmd1, cmd2) ->
        let%bind sess1, acc_sess_eq_constrs1 =
          backward ~access_to_old_trace ctxt sess_and_acc_sess_eq_constrs cmd1
        in
        let%bind sess2, acc_sess_eq_constrs2 =
          backward ~access_to_old_trace ctxt sess_and_acc_sess_eq_constrs cmd2
        in
        Or_error.try_with (fun () ->
            ( Map.merge sess1 sess2 ~f:(fun ~key:_ -> function
                | `Left _ | `Right _ -> assert false
                | `Both ((dir1, styv1), (_, styv2)) ->
                    if equal_sess_tyv styv1 styv2 then Some (dir1, styv1)
                    else
                      raise
                        (Type_error
                           ("mismatched sessions in M_branch_self", cmd.cmd_loc))),
              acc_sess_eq_constrs1 @ acc_sess_eq_constrs2 ))
    | M_call (proc_name, _) -> (
        match Map.find psig_ctxt proc_name.txt with
        | None ->
            Or_error.of_exn
              (Type_error ("unknown procedure " ^ proc_name.txt, proc_name.loc))
        | Some psigv ->
            let%bind sess0 =
              String.Map.of_alist_or_error
                (List.append
                   (Option.to_list psigv.psigv_sess_left)
                   (Option.to_list psigv.psigv_sess_right))
            in
            if not (Set.is_subset (Map.key_set sess0) ~of_:(Map.key_set sess))
            then
              Or_error.of_exn (Type_error ("mismatched channels", cmd.cmd_loc))
            else
              Or_error.try_with (fun () ->
                  ( Map.merge sess0 sess ~f:(fun ~key:_ -> function
                      | `Left _ -> assert false
                      | `Right (dir, sty) -> Some (dir, sty)
                      | `Both (type_id, (dir, sty)) ->
                          Some (dir, Styv_var (type_id, sty))),
                    acc_sess_eq_constrs )))
    | M_loop (n, _, bind_name, bind_ty, cmd0) ->
        let bind_tyv = eval_ty bind_ty in
        let ctxt' = Map.set ctxt ~key:bind_name.txt ~data:bind_tyv in
        List.fold_result
          (List.init n ~f:(fun _ -> ()))
          ~init:sess_and_acc_sess_eq_constrs
          ~f:(fun acc () -> backward ~access_to_old_trace ctxt' acc cmd0)
    | M_iter (iter_exp, _, iter_name, bind_name, bind_ty, cmd0) -> (
        let%bind iter_tyv = tycheck_exp ctxt iter_exp in
        match iter_tyv with
        | Btyv_tensor (pty, dims) when List.length dims > 0 ->
            let elem_tyv = Btyv_tensor (pty, List.tl_exn dims) in
            let bind_tyv = eval_ty bind_ty in
            let ctxt' = Map.set ctxt ~key:iter_name.txt ~data:elem_tyv in
            let ctxt'' = Map.set ctxt' ~key:bind_name.txt ~data:bind_tyv in
            List.fold_result
              (List.init (List.hd_exn dims) ~f:(fun _ -> ()))
              ~init:sess_and_acc_sess_eq_constrs
              ~f:(fun acc () -> backward ~access_to_old_trace ctxt'' acc cmd0)
        | _ -> Or_error.of_exn (Type_error ("not iterable", iter_exp.exp_loc)))
  in
  fun ctxt sess_left sess_right cmd ->
    let%bind tyv = forward_wrapper psig_ctxt ctxt cmd in
    let sess_left = Option.map sess_left ~f:(fun (k, v) -> (k, (`Left, v))) in
    let sess_right =
      Option.map sess_right ~f:(fun (k, v) -> (k, (`Right, v)))
    in
    let%bind sess =
      String.Map.of_alist_or_error
        (List.append (Option.to_list sess_left) (Option.to_list sess_right))
    in
    let%bind sess', type_eq_consts =
      backward ~access_to_old_trace:true ctxt (sess, []) cmd
    in
    Ok
      ( tyv,
        Option.map sess_left ~f:(fun (channel_id, _) ->
            let _, sty = Map.find_exn sess' channel_id in
            (channel_id, sty)),
        Option.map sess_right ~f:(fun (channel_id, _) ->
            let _, sty = Map.find_exn sess' channel_id in
            (channel_id, sty)),
        type_eq_consts )

let tycheck_proc sty_ctxt psig_ctxt ext_ctxt proc =
  let psigv = eval_proc_sig proc.proc_sig in
  let%bind ctxt =
    String.Map.of_alist_or_error
      (List.concat
         [
           ext_ctxt;
           List.map psigv.psigv_theta_tys ~f:(fun (var_name, pty) ->
               (var_name, pty));
           psigv.psigv_param_tys;
         ])
  in
  let%bind tyv, sess_left, sess_right, type_eq_constrs =
    tycheck_cmd psig_ctxt ctxt
      (Option.map psigv.psigv_sess_left ~f:(fun (channel_id, _) ->
           (channel_id, Styv_one)))
      (Option.map psigv.psigv_sess_right ~f:(fun (channel_id, _) ->
           (channel_id, Styv_one)))
      proc.proc_body
  in
  (* For debugging *)
  (* let () =
       match sess_left with
       | None -> print_endline "Left session type: None"
       | Some (channel_name, session_type) ->
           Format.printf "Left session type: channel name = %s, type = %a\n"
             channel_name Ast_ops.print_sess_tyv session_type
     in *)
  (* For debugging *)
  (* let () =
       match sess_right with
       | None -> print_endline "Right session type: None"
       | Some (channel_name, session_type) ->
           Format.printf "Right session type: channel name = %s, type = %a\n"
             channel_name Ast_ops.print_sess_tyv session_type
     in *)
  if not (is_subtype tyv psigv.psigv_ret_ty) then
    Or_error.of_exn (Type_error ("mismatched signature types", proc.proc_loc))
  else if
    Option.value_map sess_left ~default:false ~f:(fun (_, sty) ->
        let type_id = Option.value_exn psigv.psigv_sess_left |> snd in
        match Hashtbl.find sty_ctxt type_id with
        | None -> true
        | Some sty_def -> (
            match sty_def with
            | None ->
                Format.printf
                  "successfully inferred guide type operator %s[$]@.\t%a@.@."
                  type_id Ast_ops.print_sess_tyv sty;
                Hashtbl.set sty_ctxt ~key:type_id ~data:(Some sty);
                false
            | Some sty_def ->
                (* Here, we use syntactic equality checking for session types that
                   takes into account coverage checking. This is because we want to
                   make sure that the session type provided by the user exactly
                   matches the type we infer from the code. *)
                not (equal_sess_tyv sty sty_def)))
  then Or_error.of_exn (Type_error ("mismatched left session", proc.proc_loc))
  else if
    Option.value_map sess_right ~default:false ~f:(fun (_, sty) ->
        let type_id = Option.value_exn psigv.psigv_sess_right |> snd in
        match Hashtbl.find sty_ctxt type_id with
        | None -> true
        | Some sty_def -> (
            match sty_def with
            | None ->
                Format.printf
                  "successfully inferred guide type operator %s[$]@.\t%a@.@."
                  type_id Ast_ops.print_sess_tyv sty;
                Hashtbl.set sty_ctxt ~key:type_id ~data:(Some sty);
                false
            | Some sty_def ->
                (* For debugging *)
                (* Format.printf "sty_def = %a, sty = %a line 885\n"
                   Ast_ops.print_sess_tyv sty_def Ast_ops.print_sess_tyv sty; *)
                not (equal_sess_tyv sty sty_def)))
  then Or_error.of_exn (Type_error ("mismatched right session", proc.proc_loc))
  else Ok type_eq_constrs

let rec verify_sess_ty sty_ctxt sty =
  match sty.sty_desc with
  | Sty_one -> Ok ()
  | Sty_conj (_, sty2) -> verify_sess_ty sty_ctxt sty2
  | Sty_imply (_, sty2) -> verify_sess_ty sty_ctxt sty2
  | Sty_ichoice (sty1, sty2) ->
      let%bind () = verify_sess_ty sty_ctxt sty1 in
      verify_sess_ty sty_ctxt sty2
  | Sty_echoice (sty1, sty2) ->
      let%bind () = verify_sess_ty sty_ctxt sty1 in
      verify_sess_ty sty_ctxt sty2
  | Sty_var (type_name, sty0) -> (
      match Hashtbl.find sty_ctxt type_name.txt with
      | None ->
          Or_error.of_exn
            (Type_error ("unknown type " ^ type_name.txt, type_name.loc))
      | Some _ ->
          Option.value_map sty0 ~default:(Ok ()) ~f:(verify_sess_ty sty_ctxt))

let tycheck_prog prog =
  let%bind sty_ctxt = collect_sess_tys prog in
  (* For debugging *)
  (* let () = Ast_ops.print_sess_type_context Format.std_formatter sty_ctxt in *)
  let%bind psig_ctxt = collect_proc_sigs prog in
  (* For debugging *)
  (* Ast_ops.print_proc_signature_context Format.std_formatter psig_ctxt; *)
  let ext_ctxt = collect_externals prog in
  (* List of pairs of types whose equality must be checked *)
  let%bind type_eq_constrs =
    List.fold_result prog ~init:[] ~f:(fun acc top ->
        match top with
        | Top_sess (_, sty) -> (
            match sty with
            | None -> Ok acc
            | Some sty -> (
                match sty.sty_desc with
                | Sty_var _ ->
                    Or_error.of_exn
                      (Type_error ("non-contractive type", sty.sty_loc))
                | _ ->
                    let%bind () = verify_sess_ty sty_ctxt sty in
                    Ok acc))
        | Top_proc (_, proc) ->
            let%bind type_eq_consts =
              tycheck_proc sty_ctxt psig_ctxt ext_ctxt proc
            in
            Ok (type_eq_consts @ acc)
        | Top_external _ -> Ok acc
        | _ -> Ok acc)
  in
  let sty_ctxt_list =
    List.filter_map (Hashtbl.to_alist sty_ctxt) ~f:(fun (name, definition) ->
        match definition with None -> None | Some d -> Some (name, d))
  in
  (* We must check the equality of types we have inferred types for all
     processes. Otherwise, if we instead checked the type equality at the end of
     type-inference of a single process (rather than all processes in the
     program), we could encoungere a type name whose definition has not been
     inferred yet. *)
  let list_equality_result =
    match type_eq_constrs with
    | [] ->
        (* If the list is empty, we don't even need to compute a Caucal base *)
        []
    | _ ->
        Type_equality_check.type_equality_check_list_type_pairs sty_ctxt_list
          type_eq_constrs
  in
  (* Print out the result of checking type-equality constraints generated by
     type infernece *)
  let () =
    if not (List.is_empty list_equality_result) then (
      print_endline "We check all type-equality constraints from type inference";
      List.iter list_equality_result ~f:(fun (x, y, eq) ->
          match eq with
          | true ->
              Format.printf "Types %a and %a are equal modulo coverage\n"
                Ast_ops.print_sess_tyv x Ast_ops.print_sess_tyv y
          | false ->
              Format.printf "Types %a and %a are unequal modulo coverage\n"
                Ast_ops.print_sess_tyv x Ast_ops.print_sess_tyv y);
      if List.for_all list_equality_result ~f:(fun (_, _, eq) -> eq) then
        print_endline "All equal modulo coverage"
      else print_endline "Some are unequal modulo coverage")
    else ()
  in
  Ok ()

let () =
  Location.register_error_of_exn (function
    | Type_error (msg, loc) -> Some (Location.errorf ~loc "%s" msg)
    | _ -> None)
