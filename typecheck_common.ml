open Core
open Ast_types

let rec eval_ty ty =
  match ty.bty_desc with
  | Bty_prim pty -> Btyv_prim pty
  | Bty_prim_uncovered pty -> Btyv_prim_uncovered pty
  | Bty_arrow (ty1, ty2) -> Btyv_arrow (eval_ty ty1, eval_ty ty2)
  | Bty_dist ty0 -> Btyv_dist (eval_ty ty0)
  | Bty_tensor (pty, dims) -> Btyv_tensor (pty, dims)
  | Bty_simplex n -> Btyv_simplex n
  | Bty_external type_name -> Btyv_external type_name.txt
  | Bty_product (ty1, ty2) -> Btyv_product (eval_ty ty1, eval_ty ty2)

let rec eval_sty sty =
  match sty.sty_desc with
  | Sty_one -> Styv_one
  | Sty_conj (ty1, sty2) -> Styv_conj (eval_ty ty1, eval_sty sty2)
  | Sty_imply (ty1, sty2) -> Styv_imply (eval_ty ty1, eval_sty sty2)
  | Sty_ichoice (sty1, sty2) -> Styv_ichoice (eval_sty sty1, eval_sty sty2)
  | Sty_echoice (sty1, sty2) -> Styv_echoice (eval_sty sty1, eval_sty sty2)
  | Sty_var (type_name, None) -> Styv_var (type_name.txt, Styv_one)
  | Sty_var (type_name, Some sty0) -> Styv_var (type_name.txt, eval_sty sty0)

let eval_proc_sig psig =
  {
    psigv_theta_tys =
      List.map psig.psig_theta_tys ~f:(fun (var_name, pty) ->
          (var_name.txt, eval_ty pty));
    psigv_param_tys =
      List.map psig.psig_param_tys ~f:(fun (var_name, ty) ->
          (var_name.txt, eval_ty ty));
    psigv_ret_ty = eval_ty psig.psig_ret_ty;
    psigv_sess_left =
      Option.map psig.psig_sess_left ~f:(fun (channel_name, type_name) ->
          (channel_name.txt, type_name.txt));
    psigv_sess_right =
      Option.map psig.psig_sess_right ~f:(fun (channel_name, type_name) ->
          (channel_name.txt, type_name.txt));
  }

let extract_context_of_process ext_ctxt proc =
  let psigv = eval_proc_sig proc.proc_sig in
  let ctxt =
    String.Map.of_alist_or_error
      (List.concat
         [
           ext_ctxt;
           List.map psigv.psigv_theta_tys ~f:(fun (var_name, pty) ->
               (var_name, pty));
           psigv.psigv_param_tys;
         ])
  in
  match ctxt with
  | Ok context -> context
  | _ -> failwith "We fail to extract a context"

let collect_externals prog =
  List.filter_map prog ~f:(fun top ->
      match top with
      | Top_sess _ -> None
      | Top_proc _ -> None
      | Top_external (var_name, ty) -> Some (var_name.txt, eval_ty ty))
