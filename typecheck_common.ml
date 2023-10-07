open Ast_types

let rec eval_ty ty =
  match ty.bty_desc with
  | Bty_prim pty -> Btyv_prim pty
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
