open Types
open TypesUtils
open Values

(** Decode only Charon's exact zero-operand unit aggregate constant.
    The caller keeps its existing diagnostic for every unsupported shape. *)
let eval (cv : constant_expr) : tvalue option =
  match cv.kind with
  | CAdt (None, []) when cv.ty = mk_unit_ty ->
      Some { value = VAdt { variant_id = None; fields = [] }; ty = cv.ty }
  | _ -> None
