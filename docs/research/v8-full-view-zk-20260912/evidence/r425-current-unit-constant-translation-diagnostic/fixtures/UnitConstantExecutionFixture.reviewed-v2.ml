open Aeneas
open Aeneas.Types
open Aeneas.TypesUtils
open Aeneas.Values
open Aeneas.Expressions
open Aeneas.LlbcAst
open Aeneas.Identifiers
module SA = Aeneas.SymbolicAst

let checks = ref 0
let fail label = failwith ("R425 unit execution fixture failed: " ^ label)
let check label condition =
  incr checks;
  if not condition then fail label

let empty_args : generic_args =
  { regions = []; types = []; const_generics = []; trait_refs = [] }

let unit_ty = mk_unit_ty
let unit_const = Charon.ExpressionsUtils.mk_unit_const
let expected_unit : tvalue =
  { value = VAdt { variant_id = None; fields = [] }; ty = unit_ty }

let tuple_with_one_unit : constant_expr =
  {
    kind = CAdt (None, [ unit_const ]);
    ty = TAdt { id = TTuple; generics = { empty_args with types = [ unit_ty ] } };
  }

let with_decoded_contexts llbc_path run =
  match LlbcOfJson.crate_of_json_file llbc_path with
  | Error msg -> failwith ("could not decode R419 LLBC: " ^ msg)
  | Ok crate ->
      let fd = FunDeclId.Map.find (FunDeclId.of_int 58) crate.fun_decls in
      let span = fd.item_meta.span in
      let decls_ctx = Interp.compute_contexts crate in
      let ctx =
        InterpUtils.initialize_eval_ctx (Some span) decls_ctx [] [] []
          ContextsBase.empty_marked_ids
      in
      run crate span ctx

let exercise_mode (span : Meta.span) (ctx : Contexts.eval_ctx)
    (mode : Contexts.interpreter_mode) =
  let config = Contexts.mk_config mode in
  let value, ctx_out, continue =
    InterpExpressions.eval_operands config span [ Constant unit_const ]
      ctx
  in
  check "exact returned zero-field tuple value and unit type"
    (value = [ expected_unit ]);
  check "same physical evaluation context returned" (ctx_out == ctx);
  let witness = SA.Assertion (ctx, true, expected_unit, SA.Panic) in
  check "continuation preserves the exact expression object"
    (continue witness == witness);

  let expected_diagnostic =
    "Found unexpected constant: "
    ^ InterpUtils.constant_expr_to_string ctx tuple_with_one_unit
  in
  let observed_diagnostic =
    try
      ignore
        (InterpExpressions.eval_operands config span
           [ Constant tuple_with_one_unit ] ctx);
      None
    with Errors.CFailure failure -> Some failure.msg
  in
  check "valid nonempty tuple keeps the exact old unsupported-constant diagnostic"
    (observed_diagnostic = Some expected_diagnostic)

let () =
  Config.fail_hard := false;
  if Array.length Sys.argv <> 2 then
    failwith "usage: unit-constant-execution-fixture <R419-candidate.llbc>";
  with_decoded_contexts Sys.argv.(1) (fun _crate span ctx ->
      exercise_mode span ctx Contexts.ConcreteMode;
      exercise_mode span ctx Contexts.SymbolicMode);
  if !checks <> 8 then fail "fixture assertion count must be 8";
  Printf.printf "R425 unit execution checks passed: %d\n" !checks
