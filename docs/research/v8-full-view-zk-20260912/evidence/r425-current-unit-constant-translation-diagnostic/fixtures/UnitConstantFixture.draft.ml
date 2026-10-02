open Aeneas
open Aeneas.Types
open Aeneas.TypesUtils
open Aeneas.Values
open Aeneas.LlbcAst
open Aeneas.Identifiers

let checks = ref 0
let fail label = failwith ("R425 unit fixture failed: " ^ label)
let check label condition =
  incr checks;
  if not condition then fail label

let empty_args : generic_args =
  { regions = []; types = []; const_generics = []; trait_refs = [] }

let unit_ty = mk_unit_ty
let charon_unit = Charon.ExpressionsUtils.mk_unit_const
let expected_tvalue : tvalue =
  { value = VAdt { variant_id = None; fields = [] }; ty = unit_ty }

let rejected label (cv : constant_expr) =
  check (label ^ " must be rejected") (UnitConstant.eval cv = None)

let unit_constant (cv : constant_expr) =
  match cv.kind with
  | CAdt (None, []) -> cv.ty = unit_ty
  | _ -> false

let check_exact_r419_unit (crate : crate) =
  let id = FunDeclId.of_int 58 in
  let fd = FunDeclId.Map.find id crate.fun_decls in
  let found = ref [] in
  let visitor =
    object
      inherit [_] iter_statement as super
      method! visit_constant_expr env (cv : constant_expr) =
        if unit_constant cv then found := cv :: !found;
        super#visit_constant_expr env cv
    end
  in
  (match fd.body with
  | StructuredBody body -> visitor#visit_block () body.body
  | _ -> fail "R419 function 58 no longer has a structured body");
  match !found with
  | [ cv ] ->
      check "R419 decoded function58 unit equals Charon mk_unit_const"
        (cv = charon_unit);
      check "R419 function58 unit evaluates to zero-field tuple"
        (UnitConstant.eval cv = Some expected_tvalue)
  | _ -> fail "R419 function58 must contain exactly one unit constant"

let run (crate : crate) =
  check "Charon mk_unit_const has exact unit shape"
    (unit_constant charon_unit);
  check "Charon mk_unit_const evaluates to zero-field tuple"
    (UnitConstant.eval charon_unit = Some expected_tvalue);
  check_exact_r419_unit crate;

  rejected "nonempty CAdt fields"
    { charon_unit with kind = CAdt (None, [ charon_unit ]) };
  rejected "Some variant with empty fields"
    { charon_unit with kind = CAdt (Some (VariantId.of_int 0), []) };
  let nonunit_tuple =
    TAdt { id = TTuple; generics = { empty_args with types = [ unit_ty ] } }
  in
  rejected "nonunit tuple type"
    { charon_unit with ty = nonunit_tuple };
  let region_tuple =
    TAdt { id = TTuple; generics = { empty_args with regions = [ RStatic ] } }
  in
  rejected "tuple with region argument"
    { charon_unit with ty = region_tuple };
  let const_tuple =
    TAdt { id = TTuple; generics = { empty_args with const_generics = [ charon_unit ] } }
  in
  rejected "tuple with const-generic argument"
    { charon_unit with ty = const_tuple };
  let dummy_trait_ref : trait_ref =
    {
      kind = Clause (Free (TraitClauseId.of_int 0));
      trait_decl_ref =
        {
          binder_regions = [];
          binder_value =
            { id = TraitDeclId.of_int 0; generics = empty_args };
        };
    }
  in
  let trait_tuple =
    TAdt
      {
        id = TTuple;
        generics = { empty_args with trait_refs = [ dummy_trait_ref ] };
      }
  in
  rejected "tuple with trait argument"
    { charon_unit with ty = trait_tuple };
  rejected "non-aggregate constant kind with unit type"
    { charon_unit with kind = CArray [] };
  check "fixture assertion count is stable" (!checks = 11);
  Printf.printf "R425 unit constant fixture assertions passed: %d\n" !checks

let () =
  Config.fail_hard := false;
  if Array.length Sys.argv <> 2 then
    failwith "usage: unit-constant-fixture <R419-candidate.llbc>";
  match LlbcOfJson.crate_of_json_file Sys.argv.(1) with
  | Error msg -> failwith ("could not decode R419 LLBC: " ^ msg)
  | Ok crate -> run crate
