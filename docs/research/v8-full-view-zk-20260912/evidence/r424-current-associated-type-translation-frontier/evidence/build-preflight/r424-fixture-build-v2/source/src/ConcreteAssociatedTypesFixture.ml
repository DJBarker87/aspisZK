(* UNVERIFIED focused executable fixture for ConcreteAssociatedTypes.draft.ml.
   Run with the exact R396 LLBC JSON as argv.(1) in a fresh R424 workspace.
   Preparation only: no test or compile has been run. *)

open Aeneas
open Core
open Poly
open Aeneas.Types
open Aeneas.LlbcAst
open Aeneas.Identifiers

let assertions = ref 0
let fail label = failwith ("R424 fixture failed: " ^ label)
let check label condition =
  incr assertions;
  if not condition then fail label

let empty_args : generic_args =
  { regions = []; types = []; const_generics = []; trait_refs = [] }

let empty_params : generic_params =
  {
    regions = [];
    types = [];
    const_generics = [];
    trait_clauses = [];
    regions_outlive = [];
    types_outlive = [];
    trait_type_constraints = [];
  }

let unit_ty = TAdt { id = TTuple; generics = empty_args }
let bool_ty = TLiteral TBool
let word_ty = TLiteral (TUInt U32)

let reject_message label expected_message thunk =
  let observed =
    try
      thunk ();
      None
    with Errors.CFailure failure -> Some failure.msg
  in
  match observed with
  | None -> check (label ^ " must reject") false
  | Some message ->
      check (label ^ " must use the expected R424 rejection")
        (message = expected_message)

let reject_native_arity label thunk =
  let rejected =
    try
      thunk ();
      false
    with Errors.CFailure _ -> true
  in
  check (label ^ " must fail through the Aeneas substitution error path") rejected

let replace_assoc_impl crate impl_id assoc_id assoc =
  let impl = TraitImplId.Map.find impl_id crate.trait_impls in
  let impl =
    { impl with types = AssocTypeId.Map.add assoc_id assoc impl.types }
  in
  { crate with trait_impls = TraitImplId.Map.add impl_id impl crate.trait_impls }

let get_assoc impl assoc_id = AssocTypeId.Map.find assoc_id impl.types

let mk_impl_ref impl_id impl types =
  let generics = { empty_args with types } in
  let kind = TraitImpl { id = impl_id; generics } in
  let subst =
    Substitute.make_subst_from_generics __FILE__ __LINE__ None impl.generics generics kind
  in
  let trait_decl_ref = Substitute.trait_decl_ref_substitute subst impl.impl_trait in
  {
    kind;
    trait_decl_ref = { binder_regions = []; binder_value = trait_decl_ref };
  }

let output_projection impl_id impl b c =
  TTraitType (mk_impl_ref impl_id impl [ b; c ], AssocTypeId.of_int 0, empty_args)

let get_fixture_impl crate =
  let id = TraitImplId.of_int 24 in
  (id, TraitImplId.Map.find id crate.trait_impls)

let set_output_value binder value =
  let binder_value = { binder.binder_value with value; implied_trait_refs = [] } in
  { binder with binder_value }

let base_signature crate =
  match FunDeclId.Map.bindings crate.fun_decls with
  | (_, fd) :: _ -> fd.signature
  | [] -> fail "R396 fixture must contain a function signature"

let borrowed_c =
  TRef (RVar (Free (RegionId.of_int 70)), unit_ty, RShared)

let lift_arrow_outer_region_one_level ty =
  (* Fixture-local, shape-specific lifting. This changes only a Bound(1) region
     in the two reference positions of the exact test arrow, preserving its
     inner Bound(0). It is not a generic production de Bruijn transformer. *)
  match ty with
  | TFnPtr binder ->
      let lift = function
        | TRef (RVar (Bound (1, rid)), pointee, kind) ->
            TRef (RVar (Bound (2, rid)), pointee, kind)
        | other -> other
      in
      TFnPtr
        {
          binder with
          binder_value =
            {
              binder.binder_value with
              inputs = List.map ~f:lift binder.binder_value.inputs;
              output = lift binder.binder_value.output;
            };
        }
  | _ -> fail "expected nested function-pointer fixture"

let lift_try_self_type_for_empty_region_binder tref =
  (* Try's self type is ControlFlow<B,C>. The trait-declaration reference is
     itself stored under its region_binder. Lift only C's exact nested-arrow
     fixture across that one stored binder: inner Bound(0) stays fixed and
     ambient Bound(1) becomes Bound(2). The trait-impl reference's own
     instantiation remains at the surrounding type's depth. *)
  let br = tref.trait_decl_ref in
  match br.binder_value.generics.types with
  | [ TAdt control_flow ] ->
      (match control_flow.generics.types with
      | [ b; c ] ->
          let control_flow =
            { control_flow with
              generics = { control_flow.generics with types = [ b; lift_arrow_outer_region_one_level c ] } }
          in
          let decl =
            { br.binder_value with generics = { br.binder_value.generics with types = [ TAdt control_flow ] } }
          in
          { tref with trait_decl_ref = { br with binder_value = decl } }
      | _ -> fail "impl24 ControlFlow self type did not have B/C arguments")
  | _ -> fail "impl24 Try self type did not have a ControlFlow argument"

let nested_arrow_case crate impl_id impl =
  (* The arrow is the C argument and contains local Bound(0) plus ambient
     Bound(1). The whole projection is placed under an outer bound region. *)
  let outer = RegionId.of_int 70 in
  let inner = RegionId.of_int 71 in
  let outer_param = { index = outer; name = Some "outer"; mutability = LtShared } in
  let inner_param = { index = inner; name = Some "inner"; mutability = LtShared } in
  let unit_ref r = TRef (r, unit_ty, RShared) in
  let base = base_signature crate in
  let inner_arrow =
    TFnPtr
      {
        binder_regions = [ inner_param ];
        binder_value =
          {
            base with
            inputs = [ unit_ref (RVar (Bound (0, inner))); unit_ref (RVar (Bound (1, outer))) ];
            output = unit_ref (RVar (Bound (1, outer)));
          };
      }
  in
  let ordinary = mk_impl_ref impl_id impl [ word_ty; inner_arrow ] in
  let lifted = lift_try_self_type_for_empty_region_binder ordinary in
  let projection = TTraitType (lifted, AssocTypeId.of_int 0, empty_args) in
  let outer_type =
    TFnPtr
      {
        binder_regions = [ outer_param ];
        binder_value = { base with inputs = []; output = projection };
      }
  in
  let expected =
    TFnPtr
      {
        binder_regions = [ outer_param ];
        binder_value = { base with inputs = []; output = inner_arrow };
      }
  in
  (inner_arrow, outer_type, expected)

let run crate =
  let impl_id, impl = get_fixture_impl crate in
  let out_id = AssocTypeId.of_int 0 in
  let source_output = get_assoc impl out_id in
  check "impl24 Output has no associated-item generic parameters"
    (source_output.binder_params = empty_params);
  check "impl24 Output source body is C"
    (match source_output.binder_value.value with
    | TVar (Free id) -> id = (List.nth_exn impl.generics.types 1).index
    | _ -> false);

  (* Actual R396 impl24: Output(unit, unit) = unit. *)
  let projection = output_projection impl_id impl unit_ty unit_ty in
  check "impl24 Output(unit,unit) reduces to unit"
    (ConcreteAssociatedTypes.normalize_ty None crate projection = unit_ty);

  (* Distinct concrete and symbolic arguments separately prove the output
     selects C's position. *)
  let concrete_projection = output_projection impl_id impl word_ty bool_ty in
  check "distinct concrete B/C map Output to C"
    (ConcreteAssociatedTypes.normalize_ty None crate concrete_projection = bool_ty);
  let symbolic_b = TVar (Free (TypeVarId.of_int 90)) in
  let symbolic_c = TVar (Free (TypeVarId.of_int 91)) in
  let symbolic_projection = output_projection impl_id impl symbolic_b symbolic_c in
  check "distinct symbolic B/C map Output to C"
    (ConcreteAssociatedTypes.normalize_ty None crate symbolic_projection = symbolic_c);

  (* A borrowed type argument keeps its free lifetime. *)
  let projection = output_projection impl_id impl word_ty borrowed_c in
  check "borrowed C keeps its free lifetime"
    (ConcreteAssociatedTypes.normalize_ty None crate projection = borrowed_c);

  (* A nested function pointer keeps local Bound(0) and ambient Bound(1). *)
  let inner_arrow, outer_type, expected = nested_arrow_case crate impl_id impl in
  ignore inner_arrow;
  check "nested arrow retains local Bound(0) and ambient Bound(1) capture-free"
    (ConcreteAssociatedTypes.normalize_ty None crate outer_type = expected);

  (* Clause projections remain abstract. *)
  let tref = mk_impl_ref impl_id impl [ word_ty; bool_ty ] in
  let clause_ref = { tref with kind = Clause (Free (TraitClauseId.of_int 77)) } in
  let clause_projection = TTraitType (clause_ref, out_id, empty_args) in
  check "clause projection remains unchanged"
    (ConcreteAssociatedTypes.normalize_ty None crate clause_projection = clause_projection);

  (* A mismatched trait declaration identity is rejected. *)
  let tref = mk_impl_ref impl_id impl [ word_ty; bool_ty ] in
  let wrong_trait =
    { tref with
      trait_decl_ref =
        { tref.trait_decl_ref with
          binder_value = { tref.trait_decl_ref.binder_value with id = TraitDeclId.of_int 0 } } }
  in
  reject_message "trait identity mismatch" "R424: concrete implementation trait instantiation mismatch" (fun () ->
      ignore (ConcreteAssociatedTypes.normalize_ty None crate (TTraitType (wrong_trait, out_id, empty_args))));

  (* Missing associated item. *)
  reject_message "missing associated type" "R424: missing concrete associated-type definition" (fun () ->
      ignore (ConcreteAssociatedTypes.normalize_ty None crate
        (TTraitType (mk_impl_ref impl_id impl [ word_ty; bool_ty ], AssocTypeId.of_int 99, empty_args))));

  (* Start from a valid self reference, then corrupt only the impl-kind args.
     This ensures the failure is exercised inside the candidate normalization,
     not while constructing the fixture reference. *)
  reject_native_arity "bad implementation argument arity" (fun () ->
      let valid = mk_impl_ref impl_id impl [ word_ty; bool_ty ] in
      let bad_kind =
        TraitImpl { id = impl_id; generics = { empty_args with types = [ word_ty ] } }
      in
      let malformed = { valid with kind = bad_kind } in
      ignore (ConcreteAssociatedTypes.normalize_ty None crate (TTraitType (malformed, out_id, empty_args))));

  (* Nonempty associated-item binder remains explicitly unsupported. *)
  let generic_output =
    { source_output with
      binder_params = { source_output.binder_params with types = [ List.hd_exn impl.generics.types ] } }
  in
  let generic_impl = replace_assoc_impl crate impl_id out_id generic_output in
  reject_message "nonempty associated-item binder" "R424: generic associated-type binder is unsupported" (fun () ->
      ignore (ConcreteAssociatedTypes.normalize_ty None generic_impl
        (output_projection impl_id impl word_ty bool_ty)));

  (* The recursive target is rejected by the explicit source-binder guard,
     because it contains a TTraitType projection. This does not exercise the
     separate recursion-stack detector. *)
  let recursive_projection = output_projection impl_id impl unit_ty unit_ty in
  let recursive_output = set_output_value source_output recursive_projection in
  let recursive_impl = replace_assoc_impl crate impl_id out_id recursive_output in
  reject_message "recursive source projection is rejected by binder guard" "R424: nested associated-value region binder is unsupported" (fun () ->
      ignore (ConcreteAssociatedTypes.normalize_ty None recursive_impl recursive_projection));

  (* Unavailable implementation lookup is rejected. *)
  let tref = mk_impl_ref impl_id impl [ word_ty; bool_ty ] in
  let missing_impl_ref =
    { tref with
      kind = TraitImpl { id = TraitImplId.of_int 999; generics = { empty_args with types = [ word_ty; bool_ty ] } } }
  in
  reject_message "missing implementation" "R424: missing concrete trait implementation" (fun () ->
      ignore (ConcreteAssociatedTypes.normalize_ty None crate
        (TTraitType (missing_impl_ref, out_id, empty_args))));

  print_endline (Printf.sprintf "R424 fixture assertions passed: %d" !assertions)

let () =
  Config.fail_hard := false;
  if Array.length Sys.argv <> 2 then failwith "usage: fixture <R396.llbc>";
  match LlbcOfJson.crate_of_json_file Sys.argv.(1) with
  | Error msg -> failwith ("could not load R396 fixture: " ^ msg)
  | Ok crate -> run crate
