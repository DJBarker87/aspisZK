import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_067
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_068
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (CommitmentsInst : host_semantic.Commitments
  T1)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (noised_semantic_c1 :
  aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (commitments : T1)
  (hash : H) (variant : transport.Variant) :
  Logged ((core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error)
    × T1)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let s ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice noised_semantic_c1.c1))
  let i := Slice.len s
  if i != 16#usize
  then Pure.pure (core.result.Result.Err r1_wire.Error.Public, commitments)
  else
    let s1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice compiled.semantic_c1.c1))
    let i1 := Slice.len s1
    if i1 != 16#usize
    then Pure.pure (core.result.Result.Err r1_wire.Error.Public, commitments)
    else
      let pvplpsv ← PV_L1D_Logged.lift (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition
          public1)
      let b ← PV_L1D_Logged.lift (core.cmp.impls.PartialEqShared.ne
          aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1
          compiled.public_statement pvplpsv)
      if b
      then Pure.pure (core.result.Result.Err r1_wire.Error.Public, commitments)
      else
        let s2 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice noised_semantic_c1.c1))
        let c1 ← PV_L1D_Logged.lift (host_semantic.clone_semantic_columns s2 mask_only)
        PV_L1D_Source_067.produce aspis_coredigestDigest32Inst
          (host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error
          aspis_coredigestDigest32Inst CommitmentsInst) CommitmentsInst public1
          c1 d g h1_padding (compiled, public1) commitments hash variant

theorem complete_result
  {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (CommitmentsInst : host_semantic.Commitments
  T1)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (noised_semantic_c1 :
  aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (commitments : T1)
  (hash : H) (variant : transport.Variant) :
  erase (produce (H := H) (T1 := T1) aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant) = host_semantic.build_with_material (H := H) (T1 := T1) aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant := by
  unfold produce
  conv_rhs => unfold host_semantic.build_with_material
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_067.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_067.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_067.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_068
