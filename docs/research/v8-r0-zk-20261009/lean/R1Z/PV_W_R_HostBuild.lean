import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_HostBuild
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
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
  P ((core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error)
    × T1) := do
  let s ← invoke "Aeneas.Std.lift" (fun ops =>
      letI : ExternalFuns := ops
      Aeneas.Std.lift (Array.to_slice noised_semantic_c1.c1))
  let i := Slice.len s
  if i != 16#usize then
    pure (core.result.Result.Err r1_wire.Error.Public, commitments)
  else
    let s1 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Array.to_slice compiled.semantic_c1.c1))
    let i1 := Slice.len s1
    if i1 != 16#usize then
      pure (core.result.Result.Err r1_wire.Error.Public, commitments)
    else
      let pvplpsv ← invoke "aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition" (fun ops =>
          letI : ExternalFuns := ops
          aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition
          public1)
      let b ← invoke "core.cmp.impls.PartialEqShared.ne" (fun ops =>
          letI : ExternalFuns := ops
          core.cmp.impls.PartialEqShared.ne
          aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1
          compiled.public_statement pvplpsv)
      if b then
        pure (core.result.Result.Err r1_wire.Error.Public, commitments)
      else
        let s2 ← invoke "Aeneas.Std.lift" (fun ops =>
            letI : ExternalFuns := ops
            Aeneas.Std.lift (Array.to_slice noised_semantic_c1.c1))
        let c1 ← invoke "host_semantic.clone_semantic_columns" (fun ops =>
            letI : ExternalFuns := ops
            host_semantic.clone_semantic_columns s2 mask_only)
        invoke "host_semantic.build_with_helper_mode" (fun ops =>
          letI : ExternalFuns := ops
          host_semantic.build_with_helper_mode aspis_coredigestDigest32Inst
          (host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error
          aspis_coredigestDigest32Inst CommitmentsInst) CommitmentsInst public1
          c1 d g h1_padding (compiled, public1) commitments hash variant)

theorem erase_program (ops : ExternalFuns)
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
  erase ops (program aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant) =
    @host_semantic.build_with_material _ ops H T1 aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant := by
  unfold program host_semantic.build_with_material
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro s
    try dsimp only
    try dsimp only
    apply PV_W_Callbacks.erase_if_congr
    ·
      rfl
    ·
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro s1
        try dsimp only
        try dsimp only
        apply PV_W_Callbacks.erase_if_congr
        ·
          rfl
        ·
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro pvplpsv
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro b
              try dsimp only
              apply PV_W_Callbacks.erase_if_congr
              ·
                rfl
              ·
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro s2
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro c1
                    exact erase_invoke ops _ _

#print axioms erase_program
end R1Z.PV_W_R_HostBuild
