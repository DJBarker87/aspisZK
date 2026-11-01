import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_BuildSemantics
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  op225_OPEN : ∀ (arg0 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public), P (aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
  sharedNe_OPEN : ∀ {T U : Type} (inst : core.cmp.PartialEq T U) (a : T) (b : U), P (Bool)
  clone_semantic_columns_OPEN : ∀ (noised : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize), P ((Array (alloc.vec.Vec aspis_core.field.M31) 26#usize))
  build_with_helper_mode_OPEN : ∀ {H : Type} {T1 : Type} {T2 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H)
  (coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst :
  core.ops.function.FnOnce T1 (aspis_core.field.QM31 × aspis_core.field.QM31)
  (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) r1_wire.Error))
  (CommitmentsInst : host_semantic.Commitments T2)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (helper : T1)
  (commitments : T2) (hash : H) (variant : transport.Variant), P (((core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error)
    × T2))

structure Compatible (c : Callees) : Prop where
  op225_fixed : ∀ (arg0 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public), FinishedView (c.op225_OPEN arg0) (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition arg0)
  sharedNe_fixed : ∀ {T U : Type} (inst : core.cmp.PartialEq T U) (a : T) (b : U), FinishedView (c.sharedNe_OPEN inst a b) (core.cmp.impls.PartialEqShared.ne inst a b)
  clone_semantic_columns_fixed : ∀ (noised : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize), FinishedView (c.clone_semantic_columns_OPEN noised mask_only) (host_semantic.clone_semantic_columns noised mask_only)
  build_with_helper_mode_fixed : ∀ {H : Type} {T1 : Type} {T2 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H)
  (coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst :
  core.ops.function.FnOnce T1 (aspis_core.field.QM31 × aspis_core.field.QM31)
  (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) r1_wire.Error))
  (CommitmentsInst : host_semantic.Commitments T2)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (helper : T1)
  (commitments : T2) (hash : H) (variant : transport.Variant), FinishedView (c.build_with_helper_mode_OPEN aspis_coredigestDigest32Inst coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst CommitmentsInst public1 c1 d g h1_padding helper commitments hash variant) (host_semantic.build_with_helper_mode aspis_coredigestDigest32Inst coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst CommitmentsInst public1 c1 d g h1_padding helper commitments hash variant)

def run
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
  (hash : H) (variant : transport.Variant) (c : Callees) : P ((core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error)
    × T1) := do
  let s ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice noised_semantic_c1.c1))
  let i := Slice.len s
  if i != 16#usize then
    pure (core.result.Result.Err r1_wire.Error.Public, commitments)
  else
    let s1 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice compiled.semantic_c1.c1))
    let i1 := Slice.len s1
    if i1 != 16#usize then
      pure (core.result.Result.Err r1_wire.Error.Public, commitments)
    else
      let pvplpsv ← c.op225_OPEN
          public1
      let b ← c.sharedNe_OPEN
          aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1
          compiled.public_statement pvplpsv
      if b then
        pure (core.result.Result.Err r1_wire.Error.Public, commitments)
      else
        let s2 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice noised_semantic_c1.c1))
        let c1 ← c.clone_semantic_columns_OPEN s2 mask_only
        c.build_with_helper_mode_OPEN aspis_coredigestDigest32Inst
          (host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error
          aspis_coredigestDigest32Inst CommitmentsInst) CommitmentsInst public1
          c1 d g h1_padding (compiled, public1) commitments hash variant

theorem run_fixed
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
  (hash : H) (variant : transport.Variant) (c : Callees) (compatible : Compatible c) :
    FinishedView (run aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant c) (host_semantic.build_with_material aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant) := by
  unfold run host_semantic.build_with_material
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact PV_EVH_Prefix.lift_fixed _
  · intro s
    let i := Slice.len s
    try dsimp only
    by_cases condition : i != 16#usize
    · try dsimp only [i] at condition
      simp only [condition,if_true]
      exact PV_EVH_Prefix.lift_fixed _
    · try dsimp only [i] at condition
      simp only [condition,if_false]
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact PV_EVH_Prefix.lift_fixed _
      · intro s1
        let i1 := Slice.len s1
        try dsimp only
        by_cases condition : i1 != 16#usize
        · try dsimp only [i,i1] at condition
          simp only [condition,if_true]
          exact PV_EVH_Prefix.lift_fixed _
        · try dsimp only [i,i1] at condition
          simp only [condition,if_false]
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact compatible.op225_fixed _
          · intro pvplpsv
            try dsimp only
            apply PV_EVH_Prefix.bind_fixed
            ·
              exact compatible.sharedNe_fixed _ _ _
            · intro b
              by_cases condition : b
              · try dsimp only [i,i1] at condition
                simp only [condition,if_true]
                exact PV_EVH_Prefix.lift_fixed _
              · try dsimp only [i,i1] at condition
                simp only [condition,if_false]
                try dsimp only
                apply PV_EVH_Prefix.bind_fixed
                ·
                  exact PV_EVH_Prefix.lift_fixed _
                · intro s2
                  try dsimp only
                  apply PV_EVH_Prefix.bind_fixed
                  ·
                    exact compatible.clone_semantic_columns_fixed _ _
                  · intro c1
                    exact compatible.build_with_helper_mode_fixed _ _ _ _ _ _ _ _ _ _ _ _

#print axioms run_fixed
end PV_EVH_BuildSemantics
