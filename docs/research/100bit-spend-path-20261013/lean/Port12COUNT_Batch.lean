import Port12COUNT_BatchTree
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port12COUNT_Batch
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port12COUNT_Verify Port12COUNT_BatchLeaf
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem pure_cap {A Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (r : Result A) (n : Nat) : (eval H (Port9OR_Code.program D hash (liftResult r))).1.length≤n := by
  cases r <;> exact Nat.zero_le n

/-- All physical batch0 inputs/outcomes, including short-circuited trees. -/
theorem values0 (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (queries : Array U32 22#usize) (roots : Array Digest 3#usize) :
    (eval H (Port9OR_Code.program D hash
      (Port9OR_Batch.values base D hash proof queries roots 0#usize))).1.length≤477 := by
  unfold Port9OR_Batch.values
  apply lift_cap; intro root0
  apply lift_cap; intro root1
  apply lift_cap; intro root2
  apply bind_count D hash H _ _ 165 312
  · simpa using Port12COUNT_BatchTree.batch0 base D hash H proof queries root0 0#usize _ _ (by decide)
  · intro out _
    obtain ⟨r,idx1,val1⟩ := out
    apply lift_cap; intro flow
    cases flow with
    | Break residual => exact pure_cap D hash H _ _
    | Continue unit =>
      apply bind_count D hash H _ _ 165 147
      · simpa using Port12COUNT_BatchTree.batch0 base D hash H proof queries root1 1#usize idx1 val1 (by decide)
      · intro out _
        obtain ⟨r1,idx2,val2⟩ := out
        apply lift_cap; intro flow
        cases flow with
        | Break residual => exact pure_cap D hash H _ _
        | Continue unit =>
          apply bind_count D hash H _ _ 147 0
          · simpa using Port12COUNT_BatchTree.batch0 base D hash H proof queries root2 2#usize idx2 val2 (by decide)
          · intro out _
            obtain ⟨r2,idx3,val3⟩ := out
            apply lift_cap; intro flow
            cases flow with
            | Break residual => exact pure_cap D hash H _ _
            | Continue unit => exact Nat.zero_le 0

theorem batch0 (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Digest) :
    (eval H (Port9OR_Code.program D hash
      (Port9OR_Batch.code base D hash proof p folded 0#usize))).1.length≤477 := by
  unfold Port9OR_Batch.code
  apply lift_cap; intro root0
  apply lift_cap; intro root1
  exact values0 base D hash H proof p.queries _

/-- All physical batch1 inputs/outcomes, including short-circuited trees. -/
theorem values1 (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (queries : Array U32 22#usize) (roots : Array Digest 3#usize) :
    (eval H (Port9OR_Code.program D hash
      (Port9OR_Batch.values base D hash proof queries roots 1#usize))).1.length≤563 := by
  unfold Port9OR_Batch.values
  apply lift_cap; intro root0
  apply lift_cap; intro root1
  apply lift_cap; intro root2
  apply bind_count D hash H _ _ 195 368
  · simpa using Port12COUNT_BatchTree.batch1 base D hash H proof queries root0 0#usize _ _ (by decide)
  · intro out _
    obtain ⟨r,idx1,val1⟩ := out
    apply lift_cap; intro flow
    cases flow with
    | Break residual => exact pure_cap D hash H _ _
    | Continue unit =>
      apply bind_count D hash H _ _ 195 173
      · simpa using Port12COUNT_BatchTree.batch1 base D hash H proof queries root1 1#usize idx1 val1 (by decide)
      · intro out _
        obtain ⟨r1,idx2,val2⟩ := out
        apply lift_cap; intro flow
        cases flow with
        | Break residual => exact pure_cap D hash H _ _
        | Continue unit =>
          apply bind_count D hash H _ _ 173 0
          · simpa using Port12COUNT_BatchTree.batch1 base D hash H proof queries root2 2#usize idx2 val2 (by decide)
          · intro out _
            obtain ⟨r2,idx3,val3⟩ := out
            apply lift_cap; intro flow
            cases flow with
            | Break residual => exact pure_cap D hash H _ _
            | Continue unit => exact Nat.zero_le 0

theorem batch1 (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Digest) :
    (eval H (Port9OR_Code.program D hash
      (Port9OR_Batch.code base D hash proof p folded 1#usize))).1.length≤563 := by
  unfold Port9OR_Batch.code
  apply lift_cap; intro root0
  apply lift_cap; intro root1
  exact values1 base D hash H proof p.queries _

#print axioms pure_cap
#print axioms values0
#print axioms batch0
#print axioms values1
#print axioms batch1
end AspisR1.Port12COUNT_Batch
end
