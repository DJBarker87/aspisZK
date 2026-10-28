import R1Z.PV_Src_RootRecurrence
import R1Z.PV_Src_ExternalReference

/-! The actual pure root helper is one initial parent hash followed by twenty
source recurrence steps. This source equation keeps every Result outcome.
It does not assert that these twenty-one hashes equal the frozen root table. -/
set_option autoImplicit false
namespace R1Z.PV_Src_RootSourceEquation
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

def run [ExternalLinear] : Result PV_Src_RootRecurrence.Roots := do
  let zero := Array.repeat 8#usize aspis_core.field.M31.ZERO
  let roots := Array.repeat 21#usize zero
  let first ← format.pool_v1_tree_parent zero zero
  let initial ← Array.update roots 0#usize first
  PV_Src_RootRecurrence.steps 0#usize 20 initial

theorem source [ExternalLinear] : pair_trace.pair_empty_roots = run := by
  unfold pair_trace.pair_empty_roots run
  have h : ∀ roots : PV_Src_RootRecurrence.Roots,
      pair_trace.pair_empty_roots_loop
        { start := 0#usize, «end» := pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH } roots =
      PV_Src_RootRecurrence.steps 0#usize 20 roots := by
    intro roots
    apply PV_Src_RootRecurrence.loop
    · simp [pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH,format.POOL_V1_TREE_DEPTH]
    · simp [pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH,format.POOL_V1_TREE_DEPTH]
  simp only [h]

theorem pure_source :
    @pair_trace.pair_empty_roots PV_Src_ExternalReference.dictionary =
      @run PV_Src_ExternalReference.dictionary :=
  @source PV_Src_ExternalReference.dictionary

#print axioms source
#print axioms pure_source
end R1Z.PV_Src_RootSourceEquation
