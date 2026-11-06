import NJP_CohortNode
import NJP_LoopModel
import MultiproofConeRootGuard

set_option autoImplicit false
noncomputable section
namespace NJP_CohortTerminal
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef

theorem digest_equal (left right : RefDigest) : decode left=decode right ↔ left=right :=
 ⟨fun h => NJP_DigestCarrier.faithful left right h,fun h => congrArg decode h⟩

/-- All four terminal clauses, without an acceptance or singleton premise. -/
theorem same (root : RefDigest) (physical : Slice U8) (s : reference.Scratch) :
 NJP_LoopModel.terminal (decode root) physical.val.length (raw s)=
 AspisR1.MultiproofConeRootGuard.sourceRoot root physical s := by
 unfold NJP_LoopModel.terminal AspisR1.MultiproofConeRootGuard.sourceRoot
 have index0 := NJP_CohortRead.index s 0#usize (by decide)
 have value0 := NJP_CohortRead.value s 0#usize (by decide)
 change NJP_RowModel.index (raw s) 0=s.idx.val[0]!.val at index0
 change NJP_RowModel.value (raw s) 0=decode (s.val.val[0]!) at value0
 rw [index0,value0]
 apply decide_eq_decide.mpr
 simp only [digest_equal,raw]

#print digest_equal
#print axioms digest_equal
#print same
#print axioms same
end NJP_CohortTerminal
end
