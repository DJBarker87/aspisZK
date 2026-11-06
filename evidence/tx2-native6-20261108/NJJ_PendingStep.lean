import NJJ_Pending
set_option autoImplicit false
noncomputable section
namespace NJJ_PendingStep
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev Row := Port3_NativePendingBody.Row
abbrev K := aspis_core.field.QM31

/-- Forward source-to-cut association of the arbitrary native row window.
It derives the selected source word, every untouched row, length and increment
from the literal emitted body; no post-state equation is a hypothesis. -/
theorem source (weights : Slice K) (raw : alloc.vec.Vec Row) (index : Usize)
 (weightSize : weights.val.length=64) (rawSize : raw.val.length=64) (inside : index.val<64) :
 ∃ after : alloc.vec.Vec Row, ∃ next : Usize,
 Port3_NativePendingBody.body weights raw index=ok (.cont (after,next)) ∧
 NJJ_Cuts.pendingStep weights raw after index.val next.val := by
 obtain ⟨w,read,step⟩ := Port3_NativePendingStep.step weights raw index weightSize rawSize inside
 refine ⟨raw.set index (Port3_PendingInstall.row w),Usize.wrapping_add index 1#usize,step,?_,?_,?_⟩
 · exact Port3_Wrapping.increment index (by omega)
 · simpa only [alloc.vec.Vec.set,List.length_set] using rawSize
 · intro j bound
   have lookup:=Port3_NativePendingLoop.read_lookup weights index w (by omega) read
   change (raw.val.set index.val (Port3_PendingInstall.row w))[j]?=_
   by_cases same : index.val=j
   · subst j
     rw [if_pos rfl,List.getElem?_set_self (by omega),lookup]
     rfl
   · rw [if_neg same,List.getElem?_set_ne same]

#print axioms source
end NJJ_PendingStep
