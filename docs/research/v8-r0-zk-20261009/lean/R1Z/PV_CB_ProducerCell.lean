import R1Z.PV_CB_ProducerPost
import R1Z.PV_CB_CanonicalM31Ops
import R1Z.ProverRwDictionaryScalar
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ProducerCell
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev M := aspis_core.field.M31
abbrev V := alloc.vec.Vec M
abbrev Valid := PV_CB_CanonicalM31.Valid
/-- Input read invariant. No condition is imposed on a compressor result. -/
def Reads (columns : Slice V) : Prop :=
  ∀ column vector, Slice.index_usize columns column = ok vector →
    ∀ row word, alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice M) vector row = ok word → Valid word

theorem cell (ops : ExternalFuns) (columns : Slice V) (column row : Usize)
    (offset : M) (vc : Reads columns) (vo : Valid offset) :
    PV_CB_ProducerPost.Good Valid
      (@host_semantic.copy_cell _ (ProverRwDictionaryScalar.selected ops) columns column row offset) := by
  intro out h
  simp only [host_semantic.copy_cell] at h
  split at h
  · cases h
  · rename_i bound
    generalize hr : Slice.index_usize columns column = read at h
    cases read with
    | fail e => simp only [bind_tc_fail] at h; cases h
    | div => simp only [bind_tc_div] at h; cases h
    | ok vector =>
      simp only [bind_tc_ok] at h
      split at h
      · cases h
      · generalize hw : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice M) vector row = word at h
        cases word with
        | fail e => simp only [bind_tc_fail] at h; cases h
        | div => simp only [bind_tc_div] at h; cases h
        | ok input =>
          simp only [bind_tc_ok] at h
          obtain ⟨answer,ha,hv,_⟩ := ProverCommitM31Ops48.add_exact input offset (vc column vector hr row input hw) vo
          change (do let value ← AspisR1ProducerRelease47.field.M31.add input offset; ok (core.result.Result.Ok value)) = ok (.Ok out) at h
          rw [ha] at h
          simp only [bind_tc_ok,Result.ok.injEq,core.result.Result.Ok.injEq] at h
          exact h ▸ hv
#print axioms cell
end R1Z.PV_CB_ProducerCell
