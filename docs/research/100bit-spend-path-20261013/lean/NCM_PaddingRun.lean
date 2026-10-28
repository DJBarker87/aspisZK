import NCM_PaddingValue

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_PaddingRun
open Aeneas Aeneas.Std Result NCE_PaddingCuts

def guard {Frame : Type} (native : Body Frame) (padding : Slice U8) (frame : Frame) : Result (Bool × Frame) := do
  let ce ← core.slice.Slice.chunks_exact padding 8#usize
  let out ← run native (ce.chunks.length+1) (ce,frame)
  ok (!out.1,out.2.2)

/-- The actual constructor and native iterator return determine the source
padding guard. Its caller frame is preserved on either Boolean outcome. -/
theorem observation {Frame : Type} (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (native : Body Frame)
    (cut : NCE_Native_Padding (NCM_PaddingPredicate.predicate base D) native)
    (padding : Slice U8) (words : Nat) (length : padding.val.length = 8*words) (frame : Frame) :
    guard native padding frame =
      ok (MultiproofConePadding.scan words (MultiproofConeCanonical.bytesOf padding.val),frame) := by
  obtain ⟨ce,after,constructed,returned⟩ := NCM_PaddingValue.observation base D native cut padding words length frame
  simp only [guard,constructed,bind_tc_ok,returned,Bool.not_not]

#print axioms observation
end AspisR1.NCM_PaddingRun
end
