import R1Z.ProverCommitY1Owner47
import R1Z.ProverCommitLimbBytes47
/-! Pointwise byte image of all lanes of the owned y1 evaluator. The actual
shipped iterator/tape/selector binding is not asserted by this theorem. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitY1Bytes47
open Aeneas Aeneas.Std Result ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitValueRange47
open AspisR1.ExtractedCurrentQM31Exact
attribute [local irreducible] ProverCommitEval47.messageEval ProverCommitEval47.pairEval

abbrev Coefficients := Fin 29 → Nat → Old.Q

def model (q : Nat → Old.Q) (x y : Old.Q) : ProverCommitValueRange47.E :=
  ProverCommitEval47.messageEval (fun j : Fin 1024 => embed (decode (q j.val)))
    (embed (decode x)) (embed (decode y))

/-- No codec-success, producer-success, canonical-input, or model-image
premise: normalization and the complete owned evaluation supply the range. -/
theorem component (q : Nat → Old.Q) (x y : Old.Q) :
    ∃ (z : Old.Q) (hz : Canonical z),
      ProverCommitY1Owner47.run (fun j => ProverCommitNativeOps47.normalize (q j))
        (ProverCommitNativeOps47.normalize x) (ProverCommitNativeOps47.normalize y) =
          ok (ProverCommitNativeOps47.embedded z) ∧
      ProverCommitLimbBytes47.sourceCell z hz=bytes (model q x y) ∧
      AspisR1.FoldedLeafCodec.decodeWide
        ((List.ofFn (ProverCommitLimbBytes47.sourceCell z hz)).map UInt8.toFin)=
          some (model q x y) := by
  obtain ⟨z,hrun,hcanon,hd⟩ := ProverCommitY1Owner47.raw_value q x y
  have hm : embed (decode z)=model q x y := by
    rw [model,ProverCommitEval47.message_embed,hd]
  refine ⟨z,hcanon,hrun,?_,?_⟩
  · rw [ProverCommitLimbBytes47.source_image,hm]
  · rw [ProverCommitLimbBytes47.source_decode,hm]

/-- All 29 y1 coordinates have the reference's exact model byte image. This
is still not a certificate for the complete native simulator generator. -/
theorem every_lane (c : Coefficients) (x y : Old.Q) (lane : Fin 29) :
    ∃ (z : Old.Q) (hz : Canonical z),
      ProverCommitY1Owner47.run (fun j => ProverCommitNativeOps47.normalize (c lane j))
        (ProverCommitNativeOps47.normalize x) (ProverCommitNativeOps47.normalize y) =
          ok (ProverCommitNativeOps47.embedded z) ∧
      ProverCommitLimbBytes47.sourceCell z hz=bytes (model (c lane) x y) ∧
      AspisR1.FoldedLeafCodec.decodeWide
        ((List.ofFn (ProverCommitLimbBytes47.sourceCell z hz)).map UInt8.toFin)=
          some (model (c lane) x y) := component (c lane) x y

#print axioms component
#print axioms every_lane
end R1Z.ProverCommitY1Bytes47
