import R1Z.PV_RunJoin_ClaimPolynomial49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimModelCell49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverRwDictionaryTower (fromW)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (c : Nat → Nat → Old.Q) (hc : ∀ l,l<29 → ∀ j,j<1024 → Canonical (c l j))
    (l : Fin 29) (x y : Old.Q) (hx : Canonical x) (hy : Canonical y)
    (z : AspisR0.ChordGeometry.Point ProverCommitWideOps48.Exact)
    (hzx : ProverCommitValueRange47.embed (decode x)=z.1.1)
    (hzy : ProverCommitValueRange47.embed (decode y)=z.1.2) :
    ∃ v : Old.Q,
      PV_RunJoin_ClaimProducerCell48.evaluate base heap box (@PV_DL_EncoderSelected.selected (types base) ops)
        ⟨fromW (ProverCommitNativeOps47.embedded x),fromW (ProverCommitNativeOps47.embedded y)⟩
        (PV_RunJoin_CoefficientsWeight46.column (fun j => fromW (ProverCommitNativeOps47.embedded (c l.val j))))=
          ok (fromW (ProverCommitNativeOps47.embedded v)) ∧ Canonical v ∧
      ProverCommitValueRange47.embed (decode v)=AspisR0.Chord.evalMessage
        (R0P.SemSource.coeffsOf AspisR1.rowEquiv (PV_RunJoin_ClaimPolynomial49.trace c) l) z := by
  obtain ⟨v,hv,hcv,hdv⟩ := PV_RunJoin_ClaimColumn49.complete base heap box ops (c l.val) (hc l.val l.isLt) x y hx hy
  refine ⟨v,hv,hcv,?_⟩
  calc
    _ = ProverCommitY1Bytes47.model (fun j => c l.val (AspisR1.rowNat j)) x y := by
      rw [hdv,ProverCommitY1Bytes47.model,ProverCommitEval47.message_embed]
    _ = _ := PV_RunJoin_ClaimPolynomial49.message c l x y z hzx hzy
#print axioms complete
end R1Z.PV_RunJoin_ClaimModelCell49
