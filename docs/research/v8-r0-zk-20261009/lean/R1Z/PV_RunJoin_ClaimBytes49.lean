import R1Z.PV_RunJoin_ClaimValues49
import R1Z.PV_RunJoin_ClaimInstalled48
import R1Z.PV_RunJoin_CoefficientsInstalled46
import R1Z.PV_RunJoin_ResultImage49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimBytes49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverRwDictionaryTower (fromW)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open PV_RunJoin_CoefficientsWeight46 (Column messages)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (c : Nat → Nat → Old.Q) (hc : ∀ l,l<29 → ∀ j,j<1024 → Canonical (c l j))
    (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    let encOps := @PV_DL_EncoderSelected.selected (types base) ops
    ∃ (coefficients : alloc.vec.Vec Column) (y1 : alloc.vec.Vec U8) (z : Fin 29 → Old.Q),
      @prover.opening_coefficients (types base) (selected base heap box encOps) .S2
        (messages (fun l j => fromW (ProverCommitNativeOps47.embedded (c l j))))=ok coefficients ∧
      coefficients.val=PV_RunJoin_CoefficientsWeight46.payload
        (fun l j => fromW (ProverCommitNativeOps47.embedded (c l j))) 0 29 ∧
      coefficients.length=29 ∧
      @prover.opening_claim_bytes (types base) (selected base heap box encOps) (alloc.vec.Vec.deref coefficients)
        ⟨fromW (ProverCommitNativeOps47.embedded x),fromW (ProverCommitNativeOps47.embedded y)⟩=ok y1 ∧
      y1.val=PV_RunJoin_ClaimImage48.bytes
        (List.ofFn (fun l : Fin 29 => fromW (ProverCommitNativeOps47.embedded (z l)))) ∧
      (∀ l,Canonical (z l)) ∧
      (∀ l,decode (z l)=ProverCommitEval47.messageEval
        (fun j : Fin 1024 => decode (c l.val (AspisR1.rowNat j.val))) (decode x) (decode y)) := by
  dsimp only
  obtain ⟨coefficients,hcoeff,hv,hl⟩ := PV_RunJoin_CoefficientsInstalled46.complete base heap box
    (@PV_DL_EncoderSelected.selected (types base) ops) (fun l j => fromW (ProverCommitNativeOps47.embedded (c l j)))
  obtain ⟨z,hvalues,hcz,hdz⟩ := PV_RunJoin_ClaimValues49.complete base heap box ops c hc x y hx hy
  have small : (alloc.vec.Vec.deref coefficients).length≤14336 := by
    change coefficients.length≤14336
    rw [hl];omega
  have image := PV_RunJoin_ClaimInstalled48.complete base heap box
    (@PV_DL_EncoderSelected.selected (types base) ops) (alloc.vec.Vec.deref coefficients)
    ⟨fromW (ProverCommitNativeOps47.embedded x),fromW (ProverCommitNativeOps47.embedded y)⟩ small
  have listval : (alloc.vec.Vec.deref coefficients).val=PV_RunJoin_CoefficientsWeight46.payload
      (fun l j => fromW (ProverCommitNativeOps47.embedded (c l j))) 0 29 := hv
  rw [listval,hvalues] at image
  obtain ⟨y1,hy1,hyv⟩ := PV_RunJoin_ResultImage49.success _ _ _ image
  exact ⟨coefficients,y1,z,hcoeff,hv,hl,hy1,hyv,hcz,hdz⟩
#print axioms complete
end R1Z.PV_RunJoin_ClaimBytes49
