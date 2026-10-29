import R1Z.PV_RunJoin_ClaimColumn49
import R1Z.PV_RunJoin_ClaimEvaluationList49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimValues49
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
    (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Fin 29 → Old.Q,
      PV_RunJoin_ClaimImage48.values
        (PV_RunJoin_ClaimProducerCell48.evaluate base heap box (@PV_DL_EncoderSelected.selected (types base) ops)
          ⟨fromW (ProverCommitNativeOps47.embedded x),fromW (ProverCommitNativeOps47.embedded y)⟩)
        (PV_RunJoin_CoefficientsWeight46.payload (fun l j => fromW (ProverCommitNativeOps47.embedded (c l j))) 0 29)=
          ok (List.ofFn (fun l : Fin 29 => fromW (ProverCommitNativeOps47.embedded (z l)))) ∧
      (∀ l,Canonical (z l)) ∧
      (∀ l,decode (z l)=ProverCommitEval47.messageEval
        (fun j : Fin 1024 => decode (c l.val (AspisR1.rowNat j.val))) (decode x) (decode y)) := by
  have cell := fun l : Fin 29 => PV_RunJoin_ClaimColumn49.complete base heap box ops
    (c l.val) (hc l.val l.isLt) x y hx hy
  choose z he hcz hd using cell
  let zs : Nat → Old.Q := fun l => if hl : l<29 then z ⟨l,hl⟩ else zero
  have hcell : ∀ l,l<29 →
      PV_RunJoin_ClaimProducerCell48.evaluate base heap box (@PV_DL_EncoderSelected.selected (types base) ops)
        ⟨fromW (ProverCommitNativeOps47.embedded x),fromW (ProverCommitNativeOps47.embedded y)⟩
        (PV_RunJoin_CoefficientsWeight46.column (fun j => fromW (ProverCommitNativeOps47.embedded (c l j))))=
          ok (fromW (ProverCommitNativeOps47.embedded (zs l))) := by
    intro l hl
    simpa only [zs,dif_pos hl] using he ⟨l,hl⟩
  refine ⟨z,?_,hcz,hd⟩
  rw [PV_RunJoin_ClaimEvaluationList49.complete _ _ _ hcell 0 29 (by omega),
    PV_RunJoin_OrderedList48.complete]
  simp only [Nat.zero_add,zs,dif_pos (Fin.isLt _)]
#print axioms complete
end R1Z.PV_RunJoin_ClaimValues49
