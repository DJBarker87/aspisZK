import R1Z.PV_RunJoin_ClaimHigh66
import R1Z.PV_RunJoin_ClaimBytes49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimDomain66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open ProverCommitPrimitive47 ProverCommitSubfieldOps47

/-- Produce the whole-cell length and every high byte from the coefficient
and point domain. These facts are conclusions, not serializer assumptions. -/
theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (c : Nat → Nat → Old.Q) (hc : ∀ l,l<29 → ∀ j,j<1024 → Canonical (c l j))
    (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    let encOps := @PV_DL_EncoderSelected.selected (types base) ops
    ∃ (coeff : alloc.vec.Vec PV_RunJoin_CoefficientsWeight46.Column) (claim : alloc.vec.Vec U8),
      @prover.opening_coefficients (types base) (selected base heap box encOps) .S2
        (PV_RunJoin_CoefficientsWeight46.messages
          (fun l j => ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded (c l j))))=ok coeff ∧
      @prover.opening_claim_bytes (types base) (selected base heap box encOps)
        (alloc.vec.Vec.deref coeff)
        ⟨ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded x),
         ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded y)⟩=ok claim ∧
      claim.length=32*29 ∧ PV_RunJoin_HighDomain40.HighZero claim.val := by
  dsimp only
  obtain ⟨coeff,claim,z,hcoeff,hv,hl,hclaim,hbytes,hz,hd⟩ :=
    PV_RunJoin_ClaimBytes49.complete base heap box ops c hc x y hx hy
  refine ⟨coeff,claim,hcoeff,hclaim,?_,?_⟩
  · change claim.val.length=32*29
    rw [hbytes,PV_RunJoin_ClaimImage48.length,List.length_ofFn]
  · rw [hbytes]
    simpa only [List.map_ofFn] using PV_RunJoin_ClaimHigh66.high (List.ofFn z)

#print axioms complete
end R1Z.PV_RunJoin_ClaimDomain66
