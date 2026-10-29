import R1Z.PV_RunJoin_ClaimInstalled48
import R1Z.PV_RunJoin_CoefficientsInstalled46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimCoefficients48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_CoefficientsWeight46 (W Column messages payload)
open PV_RunJoin_WeightMap46 (mapResult)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (p : Nat → Nat → W) :
    ∃ coefficients : alloc.vec.Vec Column,
      @prover.opening_coefficients (types base) (selected base heap box ops) .S2 (messages p)=ok coefficients ∧
      coefficients.val=payload p 0 29 ∧ coefficients.length=29 ∧
      ∀ point : aspis_core.r0.domain.Point W,
        mapResult (fun out : alloc.vec.Vec U8 => out.val)
          (@prover.opening_claim_bytes (types base) (selected base heap box ops)
            (alloc.vec.Vec.deref coefficients) point)=
          mapResult PV_RunJoin_ClaimImage48.bytes
            (PV_RunJoin_ClaimImage48.values
              (PV_RunJoin_ClaimProducerCell48.evaluate base heap box ops point) (payload p 0 29)) := by
  obtain ⟨coefficients,hc,hv,hl⟩ := PV_RunJoin_CoefficientsInstalled46.complete base heap box ops p
  refine ⟨coefficients,hc,hv,hl,?_⟩
  intro point
  have small : (alloc.vec.Vec.deref coefficients).length≤14336 := by
    change coefficients.length≤14336
    omega
  have h := PV_RunJoin_ClaimInstalled48.complete base heap box ops (alloc.vec.Vec.deref coefficients) point small
  change mapResult (fun out : alloc.vec.Vec U8 => out.val) _=mapResult PV_RunJoin_ClaimImage48.bytes
    (PV_RunJoin_ClaimImage48.values _ coefficients.val) at h
  rw [hv] at h
  exact h
#print axioms complete
end R1Z.PV_RunJoin_ClaimCoefficients48
