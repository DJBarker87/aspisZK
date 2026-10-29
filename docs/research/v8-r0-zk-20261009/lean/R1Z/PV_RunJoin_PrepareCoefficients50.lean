import R1Z.PV_RunJoin_PrepareActualMaterial50
import R1Z.PV_RunJoin_CoefficientsActual50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareCoefficients50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (Weight toWeight)
open PV_RunJoin_SemanticMaterialInputs50
open PV_RunJoin_CoefficientActualCell50 (Column permuted)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (backend : prover.Backend) (s : Sem)
    (small : backend.messages.length≤14336) :
    ∃ (coefficients : alloc.vec.Vec Column) (kw : Weight),
      (toWeight kw).variant=.S2 ∧ coefficients.val=backend.messages.val.map permuted ∧
      coefficients.length=backend.messages.length ∧
      @prover.prepare_opening (types base) (selected base heap box ops) .S2 hash backend s=
        @PV_RunJoin_PrepareOperations47.run (types base) (selected base heap box ops) .S2 hash backend s
          (ok coefficients) (do let _ ← box .S2 s.alpha s.z;ok (.Ok (toWeight kw)))
          (fun _ x => PV_RunJoin_PrepareActualMaterial50.material heap s kw x) := by
  obtain ⟨coeff,hcoeff,hv,hl⟩ := PV_RunJoin_CoefficientsActual50.complete base heap box ops
    (alloc.vec.Vec.deref backend.messages) small
  obtain ⟨kw,hs,hr⟩ := PV_RunJoin_PrepareActualMaterial50.complete base heap box ops hash backend s
  rw [hcoeff] at hr
  exact ⟨coeff,kw,hs,hv,hl,hr⟩
#print axioms complete
end R1Z.PV_RunJoin_PrepareCoefficients50
