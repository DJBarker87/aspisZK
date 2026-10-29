import R1Z.PV_RunJoin_PrepareClaimsActual50
import R1Z.PV_RunJoin_PreparePrefix48
import R1Z.PV_RunJoin_ClaimActual50
import R1Z.PV_RunJoin_PrepareScalarInstalled49
import R1Z.PV_RunJoin_GammaPowers44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareCanonicalContext50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (Weight toWeight)
open PV_RunJoin_SemanticMaterialInputs50
open PV_RunJoin_CoefficientActualCell50 (Column permuted)
open PV_RunJoin_WeightMap46 (mapResult)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (backend : prover.Backend) (s : Sem)
    (small : backend.messages.length≤14336) :
    let incoming := @PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)
    ∃ (coefficients : alloc.vec.Vec Column) (kw : Weight),
      (toWeight kw).variant=.S2 ∧ coefficients.val=backend.messages.val.map permuted ∧
      coefficients.length=backend.messages.length ∧
      @prover.prepare_opening (types base) (selected base heap box incoming) .S2 hash backend s=
        @PV_RunJoin_PrepareScalarContext49.run (types base) (selected base heap box incoming) .S2 hash backend s
          (ok coefficients) (do let _ ← box .S2 s.alpha s.z;ok (.Ok (toWeight kw)))
          (fun _ x => PV_RunJoin_PrepareActualMaterial50.material heap s kw x)
          PV_RunJoin_ClaimActual50.run
          (fun q _ => mapResult ProverRwDictionaryTower.fromW
            (PV_RunJoin_InactiveFinite48.run 1024 q (PV_RunJoin_WeightCarrier46.state (toWeight kw))
              AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO 0#usize))
          (@PV_RunJoin_PrepareTail48.run (types base) (selected base heap box incoming) .S2 hash backend s)
          (PV_RunJoin_ScalarSource49.retained base heap box incoming
            (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box incoming))) := by
  dsimp only
  let incoming := @PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)
  obtain ⟨coeff,kw,hs,hv,hl,hr⟩ := PV_RunJoin_PrepareClaimsActual50.complete base heap box
    (@PV_RunJoin_GammaPowers44.inputs (types base) ops) hash backend s small
  refine ⟨coeff,kw,hs,hv,hl,?_⟩
  rw [hr,PV_RunJoin_PrepareMaterialContext49.source]
  exact PV_RunJoin_PrepareScalarInstalled49.complete base heap box incoming .S2 hash backend s _ _ _ _ _ _
#print axioms complete
end R1Z.PV_RunJoin_PrepareCanonicalContext50
