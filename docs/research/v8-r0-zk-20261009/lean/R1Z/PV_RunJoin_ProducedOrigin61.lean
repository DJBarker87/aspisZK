import R1Z.PV_RunJoin_CaptureBoundary61
import R1Z.PV_RunJoin_SourceOriginGeneric60
import R1Z.PV_RunJoin_MaterialPointOrigins51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ProducedOrigin61
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem origin (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∀ p, PV_RunJoin_ActualProvenance60.Produced p → PV_RunJoin_BuildOrigin60.Origin p :=
  @PV_RunJoin_SourceOriginGeneric60.produced (types base) (selected base heap box ops)
    (PV_RunJoin_CaptureBoundary61.selected_mapErr base heap box ops)

/-- The actual captured source phase reached both circle calls, without an
extra map_err installation or a new producer hypothesis. -/
theorem circles (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∀ p, PV_RunJoin_ActualProvenance60.Produced p →
      PV_RunJoin_CircleProduced51.Produced
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 p.sem := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  intro p hp
  obtain ⟨_,compiled,noised,maskOnly,d,g,padding,initial,_,built⟩ := origin base heap box ops p hp
  obtain ⟨before,middle,z0,z1,f25,f26,h25,h26,hz,_⟩ :=
    PV_RunJoin_MaterialPointOrigins51.complete base heap box ops
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
      prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
      p.public1 compiled noised maskOnly d g padding initial p.backend p.hash .S2 p.sem built
  exact ⟨before,middle,z0,z1,f25,f26,h25,h26,hz⟩

#print axioms origin
#print axioms circles
end R1Z.PV_RunJoin_ProducedOrigin61
