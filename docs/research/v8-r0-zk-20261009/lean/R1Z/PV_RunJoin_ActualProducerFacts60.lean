import R1Z.PV_RunJoin_ActualOrigin60
import R1Z.PV_RunJoin_MaterialBackendTrace60
import R1Z.PV_RunJoin_MaterialAlphaProduced51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualProducerFacts60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem alpha (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box (PV_RunJoin_MapErrInstalled60.install ops)
    ∀ p, PV_RunJoin_ActualProvenance60.Produced p → ∀ i,i<10 →
      ProverCommitSubfieldOps47.Canonical ((PV_RunJoin_ActualRun.data p).p i) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box (PV_RunJoin_MapErrInstalled60.install ops)
  intro p hp
  obtain ⟨_,compiled,noised,maskOnly,d,g,padding,initial,_,built⟩ :=
    PV_RunJoin_ActualOrigin60.actual base heap box ops p hp
  exact PV_RunJoin_MaterialAlphaProduced51.complete base heap box (PV_RunJoin_MapErrInstalled60.install ops)
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments p.public1 compiled noised maskOnly
    d g padding initial p.backend p.hash .S2 p.sem built

/-- Actual caller extraction: the C1/C2 equations are conclusions. The full
hinput link still needs column lengths and the stored-column cell transport. -/
theorem backendTrace (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box (PV_RunJoin_MapErrInstalled60.install ops)
    ∀ p, PV_RunJoin_ActualProvenance60.Produced p →
      ∃ (initial : prover.Backend)
        (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
        (d g : Array aspis_core.field.QM31 1024#usize),
        initial.messages.length=29 ∧
        PV_RunJoin_BackendBuildTrace60.Trace
          prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments columns d g initial p.backend p.sem := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box (PV_RunJoin_MapErrInstalled60.install ops)
  intro p hp
  obtain ⟨_,compiled,noised,maskOnly,d,g,padding,initial,hlen,built⟩ :=
    PV_RunJoin_ActualOrigin60.actual base heap box ops p hp
  have h := PV_RunJoin_MaterialBackendTrace60.complete base heap box (PV_RunJoin_MapErrInstalled60.install ops)
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments p.public1 compiled noised maskOnly
    d g padding initial p.hash .S2
  rw [built] at h
  obtain ⟨columns,h⟩ := h
  exact ⟨initial,columns,d,g,hlen,h⟩

#print axioms alpha
#print axioms backendTrace
end R1Z.PV_RunJoin_ActualProducerFacts60
