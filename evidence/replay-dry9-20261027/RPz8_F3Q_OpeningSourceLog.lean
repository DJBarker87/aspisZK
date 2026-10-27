import RPz8_F3Q_HashBind
import RPz8_F3K_PrepareLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_OpeningSourceLog
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem log {Hash : Type} (D : aspis_core.Digest32 Hash) (B : PreparedScratchModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (sem : r1_semantic.Verified Hash) (v : verifier.View) (hash : Hash)
    (p : OraclePortCompactDraft.Parsed) (out : verifier.Prepared)
    (scratch input : Array aspis_core.field.WideExact 29#usize)
    (spine : F3K_OpeningSpine.Spine D B embed sem v hash p out scratch)
    (variant : v.variant=.S2) :
    observe (run (PreparedSourceEffects.prepare
      (preparationEffects B (Query31ConcreteMaterializedSchedule.concreteBoundaries
        Query31ConcreteDriverTraceFacts.sourceDefaultState embed)) D sem v hash input)).1=
      observe (run (PreparedHashEffects.new effects D hash sem.transcript.state v.variant)).1 ++
        F3K_OpeningCalls.log spine.c := by
  exact F3K_PrepareLog.spine spine variant input

#print axioms log
end AspisR1.F3Q_OpeningSourceLog
end
