import F3Q_HashBind
import F3K_OpeningSpine
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
  have seed := (new_erasure D hash sem.transcript.state v.variant).trans spine.seed
  have first := (scalar_erasure B.sampling D spine.c.t0 27#u8 v.y1 true).trans spine.c.firstCall
  have second := (scalar_erasure B.sampling D spine.c.t1 28#u8 (Array.to_slice spine.c.inactive) false).trans spine.c.secondCall
  have third := (scalar_erasure B.sampling D spine.c.t2 29#u8 v.round0 false).trans spine.c.thirdCall
  have fourth := (scalar_erasure B.sampling D spine.c.t3 30#u8 spine.c.second.deref false).trans spine.c.fourthCall
  have query := (queries_erasure _ D spine.c.t4 31#u8 v.final_message).trans spine.c.queryCall
  have rho := (scalar_k_erasure B.sampling D spine.c.t5 32#u8 PreparedScratchReachability.emptyPayload).trans spine.c.rhoCall
  unfold PreparedSourceEffects.prepare
  simp only [preparationEffects,Bind.bind,liftM,MonadLift.monadLift,MonadLiftT.monadLift,
    AspisR1PublicPreparation.PreparedHashCode.bind,run,lift,r1_wire.SemanticTranscript.impl.state]
  rw [F3Q_HashBind.run_ok _ _ _ seed]
  simp only
  rw [F3Q_HashBind.run_ok _ _ _ first]
  simp only [spine.c.inactiveCall,liftM,MonadLift.monadLift,MonadLiftT.monadLift,
    AspisR1PublicPreparation.PreparedHashCode.bind,run,lift]
  rw [F3Q_HashBind.run_ok _ _ _ second]
  simp only
  rw [F3Q_HashBind.run_ok _ _ _ third]
  simp only [variant,transport.Variant.folds,bind_tc_ok]
  simp only [liftM,MonadLift.monadLift,MonadLiftT.monadLift,AspisR1PublicPreparation.PreparedHashCode.bind,
    run,lift,spine.unwrapped,spine.first,spine.second]
  rw [F3Q_HashBind.run_ok _ _ _ fourth]
  simp only
  rw [F3Q_HashBind.run_ok _ _ _ query]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,liftM,MonadLift.monadLift,MonadLiftT.monadLift,
    AspisR1PublicPreparation.PreparedHashCode.bind,run,lift]
  rw [F3Q_HashBind.run_ok _ _ _ rho]
  simp only [spine.powers,spine.claim,core.result.Result.Insts.CoreOpsTry.branch,
    liftM,MonadLift.monadLift,MonadLiftT.monadLift,AspisR1PublicPreparation.PreparedHashCode.bind,
    Pure.pure,run,lift,List.append_nil,AuS1_Trace.observe_append,F3K_OpeningCalls.log,List.append_assoc]

#print axioms log
end AspisR1.F3Q_OpeningSourceLog
end
