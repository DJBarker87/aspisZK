import F3K_OpeningSpine
import F3K_CodeBind
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_PrepareLog
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
attribute [local irreducible] PreparedScalarEffects.scalar PreparedScalarEffects.scalar_k
  PreparedQueryEffects.queries PreparedHashEffects.new

theorem spine {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedScratchModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {sem : r1_semantic.Verified Hash} {v : verifier.View} {hash : Hash} {p : OraclePortCompactDraft.Parsed}
    {out : verifier.Prepared} {scratch : Array aspis_core.field.WideExact 29#usize}
    (s : F3K_OpeningSpine.Spine D B embed sem v hash p out scratch)
    (variant : v.variant=.S2) (input : Array aspis_core.field.WideExact 29#usize) :
    observe (run (PreparedSourceEffects.prepare
      (preparationEffects B (Query31ConcreteMaterializedSchedule.concreteBoundaries
        Query31ConcreteDriverTraceFacts.sourceDefaultState embed)) D sem v hash input)).1=
      observe (run (PreparedHashEffects.new effects D hash sem.transcript.state v.variant)).1 ++
      F3K_OpeningCalls.log s.c := by
  have hn : erase (PreparedHashEffects.new effects D hash sem.transcript.state v.variant)=ok s.c.t0 :=
    (new_erasure D hash sem.transcript.state v.variant).trans s.seed
  have h27 : erase (PreparedScalarEffects.scalar effects B.sampling D s.c.t0 27#u8 v.y1 true)=ok (s.c.gamma,s.c.t1) :=
    (scalar_erasure B.sampling D s.c.t0 27#u8 v.y1 true).trans s.c.firstCall
  have h28 : erase (PreparedScalarEffects.scalar effects B.sampling D s.c.t1 28#u8 (Array.to_slice s.c.inactive) false)=ok (s.c.kappa,s.c.t2) :=
    (scalar_erasure B.sampling D s.c.t1 28#u8 (Array.to_slice s.c.inactive) false).trans s.c.secondCall
  have h29 : erase (PreparedScalarEffects.scalar effects B.sampling D s.c.t2 29#u8 v.round0 false)=ok (s.c.alpha0,s.c.t3) :=
    (scalar_erasure B.sampling D s.c.t2 29#u8 v.round0 false).trans s.c.thirdCall
  have h30 : erase (PreparedScalarEffects.scalar effects B.sampling D s.c.t3 30#u8 s.c.second.deref false)=ok (s.c.alpha1,s.c.t4) :=
    (scalar_erasure B.sampling D s.c.t3 30#u8 s.c.second.deref false).trans s.c.fourthCall
  have hq : erase (PreparedQueryEffects.queries effects
      (Query31ConcreteMaterializedSchedule.concreteBoundaries Query31ConcreteDriverTraceFacts.sourceDefaultState embed)
      D s.c.t4 31#u8 v.final_message)=ok (.Ok s.c.queries,s.c.t5) :=
    (queries_erasure _ D s.c.t4 31#u8 v.final_message).trans s.c.queryCall
  have hr : erase (PreparedScalarEffects.scalar_k effects B.sampling D s.c.t5 32#u8 PreparedScratchReachability.emptyPayload)=ok (s.c.rho,s.c.t6) :=
    (scalar_k_erasure B.sampling D s.c.t5 32#u8 PreparedScratchReachability.emptyPayload).trans s.c.rhoCall
  have folds : transport.Variant.folds v.variant=ok (2#usize) := by
    rw [variant]
    simp [transport.Variant.folds,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
      transport.Variant.read_discriminant]
  have capacity : 32#usize+224#usize=ok (256#usize) := by
    obtain ⟨z,hz,hval⟩ := Aeneas.Std.spec_imp_exists
      (@UScalar.add_spec .Usize (32#usize) (224#usize) (by scalar_tac))
    have same : z=256#usize := by apply UScalar.eq_of_val_eq;scalar_tac
    simpa only [same] using hz
  have row32 : 31#u8+1#u8=ok (32#u8) := rfl
  unfold PreparedSourceEffects.prepare
  simp only [preparationEffects]
  erw [F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ hn]
  erw [F3K_CodeBind.success _ _ _ h27]
  erw [F3K_CodeStep.lift_success _ _ s.c.inactiveCall]
  erw [F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ h28]
  erw [F3K_CodeBind.success _ _ _ h29]
  erw [F3K_CodeStep.lift_success _ _ folds]
  simp only [if_pos rfl]
  erw [F3K_CodeStep.lift_success _ _ capacity]
  erw [F3K_CodeStep.lift_success _ _ s.unwrapped]
  erw [F3K_CodeStep.pure_step]
  erw [F3K_CodeStep.lift_success _ _ s.first]
  erw [F3K_CodeStep.lift_success _ _ s.second]
  erw [F3K_CodeBind.success _ _ _ h30]
  erw [F3K_CodeBind.success _ _ _ hq]
  simp only [core.result.Result.Insts.CoreOpsTry.branch]
  erw [F3K_CodeStep.pure_step]
  erw [F3K_CodeStep.lift_success _ _ row32]
  erw [F3K_CodeStep.pure_step]
  erw [F3K_CodeBind.success _ _ _ hr]
  erw [F3K_CodeStep.lift_success _ _ s.powers]
  erw [F3K_CodeStep.lift_success _ _ s.claim]
  simp only [core.result.Result.Insts.CoreOpsTry.branch]
  erw [F3K_CodeStep.pure_step]
  erw [F3K_CodeStep.pure_step]
  simp only [Bind.bind,PreparedHashCode.bind,liftM,MonadLift.monadLift,MonadLiftT.monadLift,
    Pure.pure,run,observe,List.flatMap_nil,List.append_nil,F3K_OpeningCalls.log,List.append_assoc]

#print axioms spine
end AspisR1.F3K_PrepareLog
end
