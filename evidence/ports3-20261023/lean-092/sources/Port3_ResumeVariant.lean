import Port3_NativePendingPrefix
import Port3_FinishControl

/-! The variant is derived from the SAME complete source resume return,
without a saved-state provenance or independent decoder run. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_ResumeVariant
open Aeneas Aeneas.Std Result AspisR1Stage2

elab "resume_check" kind:str : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let decl ← Lean.Meta.getLocalDeclFromUserName `accepted
    let args := decl.type.getAppArgs
    let lhs ← Lean.Meta.whnfCore args[1]!
    let lhs ← if lhs.getAppFn.isConstOf ``uncurry then
        Lean.Meta.whnfCore (← Lean.Meta.unfoldDefinition lhs)
      else pure lhs
    let good := match kind.getString with
      | "bind" => lhs.getAppFn.isConstOf ``Bind.bind
      | "guard" => lhs.getAppFn.isConstOf ``ite
      | "try" => lhs.getAppFn.isConstOf ``Bind.bind &&
          (lhs.getAppArgs[lhs.getAppArgs.size-2]!).getAppFn.isConstOf
            ``core.result.Result.Insts.CoreOpsTry.branch
      | _ => false
    unless good do throwError "shape does not match: {lhs.getAppFn}"

theorem guard {A : Type} (c : Prop) [Decidable c] (e : verifier.Error)
    (tail : Result (core.result.Result A verifier.Error)) (out : A)
    (h : (if c then ok (.Err e) else tail)=ok (.Ok out)) :
    ¬c ∧ tail=ok (.Ok out) := by
  by_cases hc : c
  · rw [if_pos hc] at h; cases h
  · rw [if_neg hc] at h; exact ⟨hc,h⟩

theorem source_variant (ops : ResumeOps) {H : Type} (D : aspis_core.digest.Digest32 H)
    (ck proof pub : Slice U8) (variant : transport.Variant) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (accepted : verifier.resumeWithOps ops D ck proof pub variant hash=ok (.Ok (p,a))) :
    p.variant=variant := by
  unfold verifier.resumeWithOps at accepted
  repeat' first
  | (resume_check "try"
     obtain ⟨x, hx, accepted⟩ := Port3_FinishControl.try_success _ _ _ accepted)
  | (resume_check "guard"
     obtain ⟨hc, accepted⟩ := guard _ _ _ _ accepted)
  | (resume_check "bind"
     obtain ⟨x, hx, accepted⟩ := Port3_FinishControl.bind_success _ _ _ accepted
     try rcases x with ⟨x,y⟩)
  all_goals
    have same := core.result.Result.Ok.inj (Result.ok.inj accepted)
    exact (congrArg (fun pair : verifier.Prepared × verifier.Accumulator => pair.1.variant) same).symm

theorem installed_variant (reserved : Bool) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (accepted : Port3_CheckpointInstall.reader reserved D ck proof pub .S2 hash=ok (.Ok (p,a))) :
    p.variant=.S2 := by
  exact source_variant (CheckpointBytes4Ops.ops reserved) (VTop_Checkpoint.digest D)
    ck proof pub .S2 hash p a
    (Port3_CheckpointInstall.reader_success reserved D ck proof pub .S2 hash p a accepted)

#print axioms source_variant
#print axioms installed_variant
end AspisR1.Port3_ResumeVariant
end
