import Port10AUTH_Levels
import Port9OR_P6Verify

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_VerifyCut
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

/-- The concrete pure final guard derives its actual returned height scratch. -/
theorem after_success (root : Digest) (nodes : Slice U8) (level : reference.Level) (out : reference.Scratch)
    (success : Port9OR_P6Verify.after root nodes level=ok (true,out)) :
    level=.Done out ∧ MultiproofConeRootGuard.sourceRoot root nodes out=true := by
  cases level with
  | Stop stopped => cases success
  | Done next =>
    unfold Port9OR_P6Verify.after at success
    repeat' first
    | (solve | cases success)
    | uncase_result
    | head_reduce success
    | split at success
    all_goals
      have pair := Result.ok.inj success
      have cursor := congrArg Prod.fst pair
      have state := congrArg Prod.snd pair
      dsimp only at state cursor
      subst out
      subst_vars
      refine ⟨rfl,?_⟩
      exact Port4B_VerifyInstall.final_guard root nodes _ (by assumption) (by assumption) _ (by assumption)
        (by assumption) (of_decide_eq_true cursor)

/-- The accepted emitted verifier supplies the exact reached height, with
all its observations, and the real final root/cursor guard. No height success
or observation relation is an input hypothesis. -/
theorem accepted {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (root : Digest) (s out : reference.Scratch) (nodes : Slice U8)
    (success : erase D hash (Port9OR_P6Verify.code root s nodes)=ok (true,out)) :
    erase D hash (Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes)=ok (.Done out) ∧
    MultiproofConeRootGuard.sourceRoot root nodes out=true ∧
    (Port9OR_Code.trace D hash (Port9OR_P6Verify.code root s nodes)).1=
      (Port9OR_Code.trace D hash (Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes)).1 := by
  unfold Port9OR_P6Verify.code at success ⊢
  by_cases zero : s.n=0#usize
  · simp only [if_pos zero,erase_pure] at success;cases success
  · simp only [if_neg zero] at success ⊢
    by_cases large : s.n>16#usize
    · simp only [if_pos large,erase_pure] at success;cases success
    · simp only [if_neg large,erase_bind,erase_lift] at success
      obtain ⟨valid,validCall,remaining⟩ := Port3_PushFrame.bind_success _ _ _ success
      cases valid with
      | false => cases remaining
      | true =>
        simp only [if_true,erase_bind,erase_lift] at remaining
        obtain ⟨rem,remCall,remaining⟩ := Port3_PushFrame.bind_success _ _ _ remaining
        by_cases aligned : rem != 0#usize
        · simp only [if_pos aligned,erase_pure] at remaining;cases remaining
        · simp only [if_neg aligned,erase_bind,erase_lift] at remaining
          obtain ⟨height,heightCall,afterCall⟩ := Port3_PushFrame.bind_success _ _ _ remaining
          obtain ⟨same,rootOK⟩ := after_success root nodes height out afterCall
          subst height
          refine ⟨heightCall,rootOK,?_⟩
          have heightTrace := Port9OR_Code.trace_value D hash
            (Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes)
          rw [heightCall] at heightTrace
          rw [if_neg large,Port10AUTH_Leaf.lift_bind,validCall]
          change (Port9OR_Code.trace D hash (do
            let rem ← liftResult (Slice.len nodes % 32#usize)
            if rem != 0#usize then pure (false,s) else do
              let out ← Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes
              liftResult (Port9OR_P6Verify.after root nodes out))).1=_
          rw [Port10AUTH_Leaf.lift_bind,remCall]
          change (Port9OR_Code.trace D hash (if rem != 0#usize then pure (false,s) else do
              let out ← Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes
              liftResult (Port9OR_P6Verify.after root nodes out))).1=_
          rw [if_neg aligned,Port10AUTH_Trace.trace_bind]
          generalize eq : Port9OR_Code.trace D hash
            (Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes)=pair at heightTrace ⊢
          obtain ⟨log,result⟩ := pair
          dsimp only at heightTrace
          rw [heightTrace]
          simp only [Port10AUTH_Trace.trace_lift,List.append_nil]

#print axioms after_success
#print axioms accepted
end AspisR1.Port10AUTH_VerifyCut
end
