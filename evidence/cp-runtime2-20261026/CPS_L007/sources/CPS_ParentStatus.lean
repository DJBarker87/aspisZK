import CPP_AtomicRecordNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPS_ParentStatus
open Aeneas Aeneas.Std Result Hist_Store CPP_Atomic
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Parent status comes from the final outer/inner Result, never from a CPI. -/
def success {B : Type} : Reply B → Bool
  | .ok (.Ok _) => true
  | _ => false

theorem success_iff {B : Type} (reply : Reply B) :
    success reply = true ↔ committed reply := by
  cases reply with
  | fail error => simp [success,committed]
  | div => simp [success,committed]
  | ok result => cases result <;> simp [success,committed]

theorem settled_status {B : Type} (before : Store) (tentative : Output B) :
    success (settle before tentative).2.2 = success tentative.2.2 := by
  rw [CPP_AtomicLaws.reply]

theorem retained_sites_iff {A B : Type} (reply : Reply B)
    (sites : List (Hir_ProvenanceModel.CallAt A)) :
    CPP_AtomicRecord.keep reply sites = if success reply then sites else [] := by
  cases reply with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

theorem failure_image {B : Type} (before : Store) (tentative : Output B)
    (failed : success tentative.2.2 = false) :
    settle before tentative = (before,[.rollback],tentative.2.2) := by
  apply CPP_AtomicLaws.rollback
  intro committed
  have yes := (success_iff tentative.2.2).mpr committed
  rw [failed] at yes
  cases yes

theorem success_image {B : Type} (before : Store) (tentative : Output B)
    (accepted : success tentative.2.2 = true) : settle before tentative = tentative :=
  CPP_AtomicLaws.commit before tentative ((success_iff _).mp accepted)

#print axioms success_iff
#print axioms settled_status
#print axioms retained_sites_iff
#print axioms failure_image
#print axioms success_image
end AspisR1.CPS_ParentStatus
end
