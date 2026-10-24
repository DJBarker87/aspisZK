import Port9OR_P6Node

/-! Successful-step progress for a PARTIAL native digest. Totalization is used
only as a proof device after success; it is never executed or sampled. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_P6Progress
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConeNodeDomain

def total {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) :
    AspisR1Stage2.aspis_core.digest.Digest32 Hash :=
  {D with digest := fun hash parts => match D.digest hash parts with
    | .ok d => .ok d
    | _ => .ok (Array.repeat 32#usize 0#u8)}

theorem totality {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    HashTotal (Port9OR_P6Node.digest (total D)) hash := by
  intro parts
  cases call : D.digest hash parts <;> exact ⟨_,by simp only [total,Port9OR_P6Node.digest,call]⟩

theorem success {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (code : Code A) (a : A) (ran : erase D hash code=ok a) :
    erase (total D) hash code=ok a := by
  induction code with
  | done b => exact ran
  | step r k ih => cases r with
    | fail e => cases ran
    | div => cases ran
    | ok b => exact ih b ran
  | read parts k ih =>
    cases call : D.digest hash parts with
    | fail e => simp only [erase,call,bind_tc_fail] at ran; cases ran
    | div => simp only [erase,call,bind_tc_div] at ran; cases ran
    | ok b =>
      simp only [erase,call,bind_tc_ok] at ran
      simpa only [erase,total,call,bind_tc_ok] using ih b ran

/-- No totality or digest-agreement premise. Actual success derives the
source's bounds and progress, including exactly the returned scratch. -/
theorem node_progress {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (physical : Slice U8) (s : reference.Scratch) (i w : Usize)
    (domain : RowDomain physical s i w) (active : i.val<s.n.val) (out : reference.Row)
    (ran : reference.binary_step (Port9OR_P6Node.digest D) hash s physical i w=ok out) :
    Progress physical s i w out := by
  have erased := (Port9OR_P6Node.node_source D hash s physical i w).trans ran
  have replaced := success D hash _ out erased
  rw [Port9OR_P6Node.node_source] at replaced
  obtain ⟨other,call,progress⟩ := binary_step_progress (Port9OR_P6Node.digest (total D)) hash
    (totality D hash) physical s i w domain active
  have same : other=out := Result.ok.inj (call.symm.trans replaced)
  exact same ▸ progress

#print axioms totality
#print axioms success
#print axioms node_progress
end AspisR1.Port9OR_P6Progress
end
