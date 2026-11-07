import NMV_TotalSnapshot
set_option autoImplicit false
namespace NMV_TotalFold
open NMV_Model NMV_Snapshot NMV_TotalSnapshot

/-- One state is threaded through every step; a stop has no continuation or
post-state and therefore cannot accidentally add a later child's events. -/
def bind {α β : Type} (out : Outcome α) (next : World → α → Outcome β) : Outcome β :=
 match out with
 | .returned world value => next world value
 | .stopped reason trace => .stopped reason trace

theorem bind_assoc {α β γ : Type} (out : Outcome α)
 (f : World → α → Outcome β) (g : World → β → Outcome γ) :
 bind (bind out f) g = bind out (fun w x => bind (f w x) g) := by
 cases out <;> rfl

def snapshots (world : World) (allocation : List Bool) :
    List (Nat × Nat × Nat) → Outcome (List Owned)
 | [] => .returned world []
 | (account,l₁,l₂)::rest =>
   bind (NMV_TotalSnapshot.run world account l₁ l₂ (allocation.headD true))
     (fun w value => bind (snapshots w allocation.tail rest)
       (fun after values => .returned after (value::values)))

theorem frame (world after : World) (allocation : List Bool)
 (plan : List (Nat × Nat × Nat)) (values : List Owned)
 (h : snapshots world allocation plan = .returned after values) :
 after.sdk.state = world.sdk.state := by
 induction plan generalizing world after allocation values with
 | nil => cases h; rfl
 | cons head tail ih =>
   rcases head with ⟨account,l₁,l₂⟩
   dsimp only [snapshots] at h
   cases step : NMV_TotalSnapshot.run world account l₁ l₂ (allocation.headD true) with
   | stopped reason trace => simp only [step,bind] at h; cases h
   | returned middle value =>
     simp only [step,bind] at h
     cases rest : snapshots middle allocation.tail tail with
     | stopped reason trace => simp only [rest,bind] at h; cases h
     | returned last items =>
       simp only [rest,bind] at h
       have tailFrame := ih middle last allocation.tail items rest
       have stepFrame := NMV_TotalSnapshot.returned_frame world middle account l₁ l₂ (allocation.headD true) value step
       cases h
       exact tailFrame.trans stepFrame

theorem count (world after : World) (allocation : List Bool)
 (plan : List (Nat × Nat × Nat)) (values : List Owned)
 (h : snapshots world allocation plan = .returned after values) :
 values.length=plan.length := by
 induction plan generalizing world after allocation values with
 | nil => cases h; rfl
 | cons head tail ih =>
   rcases head with ⟨account,l₁,l₂⟩
   dsimp only [snapshots] at h
   cases step : NMV_TotalSnapshot.run world account l₁ l₂ (allocation.headD true) with
   | stopped reason trace => simp only [step,bind] at h; cases h
   | returned middle value =>
     simp only [step,bind] at h
     cases rest : snapshots middle allocation.tail tail with
     | stopped reason trace => simp only [rest,bind] at h; cases h
     | returned last items =>
       simp only [rest,bind] at h
       have tailCount := ih middle last allocation.tail items rest
       cases h
       simpa only [List.length_cons] using congrArg Nat.succ tailCount

#print axioms bind_assoc
#print axioms frame
#print axioms count
end NMV_TotalFold
