import PV_L2C_PaddingNative
set_option autoImplicit false
namespace PV_L2C_PaddingComplete
open PV_L2C_NativeQ PV_L2C_QFold PV_L2C_PaddingNative
inductive Failure where
  | traceShape

def activeScan (active : Fin 1024 → Bool) (padding : Fin 1024 → Q)
    (rows : List (Fin 1024)) : Except Failure Unit :=
  match rows with
  | [] => .ok ()
  | r::rest => if active r && decide (padding r ≠ zero) then .error .traceShape
      else activeScan active padding rest

def applyPadding (active : Fin 1024 → Bool) (h1 padding : Fin 1024 → Q)
    (h1Length paddingLength : Nat) : Except Failure (Fin 1024 → Q) := do
  if h1Length ≠ 1024 ∨ paddingLength ≠ 1024 then throw .traceShape
  activeScan active padding (List.finRange 1024)
  if tableSum (inactiveTable active padding) ≠ zero then throw .traceShape
  pure (fun r => addQ (h1 r) (padding r))

theorem scan (active : Fin 1024 → Bool) (padding : Fin 1024 → Q)
    (h : ∀ r, (active r && decide (padding r ≠ zero)) = false)
    (rows : List (Fin 1024)) : activeScan active padding rows = .ok () := by
  induction rows with
  | nil => rfl
  | cons r rest ih => rw [activeScan,h r];exact ih
#print axioms scan

theorem complete (active : Fin 1024 → Bool) (d : Fin 1024) (random h1 : Fin 1024 → Q)
    (hc : ∀ r, Canonical (random r)) (hd : active d = false) :
    applyPadding active h1 (rebalance active d (sample active d random)) 1024 1024 =
      .ok (fun r => addQ (h1 r) (rebalance active d (sample active d random) r)) := by
  obtain ⟨ha,hs⟩ := guard_outcomes active d random hc hd
  unfold applyPadding
  simp only [ne_eq,not_true_eq_false,or_self,↓reduceIte]
  rw [scan active _ ha]
  simp only [Except.bind]
  have hz : tableSum (inactiveTable active (rebalance active d (sample active d random))) = zero := by
    simpa only [decide_eq_false_iff_not,not_not] using hs
  rw [hz]
  simp
#print axioms complete
end PV_L2C_PaddingComplete
