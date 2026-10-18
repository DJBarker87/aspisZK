import R1SumcheckSuffixCausality
import Init.Data.List.Lemmas
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Omega

namespace R1SumcheckCausality

/-- Apply a finite sequence of writes to the sumcheck evaluation point. -/
def pointWrite {X : Type} (point : Fin 10 → X) (i : Fin 10) (value : X) : Fin 10 → X :=
  fun j => if j = i then value else point j

def applyPointUpdates {X : Type} (point : Fin 10 → X)
    (updates : List (Fin 10 × X)) : Fin 10 → X :=
  updates.foldl (fun state u => pointWrite state u.1 u.2) point

/-- Every scheduled write is to the current or a later round. -/
def FuturePointUpdates (round : Nat) (updates : List (Fin 10 × X)) : Prop :=
  ∀ u ∈ updates, round ≤ u.1.val

/-- Later-round point writes leave every earlier coordinate unchanged. -/
theorem applyPointUpdates_preserves_prefix {X : Type}
    (round : Nat) (point : Fin 10 → X) (updates : List (Fin 10 × X))
    (hfuture : FuturePointUpdates round updates) :
    SamePrefix round point (applyPointUpdates point updates) := by
  induction updates generalizing point with
  | nil => intro i hi; rfl
  | cons u us ih =>
      simp only [applyPointUpdates, List.foldl_cons]
      have htail : FuturePointUpdates round us := by
        intro v hv
        exact hfuture v (by simp [hv])
      have hpre := ih (pointWrite point u.1 u.2) htail
      intro i hi
      have hu : round ≤ u.1.val := hfuture u (by simp)
      have hne : i ≠ u.1 := by
        intro he
        have hv := congrArg Fin.val he
        omega
      calc
        point i = pointWrite point u.1 u.2 i := by simp [pointWrite, hne]
        _ = applyPointUpdates (pointWrite point u.1 u.2) us i := hpre i hi

theorem roundPayload_stable_after_future_updates {X Y Poly Bytes : Type}
    (round : Nat) (samples : List X) (assignments : List (Fin 10 → X))
    (oracle : (Fin 10 → X) → Y) (aggregate : List Y → Y)
    (interpolate : List Y → Poly) (encode : Poly → Bytes)
    (header : Bytes) (append : Bytes → Bytes → Bytes)
    (point : Fin 10 → X) (updates : List (Fin 10 × X))
    (hfuture : FuturePointUpdates round updates) :
    frameRow header append
      (roundPayload round samples assignments oracle aggregate interpolate encode point) =
    frameRow header append
      (roundPayload round samples assignments oracle aggregate interpolate encode
        (applyPointUpdates point updates)) := by
  apply framedRound_suffix_irrelevant
  exact applyPointUpdates_preserves_prefix round point updates hfuture

#print axioms applyPointUpdates_preserves_prefix
#print axioms roundPayload_stable_after_future_updates

end R1SumcheckCausality
