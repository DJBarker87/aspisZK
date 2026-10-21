import OraclePortStoredDecisionDraftC4

/-! Global first-occurrence opening maps agree with any authenticated map at
selected indices. No claim is made about unqueried map values. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortPackedChoiceC4
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4

def payload (p : Parsed) (kind pos : Nat) : Bytes :=
  let b := opening p pos
  if kind = 0 then b.take 480 else if kind = 1 then slice b 480 128 else slice b 672 128

theorem position_exists (q : Fin 22 → Fin 262144) (kind pos : Nat) (bound : pos < 22) :
    ∃ first, selectedPosition q kind (index q kind pos) = some first := by
  cases h : selectedPosition q kind (index q kind pos) with
  | some first => exact ⟨first,rfl⟩
  | none =>
    have none : ∀ x ∈ List.range 22, ¬ decide (index q kind x = index q kind pos) :=
      List.find?_eq_none.mp h
    have contradiction := none pos (List.mem_range.mpr bound)
    exact False.elim (contradiction (by simp only [decide_true]))

theorem position_fields (q : Fin 22 → Fin 262144) (kind i first : Nat)
    (h : selectedPosition q kind i = some first) : first < 22 ∧ index q kind first = i := by
  unfold selectedPosition at h
  have sound : decide (index q kind first = i) = true := List.find?_some (p := fun pos : Nat => decide (index q kind pos = i)) (a := first) h
  exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some h),of_decide_eq_true sound⟩

/-- This premise is supplied by indexed Merkle recovery, with the root frame,
trace containment and collision budget instantiated at the actual run. -/
theorem packed_agrees (p : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos < 22 → recovered (index q kind pos) = some (payload p kind pos))
    (pos : Nat) (bound : pos < 22) :
    packed p q kind (index q kind pos) = recovered (index q kind pos) := by
  obtain ⟨first,chosen⟩ := position_exists q kind pos bound
  obtain ⟨firstBound,sameIndex⟩ := position_fields q kind _ first chosen
  have actual := authenticated first firstBound
  rw [sameIndex] at actual
  unfold packed
  rw [chosen,Option.map_some]
  exact actual.symm

/-- Includes folded leaves repeated across the TX1/TX2 split. -/
theorem repeated_payloads (p : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos < 22 → recovered (index q kind pos) = some (payload p kind pos))
    (left right : Nat) (hl : left < 22) (hr : right < 22)
    (sameIndex : index q kind left = index q kind right) :
    payload p kind left = payload p kind right := by
  have a := authenticated left hl
  have b := authenticated right hr
  rw [sameIndex,b] at a
  exact (Option.some.inj a).symm

#print axioms position_exists
#print axioms position_fields
#print axioms packed_agrees
#print axioms repeated_payloads
end AspisR1.OraclePortPackedChoiceC4
end
