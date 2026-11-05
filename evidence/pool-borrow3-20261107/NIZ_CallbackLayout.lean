import NIZ_LAYOUT
set_option autoImplicit false
namespace NIZ_CallbackLayout

/-- Source cursor updates in processor.rs:897..941 and pair_processor.rs:126..164. -/
def marker (different rollover : Bool) : Nat :=
  2 + (if different then 1 else 0) + (if rollover then 1 else 0)

def current (different : Bool) : Nat := if different then 2 else 1

def next (different : Bool) : Nat := 2 + (if different then 1 else 0)

theorem pool_before_marker (different rollover : Bool) :
    0 < marker different rollover := by
  cases different <;> cases rollover <;> decide
#print axioms pool_before_marker

theorem current_before_marker (different rollover : Bool) :
    current different < marker different rollover := by
  cases different <;> cases rollover <;> decide
#print axioms current_before_marker

theorem next_before_marker (different : Bool) :
    next different < marker different true := by
  cases different <;> decide
#print axioms next_before_marker

/-- Union of marker reads/writes, marker-creation passed accounts and all token
passed accounts. Metadata seed reads from pool.key do not touch pool data.
This is the source-proposed footprint; native coverage is independently required. -/
def WithdrawalTouched (m t : Nat) : Prop :=
  t = m ∨ t = m+1 ∨ t = m+2 ∨ ∃ offset, offset < 5 ∧ t = m+7+offset

def TransitionHeld (different rollover mutateCurrent : Bool) (g : Nat) : Prop :=
  g = 0 ∨ (mutateCurrent = true ∧ g = current different) ∨
    (rollover = true ∧ g = next different)

/-- All 8 current/rollover/mutate-current cases, including genesis or same-page
alias of anchor/current; neither callback success nor footprint completeness is assumed. -/
theorem withdrawal_disjoint (different rollover mutateCurrent : Bool) (g t : Nat)
    (hg : TransitionHeld different rollover mutateCurrent g)
    (ht : WithdrawalTouched (marker different rollover) t) : g ≠ t := by
  have gb : g < marker different rollover := by
    rcases hg with hg | ⟨hm,hg⟩ | ⟨hr,hg⟩
    · rw [hg]; exact pool_before_marker different rollover
    · rw [hg]; exact current_before_marker different rollover
    · rw [hg, hr]; exact next_before_marker different
  have tb : marker different rollover ≤ t := by
    rcases ht with ht | ht | ht | ⟨o,ho,ht⟩ <;> omega
  omega
#print axioms withdrawal_disjoint

/-- Callback frame composition is pointwise in the actual touched cell set. -/
theorem disjoint_union (held first second : Nat → Prop)
    (h1 : ∀ g t, held g → first t → g ≠ t)
    (h2 : ∀ g t, held g → second t → g ≠ t) :
    ∀ g t, held g → (first t ∨ second t) → g ≠ t := by
  intro g t hg ht
  rcases ht with ht | ht
  · exact h1 g t hg ht
  · exact h2 g t hg ht
#print axioms disjoint_union
end NIZ_CallbackLayout
