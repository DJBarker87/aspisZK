import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
# Deterministic growth of retained query schedules

The collector starts with a finite set of already seen indices and unions each
retained schedule into it. A contained step is determined by that step's actual
earlier retained schedules. No distribution is imposed on the schedules, and no
assumption about acceptance preserving uniform queries occurs here.
-/

namespace AspisV8.CensoredCollectorGrowth

variable {I : Type*} [DecidableEq I]

/-- The actual recursive collector, including an arbitrary earlier state. -/
def collectFrom (seen : Finset I) : List (Finset I) → Finset I
  | [] => seen
  | schedule :: rest => collectFrom (seen ∪ schedule) rest

/-- Some retained schedule adds no new index at its own causal prefix. -/
def ContainedStep (seen : Finset I) : List (Finset I) → Prop
  | [] => False
  | schedule :: rest => schedule ⊆ seen ∨ ContainedStep (seen ∪ schedule) rest

/-- The recursive event is exactly an occurrence at an explicit earlier prefix. -/
theorem contained_iff_prefix (seen : Finset I) (trace : List (Finset I)) :
    ContainedStep seen trace ↔
      ∃ earlier schedule later,
        trace = earlier ++ schedule :: later ∧
        schedule ⊆ collectFrom seen earlier := by
  induction trace generalizing seen with
  | nil =>
      constructor
      · exact False.elim
      · rintro ⟨earlier, schedule, later, heq, _⟩
        have hlen := congrArg List.length heq
        simp only [List.length_nil, List.length_append, List.length_cons] at hlen
        omega
  | cons schedule rest ih =>
      constructor
      · intro h
        rcases h with h | h
        · exact ⟨[], schedule, rest, rfl, h⟩
        · rcases (ih (seen ∪ schedule)).mp h with ⟨earlier, next, later, heq, hsub⟩
          exact ⟨schedule :: earlier, next, later, congrArg (List.cons schedule) heq, hsub⟩
      · rintro ⟨earlier, next, later, heq, hsub⟩
        cases earlier with
        | nil =>
            have h := List.cons.inj heq
            exact Or.inl (h.1 ▸ hsub)
        | cons first earlier =>
            have h := List.cons.inj heq
            have hfirst := h.1
            subst first
            exact Or.inr ((ih (seen ∪ schedule)).mpr ⟨earlier, next, later, h.2, hsub⟩)

/-- Any schedule not contained in the current state strictly grows that state. -/
theorem union_card_grows (seen schedule : Finset I) (fresh : ¬ schedule ⊆ seen) :
    seen.card + 1 ≤ (seen ∪ schedule).card := by
  have proper : seen ⊂ seen ∪ schedule := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
    intro heq
    apply fresh
    intro x hx
    rw [heq]
    exact Finset.mem_union_right seen hx
  exact Finset.card_lt_card proper

/-- Every non-contained retained step adds at least one genuinely new index. -/
theorem fresh_trace_growth (seen : Finset I) (trace : List (Finset I))
    (fresh : ¬ ContainedStep seen trace) :
    seen.card + trace.length ≤ (collectFrom seen trace).card := by
  induction trace generalizing seen with
  | nil => exact Nat.le_refl _
  | cons schedule rest ih =>
      have headFresh : ¬ schedule ⊆ seen := fun h => fresh (Or.inl h)
      have tailFresh : ¬ ContainedStep (seen ∪ schedule) rest := fun h => fresh (Or.inr h)
      have hgrow := union_card_grows seen schedule headFresh
      have htail := ih (seen ∪ schedule) tailFresh
      change seen.card + (rest.length + 1) ≤ (collectFrom (seen ∪ schedule) rest).card
      omega

/-- Empty-start sharpening: the first retained q-set contributes all q indices. -/
theorem empty_start_growth (q : Nat) (trace : List (Finset I))
    (nonempty : trace ≠ [])
    (width : ∀ schedule ∈ trace, schedule.card = q)
    (fresh : ¬ ContainedStep ∅ trace) :
    q + trace.length - 1 ≤ (collectFrom ∅ trace).card := by
  cases trace with
  | nil => exact (nonempty rfl).elim
  | cons schedule rest =>
      have hcard : schedule.card = q := width schedule (List.mem_cons_self ..)
      have tailFresh : ¬ ContainedStep schedule rest := by
        intro h
        apply fresh
        exact Or.inr (by simpa only [Finset.empty_union] using h)
      have hgrow := fresh_trace_growth schedule rest tailFresh
      simp only [collectFrom, Finset.empty_union, List.length_cons]
      rw [hcard] at hgrow
      omega

/-- Too many retained q-sets inside a capped union force an actual contained step. -/
theorem capped_trace_contains (q cap : Nat) (trace : List (Finset I))
    (positive : 0 < q) (width_cap : q ≤ cap)
    (width : ∀ schedule ∈ trace, schedule.card = q)
    (capped : (collectFrom ∅ trace).card ≤ cap)
    (long : cap - q + 2 ≤ trace.length) :
    ContainedStep ∅ trace := by
  by_contra fresh
  have nonempty : trace ≠ [] := by
    intro hempty
    rw [hempty] at long
    simp only [List.length_nil] at long
    omega
  have hgrow := empty_start_growth q trace nonempty width fresh
  omega

/-- q22/cap255: 235 retained schedules force containment at one genuine prefix. -/
theorem q22_cap255_prefix (trace : List (Finset I))
    (width : ∀ schedule ∈ trace, schedule.card = 22)
    (capped : (collectFrom ∅ trace).card ≤ 255)
    (long : 235 ≤ trace.length) :
    ∃ earlier schedule later,
      trace = earlier ++ schedule :: later ∧
      schedule ⊆ collectFrom ∅ earlier := by
  apply (contained_iff_prefix ∅ trace).mp
  exact capped_trace_contains 22 255 trace (by omega) (by omega) width capped long

end AspisV8.CensoredCollectorGrowth

#print axioms AspisV8.CensoredCollectorGrowth.contained_iff_prefix
#print axioms AspisV8.CensoredCollectorGrowth.union_card_grows
#print axioms AspisV8.CensoredCollectorGrowth.fresh_trace_growth
#print axioms AspisV8.CensoredCollectorGrowth.empty_start_growth
#print axioms AspisV8.CensoredCollectorGrowth.capped_trace_contains
#print axioms AspisV8.CensoredCollectorGrowth.q22_cap255_prefix
