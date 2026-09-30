import AspisV8R19.CausalFirstHitUnionBound

/-! A finite-tape causal union bound.

At step `i`, the bad predicate may depend on every earlier tape cell and the
current cell, but not on future cells.  A per-prefix bound for a fresh uniform
current cell therefore lifts to the complete tape and then to a first-hit
union bound.  This is generic probability plumbing: it does not identify a
source transcript, establish frame injectivity, or claim oracle freshness. -/
set_option autoImplicit false
namespace AspisV8R19.CausalTapeFirstHit

open OracleResampling CausalFirstHitUnionBound

variable {S : Type*} [Fintype S] [Nonempty S]

def past {n : Nat} (tape : Fin n → S) (i : Fin n) : Fin i.val → S :=
  fun j => tape ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

def event {n : Nat}
    (bad : (i : Fin n) → (Fin i.val → S) → S → Prop)
    (i : Fin n) (tape : Fin n → S) : Prop :=
  bad i (past tape i) (tape i)

theorem past_update_self {n : Nat} (tape : Fin n → S) (i : Fin n) (s : S) :
    past (Function.update tape i s) i = past tape i := by
  funext j
  have hne : (⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ : Fin n) ≠ i := by
    intro h
    exact (Nat.ne_of_lt j.isLt) (congrArg Fin.val h)
  simp only [past, Function.update_of_ne hne]

theorem mean_event_eq_prefix_mean {n : Nat}
    (bad : (i : Fin n) → (Fin i.val → S) → S → Prop)
    (i : Fin n) :
    mean (fun tape : Fin n → S =>
      indicator (event bad i tape)) =
      mean (fun tape : Fin n → S =>
        mean (fun s : S => indicator (bad i (past tape i) s))) := by
  rw [resample_cell i, mean_comm]
  apply mean_congr
  intro tape
  apply mean_congr
  intro s
  simp only [event, past_update_self]
  simp

theorem mean_event_le {n : Nat}
    (bad : (i : Fin n) → (Fin i.val → S) → S → Prop)
    (bound : Fin n → ℚ)
    (hbound : ∀ i history,
      mean (fun s : S => indicator (bad i history s)) ≤ bound i)
    (i : Fin n) :
    mean (fun tape : Fin n → S => indicator (event bad i tape)) ≤ bound i := by
  rw [mean_event_eq_prefix_mean]
  unfold mean
  apply div_le_iff₀' (by positivity : (0 : ℚ) < Fintype.card (Fin n → S)) |>.mpr
  calc
    ∑ tape : Fin n → S,
        mean (fun s : S => indicator (bad i (past tape i) s)) ≤
        ∑ _tape : Fin n → S, bound i :=
      Finset.sum_le_sum (fun tape _ => hbound i (past tape i))
    _ = Fintype.card (Fin n → S) * bound i := by simp

theorem mean_causal_firstHit_le {n : Nat}
    (bad : (i : Fin n) → (Fin i.val → S) → S → Prop)
    (bound : Fin n → ℚ)
    (hbound : ∀ i history,
      mean (fun s : S => indicator (bad i history s)) ≤ bound i) :
    mean (fun tape : Fin n → S => indicator (∃ i, event bad i tape)) ≤
      ∑ i, bound i := by
  exact mean_firstHit_union_le (fun i tape => event bad i tape) bound
    (fun i => mean_event_le bad bound hbound i)

#print axioms past_update_self
#print axioms mean_event_eq_prefix_mean
#print axioms mean_event_le
#print axioms mean_causal_firstHit_le

end AspisV8R19.CausalTapeFirstHit
