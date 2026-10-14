import R1TraceTable

/-! Trace-record membership as seen through deterministic replay. -/
set_option autoImplicit false
namespace AspisR1.TraceTableMembership

open FS FS2.Duplex
open AspisV8PairedCommitment

variable {I A : Type} [DecidableEq I]

theorem mem_iff_replay_some (H : I → A) (tr : List (I × A))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (a : I) (output : A) :
    (a, output) ∈ tr ↔
      TraceTable.replay (emptyTable : Table I A) tr a = some output := by
  constructor
  · intro hmem
    have haddr : a ∈ tr.map Prod.fst := by
      exact List.mem_map.mpr ⟨(a, output), hmem, rfl⟩
    have hout : output = H a := hcons (a, output) hmem
    rw [TraceTable.replay_empty_apply H tr hcons a]
    simp [haddr, hout]
  · intro hvalue
    rw [TraceTable.replay_empty_apply H tr hcons a] at hvalue
    by_cases haddr : a ∈ tr.map Prod.fst
    · simp only [if_pos haddr] at hvalue
      have hout : H a = output := Option.some.inj hvalue
      rcases List.mem_map.mp haddr with ⟨q, hq, hqa⟩
      rcases q with ⟨b, v⟩
      simp only [Prod.fst] at hqa
      have hv : v = H b := hcons (b, v) hq
      have hvout : v = output := by rw [hv, hqa, hout]
      simpa [hqa, hvout] using hq
    · simp [haddr] at hvalue

theorem mem_eq_of_replay_eq (H : I → A) (tr₁ tr₂ : List (I × A))
    (hcons₁ : ∀ q ∈ tr₁, q.2 = H q.1)
    (hcons₂ : ∀ q ∈ tr₂, q.2 = H q.1)
    (heq : TraceTable.replay (emptyTable : Table I A) tr₁ =
      TraceTable.replay (emptyTable : Table I A) tr₂) :
    ∀ a output, (a, output) ∈ tr₁ ↔ (a, output) ∈ tr₂ := by
  intro a output
  rw [mem_iff_replay_some H tr₁ hcons₁ a output,
    mem_iff_replay_some H tr₂ hcons₂ a output]
  rw [congrFun (congrFun heq a)]

#print axioms mem_iff_replay_some
#print axioms mem_eq_of_replay_eq

end AspisR1.TraceTableMembership
