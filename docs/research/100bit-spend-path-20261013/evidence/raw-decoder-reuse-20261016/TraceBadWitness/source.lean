import FS2.DuplexTrace

/-! Converse of the existing `FS.hitsBad_of_first`: a bad event in a
consistent trace has a witness at an address's actual first-read table.
No finiteness of the address type is required. -/
set_option autoImplicit false
namespace AspisR1.TraceBadWitness

open FS FS2 FS2.Duplex AspisV8PairedCommitment

variable {I A : Type} [DecidableEq I]

theorem of_hitsBad (bad : I → Table I A → A → Prop) (H : I → A)
    (tr : List (I × A)) (t : Table I A)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hbad : hitsBad bad t tr) :
    ∃ a, Read tr a ∧ t a = none ∧ bad a (tableBefore t tr a) (H a) := by
  induction tr generalizing t with
  | nil => cases hbad
  | cons q rest ih =>
      obtain ⟨i,v⟩ := q
      have hv : v = H i := hcons (i,v) (List.mem_cons_self ..)
      have hc : ∀ q ∈ rest, q.2 = H q.1 :=
        fun q hq => hcons q (List.mem_cons_of_mem _ hq)
      rcases hbad with ⟨hmiss,hb⟩ | hr
      · refine ⟨i, by simp [Read], hmiss, ?_⟩
        simpa [tableBefore, hv] using hb
      · obtain ⟨a, ha, hmiss, hb⟩ := ih (put t i v) hc hr
        have hai : a ≠ i := by
          intro he
          subst a
          simp [put] at hmiss
        refine ⟨a, by simpa only [Read, List.map_cons, List.mem_cons] using Or.inr ha,
          by simpa [put, hai] using hmiss, ?_⟩
        simpa [tableBefore, Ne.symm hai] using hb

theorem not_hitsBad (bad : I → Table I A → A → Prop) (H : I → A)
    (tr : List (I × A)) (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hout : ∀ a, Read tr a → ¬ bad a (tableBefore emptyTable tr a) (H a)) :
    ¬ hitsBad bad emptyTable tr := by
  intro hbad
  obtain ⟨a, ha, _, hb⟩ := of_hitsBad bad H tr emptyTable hcons hbad
  exact hout a ha hb

#print axioms of_hitsBad
#print axioms not_hitsBad
end AspisR1.TraceBadWitness
