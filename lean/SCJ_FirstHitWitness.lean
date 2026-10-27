import SCJ_TableExtension
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_FirstHitWitness
open FS FS2.Duplex AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]
/-- Converse to FS.hitsBad_of_first, retaining the actual FIRST read and
its preceding table. A pair of arbitrary occurrences is not a witness. -/
theorem witness (bad : I → Table I A → A → Prop) (H : I → A)
    (tr : List (I × A)) (t : Table I A)
    (consistent : ∀ q ∈ tr, q.2 = H q.1)
    (hit : hitsBad bad t tr) :
    ∃ a, Read tr a ∧ t a = none ∧ bad a (tableBefore t tr a) (H a) := by
  induction tr generalizing t with
  | nil => exact False.elim hit
  | cons q rest ih =>
    obtain ⟨i,answer⟩ := q
    rcases hit with head | tail
    · refine ⟨i,?_,head.1,?_⟩
      · exact List.mem_cons_self
      · simp only [tableBefore,ite_true]
        rw [← consistent (i,answer) List.mem_cons_self]
        exact head.2
    · obtain ⟨a,read,fresh,badAt⟩ := ih (put t i answer)
        (fun q h => consistent q (List.mem_cons_of_mem _ h)) tail
      have different : a ≠ i := by
        intro same
        subst a
        simp only [put,ite_true] at fresh
        cases fresh
      refine ⟨a,List.mem_cons_of_mem _ read,?_,?_⟩
      · simpa only [put,if_neg different] using fresh
      · simpa only [tableBefore,if_neg (Ne.symm different)] using badAt

#print axioms witness
end AspisR1.SCJ_FirstHitWitness
end
