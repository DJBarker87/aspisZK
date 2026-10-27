import R1Z.PV_OptB_OffPole
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_AlignedSchedule
open R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
attribute [local instance] Classical.propDecidable

/-- Retry indices agree even for DIFFERENT raw tuples if the public verdicts
agree pointwise. Establishing those verdicts in the fixed native execution
is a source obligation, not a consequence of `same_public` alone. -/
theorem first_good_aligned {C D : Type} {N : Nat}
    (P : C → Prop) (Q : D → Prop) (c : Fin N → C) (d : Fin N → D)
    (aligned : ∀ k, P (c k) ↔ Q (d k)) : firstGood P c = firstGood Q d := by
  rcases hl : firstGood P c with _ | i <;> rcases hr : firstGood Q d with _ | j
  · rfl
  · exact absurd ((aligned j).2 (firstGood_spec Q d j hr)) (firstGood_none P c hl j)
  · exact absurd ((aligned i).1 (firstGood_spec P c i hl)) (firstGood_none Q d hr i)
  · have a := firstGood_least P c i hl j ((aligned j).2 (firstGood_spec Q d j hr))
    have b := firstGood_least Q d j hr i ((aligned i).1 (firstGood_spec P c i hl))
    rw [le_antisymm a b]

#print axioms first_good_aligned
theorem rejection_aligned {C D : Type} {N : Nat}
    (P : C → Prop) (Q : D → Prop) (c : Fin N → C) (d : Fin N → D)
    (aligned : ∀ k, P (c k) ↔ Q (d k)) (k : Fin N) : ¬ P (c k) ↔ ¬ Q (d k) :=
  not_congr (aligned k)

#print axioms rejection_aligned
theorem exhaustion_aligned {C D : Type} {N : Nat}
    (P : C → Prop) (Q : D → Prop) (c : Fin N → C) (d : Fin N → D)
    (aligned : ∀ k, P (c k) ↔ Q (d k)) : firstGood P c = none ↔ firstGood Q d = none := by
  rw [first_good_aligned P Q c d aligned]

#print axioms exhaustion_aligned
theorem reached_prefix_aligned {C D : Type} {N : Nat}
    (P : C → Prop) (Q : D → Prop) (c : Fin N → C) (d : Fin N → D)
    (aligned : ∀ k, P (c k) ↔ Q (d k)) (index : Fin N) :
    (∀ k : Fin N, k < index → ¬ P (c k)) ↔ (∀ k : Fin N, k < index → ¬ Q (d k)) := by
  constructor
  · intro left k before hq
    exact left k before ((aligned k).2 hq)
  · intro right k before hp
    exact right k before ((aligned k).1 hp)

#print axioms reached_prefix_aligned
theorem attempt_count_aligned {C D : Type} {N : Nat}
    (P : C → Prop) (Q : D → Prop) (c : Fin N → C) (d : Fin N → D)
    (aligned : ∀ k, P (c k) ↔ Q (d k)) :
    (firstGood P c).map (fun k => k.val+1) = (firstGood Q d).map (fun k => k.val+1) := by
  rw [first_good_aligned P Q c d aligned]

#print axioms attempt_count_aligned
end R1Z.PV_OptB_AlignedSchedule
