from step import check,append
m='R1Z/PV_OptB_AlignedSchedule';ns='R1Z.PV_OptB_AlignedSchedule'
check(m)
append(m,ns,'rejection_aligned','''theorem rejection_aligned {C D : Type} {N : Nat}
    (P : C → Prop) (Q : D → Prop) (c : Fin N → C) (d : Fin N → D)
    (aligned : ∀ k, P (c k) ↔ Q (d k)) (k : Fin N) : ¬ P (c k) ↔ ¬ Q (d k) :=
  not_congr (aligned k)
''')
append(m,ns,'exhaustion_aligned','''theorem exhaustion_aligned {C D : Type} {N : Nat}
    (P : C → Prop) (Q : D → Prop) (c : Fin N → C) (d : Fin N → D)
    (aligned : ∀ k, P (c k) ↔ Q (d k)) : firstGood P c = none ↔ firstGood Q d = none := by
  rw [first_good_aligned P Q c d aligned]
''')
append(m,ns,'reached_prefix_aligned','''theorem reached_prefix_aligned {C D : Type} {N : Nat}
    (P : C → Prop) (Q : D → Prop) (c : Fin N → C) (d : Fin N → D)
    (aligned : ∀ k, P (c k) ↔ Q (d k)) (index : Fin N) :
    (∀ k : Fin N, k < index → ¬ P (c k)) ↔ (∀ k : Fin N, k < index → ¬ Q (d k)) := by
  constructor
  · intro left k before hq
    exact left k before ((aligned k).2 hq)
  · intro right k before hp
    exact right k before ((aligned k).1 hp)
''')
append(m,ns,'attempt_count_aligned','''theorem attempt_count_aligned {C D : Type} {N : Nat}
    (P : C → Prop) (Q : D → Prop) (c : Fin N → C) (d : Fin N → D)
    (aligned : ∀ k, P (c k) ↔ Q (d k)) :
    (firstGood P c).map (fun k => k.val+1) = (firstGood Q d).map (fun k => k.val+1) := by
  rw [first_good_aligned P Q c d aligned]
''')
