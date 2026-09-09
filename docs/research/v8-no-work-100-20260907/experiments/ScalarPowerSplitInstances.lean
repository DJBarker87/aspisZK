import ScalarPowerSplit

/-! Transport the symbolic split across arbitrary enumerations of the same
finite carriers. No concrete enumeration or field operation is evaluated. -/
set_option autoImplicit false
namespace AspisV8.ScalarPowerSplitInstances

theorem split {F : Type*} [CommSemiring F] (m n : ℕ)
    (whole : Fintype (Fin (m+n))) (left : Fintype (Fin m)) (right : Fintype (Fin n))
    (values : Fin (m+n) → F) (gamma : F) :
    (∑ lane∈@Finset.univ (Fin (m+n)) whole, gamma^lane.val*values lane)=
      (∑ lane∈@Finset.univ (Fin m) left, gamma^lane.val*values (Fin.castAdd n lane))+
        gamma^m*(∑ lane∈@Finset.univ (Fin n) right,
          gamma^lane.val*values (Fin.natAdd m lane)) := by
  have sameWhole : whole=Fin.fintype (m+n) := Subsingleton.elim _ _
  have sameLeft : left=Fin.fintype m := Subsingleton.elim _ _
  have sameRight : right=Fin.fintype n := Subsingleton.elim _ _
  cases sameWhole
  cases sameLeft
  cases sameRight
  exact ScalarPowerSplit.split m n values gamma

#print axioms split
end AspisV8.ScalarPowerSplitInstances
