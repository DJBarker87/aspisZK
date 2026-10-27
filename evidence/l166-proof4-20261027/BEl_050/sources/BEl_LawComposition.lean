import BEh_Scope
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_LawComposition

/-- Success-conditioned carrier association composes without identifying
rejected error kinds or rejected mutable states. Ordered attempted histories
remain associated even when every intermediate observation rejects. -/
theorem trans {S A E F G : Type}
    (left : BEh_Scope.Outcome S A E) (middle : BEh_Scope.Outcome S A F)
    (right : BEh_Scope.Outcome S A G)
    (first : BEh_Scope.Law left middle) (second : BEh_Scope.Law middle right) :
    BEh_Scope.Law left right := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro a
    exact (first.1.1 a).trans (second.1.1 a)
  · intro a accepted
    exact (first.1.2 a accepted).trans (second.1.2 a ((first.1.1 a).mp accepted))
  · exact first.2.1.trans second.2.1
  · intro rejected
    exact (first.2.2 rejected).trans (second.2.2 (first.2.1.mp rejected))

#print axioms trans
end AspisR1.BEl_LawComposition
end
