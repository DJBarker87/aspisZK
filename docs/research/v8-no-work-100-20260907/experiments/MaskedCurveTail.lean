import AspisFormal.V5FriDegreeThreeCorrelatedAgreement

/-! A fixed own-support family covers every selected high-agreement response
outside an explicit curve-decoding exception. The strategy is masked on the
actual nonrepresentation event; existence of some unrelated predecessor is
not substituted for representation of that strategy's selected candidate.
No same-support recovery is required at every challenge, and no query union
over the family is taken. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000

namespace AspisV8.MaskedCurveTail
open Finset
open AspisV5FriDegreeThreeCorrelatedAgreement
variable {K Domain Message : Type*}
  [Field K] [Fintype K] [DecidableEq K]
  [Fintype Domain] [DecidableEq Domain]

/-- The family is defined only from the fixed received lanes. The selected
candidate may depend on z; its representation is a separate condition. -/
def CoveredAt (encoder : Message → Domain → K) (lanes : Fin 4 → Domain → K)
    (a : Nat) (strategy : ProximateStrategy K Domain Message) (z : K) : Prop :=
  ∃ components : Fin 4 → Message,
    a ≤ (jointAgreementSet encoder lanes components).card ∧
    CandidateOnCurve encoder strategy components z

noncomputable def maskedStrategy (encoder : Message → Domain → K)
    (lanes : Fin 4 → Domain → K) (a : Nat)
    (strategy : ProximateStrategy K Domain Message) :
    ProximateStrategy K Domain Message := by
  classical
  exact ⟨strategy.candidate, fun z =>
    if CoveredAt encoder lanes a strategy z then ∅ else strategy.support z⟩

noncomputable def tailSet (encoder : Message → Domain → K)
    (lanes : Fin 4 → Domain → K) (a t : Nat)
    (strategy : ProximateStrategy K Domain Message) : Finset K := by
  classical
  exact (goodChallenges encoder (t-1) lanes strategy).filter
    fun z => ¬ CoveredAt encoder lanes a strategy z

theorem masked_valid_iff (encoder : Message → Domain → K)
    (lanes : Fin 4 → Domain → K) (a threshold : Nat)
    (strategy : ProximateStrategy K Domain Message) (z : K) :
    ValidResponse encoder threshold lanes (maskedStrategy encoder lanes a strategy) z ↔
      ValidResponse encoder threshold lanes strategy z ∧
      ¬ CoveredAt encoder lanes a strategy z := by
  classical
  by_cases covered : CoveredAt encoder lanes a strategy z
  · have empty : (maskedStrategy encoder lanes a strategy).support z=∅ := by
      simp only [maskedStrategy,if_pos covered]
    constructor
    · intro valid
      have impossible : threshold<0 := by
        simpa only [empty,Finset.card_empty] using valid.1
      exact False.elim ((Nat.not_lt_zero _) impossible)
    · exact fun h => False.elim (h.2 covered)
  · have support : (maskedStrategy encoder lanes a strategy).support z=strategy.support z := by
      simp only [maskedStrategy,if_neg covered]
    constructor
    · intro valid
      refine ⟨⟨?_,?_⟩,covered⟩
      · simpa only [support] using valid.1
      · intro x hx
        have original := valid.2 x (by simpa only [support] using hx)
        exact original
    · rintro ⟨valid,_⟩
      refine ⟨?_,?_⟩
      · simpa only [support] using valid.1
      · intro x hx
        exact valid.2 x (by simpa only [support] using hx)

theorem tailSet_eq_masked_good (encoder : Message → Domain → K)
    (lanes : Fin 4 → Domain → K) (a t : Nat)
    (strategy : ProximateStrategy K Domain Message) :
    tailSet encoder lanes a t strategy=
      goodChallenges encoder (t-1) lanes (maskedStrategy encoder lanes a strategy) := by
  classical
  ext z
  simp only [tailSet,Finset.mem_filter,mem_goodChallenges_iff,masked_valid_iff]

/-- The actual selected unrepresented candidates have a curve-decoding tail
bound. The recovered tuple is proved to be in the prechallenge own-support
family using one resolving selected node; no family-membership premise occurs. -/
theorem tail_card_le (encoder : Message → Domain → K)
    (lanes : Fin 4 → Domain → K) (a t C : Nat)
    (positive : 0<t) (floor_le : a≤t)
    (curve : DegreeThreeCurveDecodable encoder (t-1) C)
    (strategy : ProximateStrategy K Domain Message) :
    (tailSet encoder lanes a t strategy).card≤C := by
  classical
  rw [tailSet_eq_masked_good]
  by_contra excessive
  have many : C<(goodChallenges encoder (t-1) lanes
      (maskedStrategy encoder lanes a strategy)).card := Nat.lt_of_not_ge excessive
  obtain ⟨components,selected,subset,large,onCurve⟩ :=
    curve lanes (maskedStrategy encoder lanes a strategy) many
  obtain ⟨z,member,resolves⟩ :=
    exists_selected_not_resolving encoder lanes components selected large
  have valid := (mem_goodChallenges_iff encoder (t-1) lanes
    (maskedStrategy encoder lanes a strategy) z).mp (subset member)
  have original := (masked_valid_iff encoder lanes a (t-1) strategy z).mp valid
  have supportIncluded := support_subset_jointAgreement encoder (t-1) lanes
    (maskedStrategy encoder lanes a strategy) components z valid (onCurve z member) resolves
  have supportCard := Finset.card_le_card supportIncluded
  have own : a≤(jointAgreementSet encoder lanes components).card := by
    have threshold := valid.1
    omega
  have selectedOn : CandidateOnCurve encoder strategy components z := by
    exact onCurve z member
  exact original.2 ⟨components,own,selectedOn⟩

end AspisV8.MaskedCurveTail

#print axioms AspisV8.MaskedCurveTail.masked_valid_iff
#print axioms AspisV8.MaskedCurveTail.tailSet_eq_masked_good
#print axioms AspisV8.MaskedCurveTail.tail_card_le
