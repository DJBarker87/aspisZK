import R1TraceSpendWitness
import R1CandidateBaseProjection
import R1SpendRelationExtraction

/-! Production facts on a base-typed wide trace imply an actual M31 spend
witness. Candidate typing is discharged using the existing subfield descent.
This is an existential algebraic theorem, not an efficient list decoder or
an acceptance-to-production/source-refinement theorem. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisR1.ConcreteSpendExtraction

open R0P SpendRelation AspisWideTower AspisV8R15.ExactTowerBase
abbrev E := WideExact
abbrev embed := ExactBaseProjection.embed

attribute [local irreducible] poseidonPermutation nodeCompress merkleRoot
attribute [local irreducible] ConcreteBinding.candidates

theorem of_production (pub : Public M31Exact) (A : Trace E) (lam chi : E)
    (hshape : PublicOptionShape.canonical pub)
    (hbase : BaseTyped embed.fieldRange A)
    (h : ProductionHolds (SpendDataMap.mapPublic embed pub) lam chi A ∧
      CopyLinkBalance (SpendDataMap.mapPublic embed pub) A) :
    ∃ w : Wspend, Rspend pub w := by
  letI : CharP E P :=
    charP_of_injective_algebraMap (algebraMap M31Exact E).injective P
  let widePub := SpendDataMap.mapPublic embed pub
  have hwideShape : PublicOptionShape.canonical widePub :=
    (SpendRelationMap.canonical_map_iff embed embed.injective pub).mpr hshape
  obtain ⟨v0, v1, v2, h0, h1, h2, hbalance, e0, e1, e2, hinput⟩ :=
    InputWitness.bounded_of_production P (by norm_num [P]) widePub A lam chi h
  have hfacts := SpendSemantics.of_production P (by norm_num [P]) widePub A lam chi h
  let w := TraceSpendWitness.fromTrace A ⟨v0, h0⟩ ⟨v1, h1⟩ ⟨v2, h2⟩
  have hw : Rspend widePub w := by
    refine ⟨hwideShape, hinput, hbalance, ?_, ?_⟩
    · simpa only [changeCommitment, w, TraceSpendWitness.fromTrace, e2] using hfacts.change
    · cases hv : widePub.variant with
      | privateTransfer =>
          obtain ⟨recipient, hr, _⟩ :=
            PublicOptionShape.private_transfer_shape widePub hv hwideShape
          rw [variantOutput, hv, hr]
          apply congrArg some
          simpa only [recipientCommitment, w, TraceSpendWitness.fromTrace, e1] using
            hfacts.recipient hv recipient hr
      | withdrawal =>
          obtain ⟨amount, _, ha, _⟩ :=
            PublicOptionShape.withdrawal_shape widePub hv hwideShape
          rw [variantOutput, hv, ha]
          apply congrArg some
          exact (hfacts.withdrawal hv amount ha).symm.trans e1
  exact ⟨SpendBaseDescent.projectWitness w,
    SpendBaseDescent.rspend_project pub w
      (TraceSpendWitness.base_coordinates A ⟨v0, h0⟩ ⟨v1, h1⟩ ⟨v2, h2⟩ hbase) hw⟩

theorem candidate_checked_witness
    (pub : Public M31Exact) (hshape : PublicOptionShape.canonical pub)
    (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List ExactLeafFieldCodec.Byte))
    (t : ConcreteBinding.Tuple E)
    (ht : t ∈ ConcreteBinding.candidates
      (TypedRecoveredWords.word embed eK c1Packed c2Packed))
    (lam chi : E)
    (h : ProductionHolds (SpendDataMap.mapPublic embed pub) lam chi
        (SemSource.rowsOf rowEquiv t) ∧
      CopyLinkBalance (SpendDataMap.mapPublic embed pub) (SemSource.rowsOf rowEquiv t)) :
    ∃ w : Wspend, checkM31 pub w = true := by
  obtain ⟨w, hw⟩ := of_production pub (SemSource.rowsOf rowEquiv t) lam chi hshape
    (CandidateBaseProjection.rows_base_typed eK c1Packed c2Packed t ht) h
  exact ⟨w, (check_eq_true_iff pub w).mpr hw⟩

#print axioms of_production
#print axioms candidate_checked_witness
end AspisR1.ConcreteSpendExtraction
