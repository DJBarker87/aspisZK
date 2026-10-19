import R1ComputableTraceWitness
import R1TraceValueDecode
import R1ConcreteSpendExtraction

/-! Executable reconstruction and checking of a spend witness from one trace.
This is not the full-log extractor: commitment recovery and complete efficient
list decoding must still supply the candidate trace. Returned witnesses are
always checked; completeness here assumes the stated production facts. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisR1.TraceWitnessExtract

open R0P SpendRelation AspisWideTower AspisV8R15.ExactTowerBase
abbrev E := WideExact
abbrev embed := ExactBaseProjection.embed

def extract (pub : Public M31Exact) (A : Trace E) : Option Wspend :=
  match TraceValueDecode.decode A with
  | none => none
  | some values =>
      let w := ComputableTraceWitness.fromTrace A values.1 values.2.1 values.2.2
      if checkM31 pub w = true then some w else none

theorem returned_checked (pub : Public M31Exact) (A : Trace E) (w : Wspend)
    (h : extract pub A = some w) : checkM31 pub w = true := by
  cases hd : TraceValueDecode.decode A with
  | none => simp [extract, hd] at h
  | some values =>
      simp only [extract, hd] at h
      split at h
      next hc =>
        have hw := Option.some.inj h
        exact hw ▸ hc
      next hc => contradiction

theorem returned_valid (pub : Public M31Exact) (A : Trace E) (w : Wspend)
    (h : extract pub A = some w) : Rspend pub w :=
  (check_eq_true_iff pub w).mp (returned_checked pub A w h)

attribute [local irreducible] poseidonPermutation nodeCompress merkleRoot
attribute [local irreducible] ConcreteBinding.candidates

theorem complete_of_production (pub : Public M31Exact) (A : Trace E) (lam chi : E)
    (hshape : PublicOptionShape.canonical pub)
    (hbase : BaseTyped embed.fieldRange A)
    (h : ProductionHolds (SpendDataMap.mapPublic embed pub) lam chi A ∧
      CopyLinkBalance (SpendDataMap.mapPublic embed pub) A) :
    ∃ w : Wspend, extract pub A = some w ∧ Rspend pub w := by
  letI : CharP E P :=
    charP_of_injective_algebraMap (algebraMap M31Exact E).injective P
  let widePub := SpendDataMap.mapPublic embed pub
  have hwideShape : PublicOptionShape.canonical widePub :=
    (SpendRelationMap.canonical_map_iff embed embed.injective pub).mpr hshape
  obtain ⟨v0, v1, v2, h0, h1, h2, hbalance, e0, e1, e2, hinput⟩ :=
    InputWitness.bounded_of_production P (by norm_num [P]) widePub A lam chi h
  have hfacts := SpendSemantics.of_production P (by norm_num [P]) widePub A lam chi h
  let ww := TraceSpendWitness.fromTrace A ⟨v0, h0⟩ ⟨v1, h1⟩ ⟨v2, h2⟩
  have hw : Rspend widePub ww := by
    refine ⟨hwideShape, hinput, hbalance, ?_, ?_⟩
    · simpa only [changeCommitment, ww, TraceSpendWitness.fromTrace, e2] using hfacts.change
    · cases hv : widePub.variant with
      | privateTransfer =>
          obtain ⟨recipient, hr, _⟩ :=
            PublicOptionShape.private_transfer_shape widePub hv hwideShape
          rw [variantOutput, hv, hr]
          apply congrArg some
          simpa only [recipientCommitment, ww, TraceSpendWitness.fromTrace, e1] using
            hfacts.recipient hv recipient hr
      | withdrawal =>
          obtain ⟨amount, _, ha, _⟩ :=
            PublicOptionShape.withdrawal_shape widePub hv hwideShape
          rw [variantOutput, hv, ha]
          apply congrArg some
          exact (hfacts.withdrawal hv amount ha).symm.trans e1
  let w := ComputableTraceWitness.fromTrace A ⟨v0, h0⟩ ⟨v1, h1⟩ ⟨v2, h2⟩
  have hwvalid : Rspend pub w := by
    rw [show w = SpendBaseDescent.projectWitness ww from
      ComputableTraceWitness.fromTrace_eq_projected_existing A _ _ _ hbase]
    exact SpendBaseDescent.rspend_project pub ww
      (TraceSpendWitness.base_coordinates A _ _ _ hbase) hw
  have hcheck : checkM31 pub w = true := (check_eq_true_iff pub w).mpr hwvalid
  have hdecode := TraceValueDecode.decode_of_values A
    (⟨v0, h0⟩ : Fin (2^30)) ⟨v1, h1⟩ ⟨v2, h2⟩ e0 e1 e2
  refine ⟨w, ?_, hwvalid⟩
  simpa only [extract, hdecode, if_pos hcheck]

theorem complete_of_candidate
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
    ∃ w : Wspend, extract pub (SemSource.rowsOf rowEquiv t) = some w ∧ Rspend pub w :=
  complete_of_production pub (SemSource.rowsOf rowEquiv t) lam chi hshape
    (CandidateBaseProjection.rows_base_typed eK c1Packed c2Packed t ht) h

#print axioms returned_checked
#print axioms returned_valid
#print axioms complete_of_production
#print axioms complete_of_candidate
end AspisR1.TraceWitnessExtract
