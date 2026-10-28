import R1Z.PV_RunJoin_PremiseTruth24
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalMapBoundary24
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- No canonical instance can have the rejected input's reconstructed
witness. This obstruction precedes any public_eq question. -/
theorem bad_no_canonical_record :
    ¬ ∃ w : BuilderCanonical.Instance (K := K), w.val.2 =
      BuilderRecordCanonical.witness (PV_Src_Forest_PrimitiveArguments.wordWitness
        (PV_RunJoin_UniversalBuild22.records PV_RunJoin_AdmissionBoundary23.bad).w) := by
  rintro ⟨w,hw⟩
  have balance := w.property.1.2.2.1
  rw [hw] at balance
  change (0 : Nat) = 1 + 0 at balance
  omega
#print axioms bad_no_canonical_record

/-- Therefore the record-based canonical map on all raw Input does not
exist. Merely assigning raw type membership never supplies this function. -/
theorem no_raw_record_map :
    ¬ ∃ f : PV_Src_NativeInput.Input → BuilderCanonical.Instance (K := K),
      ∀ i, (f i).val.2 = BuilderRecordCanonical.witness
        (PV_Src_Forest_PrimitiveArguments.wordWitness
          (PV_RunJoin_UniversalBuild22.records i).w) := by
  rintro ⟨f,hf⟩
  exact bad_no_canonical_record ⟨f PV_RunJoin_AdmissionBoundary23.bad,
    hf PV_RunJoin_AdmissionBoundary23.bad⟩
#print axioms no_raw_record_map
end R1Z.PV_RunJoin_CanonicalMapBoundary24
