import R1Z.BuilderRecordCanonical

/-! Field interpretation, rather than raw-byte equality, is the source
handoff needed by HonestProver.build. No canonical key/owner/salt-word bound
is assumed. This also covers admitted noncanonical output-owner words. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderFieldNormalization
open R0P R0Z.WriterRefine R0Z.BuilderModel R1J.SpendWitnessMap
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem decoded_witness (w : RustWitness) :
    BuilderSpendRelation.modelWitness
      (BuilderCanonical.liftWitness (K := K) (BuilderRecordCanonical.witness w)) =
      toModel (K := K) w := by
  rw [BuilderCanonical.modelWitness_lift, BuilderRecordCanonical.witness_model]
  simp only [mapW, toModel, digK, liftU, map_natCast]
  rfl

/-- Arbitrary raw key, salt, owner and pair words give the same K-valued
trace as their canonical M31 decoding. Only the existing WitnessOk shape
and public correspondence of the raw mapper are required. -/
theorem trace_normalization
    (w : RustWitness) (p : RustPublic) (pub : Public F)
    (hw : WitnessOk w) (hp : PubCorr p (mapPub (K := K) pub)) :
    BuilderRefinement.mergedTrace (K := K) w p =
      BuilderRefinement.mergedTrace
        (BuilderCanonical.rustWitness (BuilderRecordCanonical.witness w))
        (BuilderCanonical.rustPublic pub) := by
  rw [BuilderRefinement.mergedTrace_eq_model w p (mapPub pub) hp hw,
    BuilderCanonical.canonical_trace, decoded_witness]

#print axioms decoded_witness
#print axioms trace_normalization
end R1Z.BuilderFieldNormalization
