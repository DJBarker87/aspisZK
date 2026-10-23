import S9ResumeAlphaPairInputV1
import S9ActualPairReachedPowersCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ResumeActualPairCanonicalPowersV1
open AspisR1S9ResumeAlphaPairInputV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev PW := AspisR1S9ProductionPairCutV1.weights.Weights
abbrev NA := Array NW 4#usize

/-- The canonical-alpha premise of the accepted actual Pair producer theorem
is discharged by the exact successful strict resume and finish prefix source
operation. The actual Pair call explicitly consumes that same transported
slice. Enclosing whole-caller installation and source/runtime correspondence
are not assumed to follow from this local accepted-run composition. -/
theorem resume_same_pair_success_canonical_powers_helper
    (ops : AspisR1Stage2.ResumeOps) {H : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (variant : AspisR1Stage2.transport.Variant) (hash : H)
    (p : AspisR1Stage2.verifier.Prepared) (acc : AspisR1Stage2.verifier.Accumulator)
    (selected : Slice SW) (self : PW) (message : Slice U8) (kappa out : NW)
    (hresume : AspisR1Stage2.verifier.resumeWithOps
      (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops)
      D bytes proof publicInput variant hash = .ok (.Ok (p,acc)))
    (hselected : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice SW))
      p.alpha { «end» := 2#usize } = .ok selected)
    (hs2 : self.variant = AspisR1S9ProductionPairCutV1.transport.Variant.S2)
    (hpair : AspisR1S9ProductionPairCutV1.weights.Weights.pair self
      (toNativeSlice selected) message kappa = .ok (.Ok out)) :
    ∃ (a0 a1 : NW) (ap0 ap1 libra : NA),
      Slice.index_usize (toNativeSlice selected) 0#usize = .ok a0 ∧
      AspisR1S9ProductionPairCutV1.weights.powers 4#usize a0 = .ok ap0 ∧
      Slice.index_usize (toNativeSlice selected) 1#usize = .ok a1 ∧
      AspisR1S9ProductionPairCutV1.weights.powers 4#usize a1 = .ok ap1 ∧
      AspisR1S9ActualPairReachedPowersCanonicalV1.ArrayCanonical ap0 ∧
      AspisR1S9ActualPairReachedPowersCanonicalV1.ArrayCanonical ap1 ∧
      AspisR1S9ProductionPairCutV1.weights.factored_s2_libra_weights
        ap0 ap1 self.extra = .ok libra := by
  have hfold : Slice.len (toNativeSlice selected) = 2#usize := by
    apply UScalar.eq_of_val_eq
    have he := AspisR1S9ArrayTwoPrefixSourceV1.successful_array_two_prefix_eq
      p.alpha selected hselected
    rw [he]
    simpa [Slice.len,toNativeSlice,Array.to_slice] using p.alpha.property
  exact AspisR1S9ActualPairReachedPowersCanonicalV1.actual_pair_success_reaches_canonical_powers_helper
    self (toNativeSlice selected) message kappa out hs2 hfold
    (resume_finish_prefix_native_alpha_canonical ops D bytes proof publicInput variant hash
      p acc selected hresume hselected) hpair

#print axioms resume_same_pair_success_canonical_powers_helper
end AspisR1S9ResumeActualPairCanonicalPowersV1
