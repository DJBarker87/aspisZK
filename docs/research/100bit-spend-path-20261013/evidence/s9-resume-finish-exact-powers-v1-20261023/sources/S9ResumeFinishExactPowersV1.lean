import S9ResumeFinishConcreteProducersV1
import S9ActualIndexedPowersSemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ResumeFinishExactPowersV1
open AspisR1S9ResumeFinishNativePairBindingV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev NA := Array NW 4#usize

/-- Same concrete accepted finish producer path, now with exact decoded
powers for both native arrays, rather than canonicality treated as algebra.
All child executions and input canonicality are derived from the same source
resume/constructor/Pair path. Other finish slots/runtime remain explicit. -/
theorem resume_finish_concrete_success_same_exact_powers_helper {D H : Type}
    (readerOps : AspisR1Stage2.ResumeOps)
    (digest : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (hash : H)
    (p : AspisR1Stage2.verifier.Prepared) (acc : AspisR1Stage2.verifier.Accumulator)
    (ops : AspisR1FinishRelationCurrent.FinishOps Weights D)
    (v : AspisR1FinishRelationCurrent.verifier.View)
    (a : AspisR1FinishRelationCurrent.verifier.Accumulator)
    (obs : Option (AspisR1FinishRelationCurrent.verifier.Phase → Result Unit))
    (hresume : AspisR1Stage2.verifier.resumeWithOps
      (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE readerOps)
      digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash = .ok (.Ok (p,acc)))
    (hfinish : AspisR1FinishRelationCurrent.verifier.finish_relation
      (AspisR1S9FinishActualConstructorSlotV1.installActualConstructor ops)
      v (stagePrepared p) a obs = .ok (.Ok ())) :
    ∃ (self : Weights) (selected : Slice FW) (nativeOut a0 a1 : NW) (ap0 ap1 libra : NA),
      AspisR1S9FinishActualConstructorSlotV1.actualNewWeightsSlot
        (stagePrepared p).variant (stagePrepared p).semantic_alpha (stagePrepared p).z = .ok (.Ok self) ∧
      self.variant = AspisR1S9ProductionPairCutV1.transport.Variant.S2 ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice FW))
        (stagePrepared p).alpha { «end» := 2#usize } = .ok selected ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.pair self
        (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message
        (AspisR1S9FinishActualPairSlotV1.toNative (stagePrepared p).kappa) = .ok (.Ok nativeOut) ∧
      Slice.index_usize (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) 0#usize = .ok a0 ∧
      AspisR1S9ProductionPairCutV1.weights.powers 4#usize a0 = .ok ap0 ∧
      Slice.index_usize (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) 1#usize = .ok a1 ∧
      AspisR1S9ProductionPairCutV1.weights.powers 4#usize a1 = .ok ap1 ∧
      AspisR1S9ActualPairReachedPowersCanonicalV1.ArrayCanonical ap0 ∧
      AspisR1S9ActualPairReachedPowersCanonicalV1.ArrayCanonical ap1 ∧
      AspisR1S9ActualIndexedPowersSemanticsV1.Output a0 ap0 ∧
      AspisR1S9ActualIndexedPowersSemanticsV1.Output a1 ap1 ∧
      AspisR1S9ProductionPairCutV1.weights.factored_s2_libra_weights
        ap0 ap1 self.extra = .ok libra := by
  obtain ⟨self,selected,nativeOut,a0,a1,ap0,ap1,libra,hnew,hself,hselected,hpair,
      hr0,hp0,hr1,hp1,hc0,hc1,hhelper⟩ :=
    AspisR1S9ResumeFinishConcreteProducersV1.resume_finish_concrete_success_same_powers_helper
      readerOps digest bytes proof publicInput hash p acc ops v a obs hresume hfinish
  have hstage := AspisR1S9ResumeAlphaPairInputV1.resume_finish_prefix_native_alpha_canonical
    readerOps digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash p acc
    (Array.to_slice p.alpha) hresume
    (AspisR1S9ArrayTwoPrefixSourceV1.array_two_prefix_exact p.alpha)
  have hcanonical : ∀ (i : Usize) (value : NW), Slice.index_usize
      (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) i = .ok value →
      AspisR1S9ActualPairWideCanonicalV1.Canonical value := by
    intro i value hread
    apply hstage i value
    rw [← same_native_alpha_prefix p selected hselected]
    exact hread
  have hs0 := AspisR1S9ActualIndexedPowersSemanticsV1.actual_powers_four_success_decodes_powers
    a0 ap0 (hcanonical 0#usize a0 hr0) hp0
  have hs1 := AspisR1S9ActualIndexedPowersSemanticsV1.actual_powers_four_success_decodes_powers
    a1 ap1 (hcanonical 1#usize a1 hr1) hp1
  exact ⟨self,selected,nativeOut,a0,a1,ap0,ap1,libra,hnew,hself,hselected,hpair,
    hr0,hp0,hr1,hp1,hc0,hc1,hs0,hs1,hhelper⟩

#print axioms resume_finish_concrete_success_same_exact_powers_helper
end AspisR1S9ResumeFinishExactPowersV1
