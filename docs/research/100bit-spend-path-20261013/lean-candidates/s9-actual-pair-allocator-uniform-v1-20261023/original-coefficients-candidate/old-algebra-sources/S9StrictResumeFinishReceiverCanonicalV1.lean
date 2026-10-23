import S9ResumeFinishExactPowersV1
import S9ResumeConstructorInputsCanonicalV1
import S9ConstructorNativeReceiverCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9StrictResumeFinishReceiverCanonicalV1
open AspisR1S9ResumeFinishNativePairBindingV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev NA := Array NW 4#usize

/-- SAME strict checkpoint resume/finish execution supplies concrete receiver
factors/points/extras, exact actual powers arrays and the same helper call.
Input canonicality and child-success/receiver contracts are all derived.
Other finish slots, raw/decoder/callback/Box runtime and release remain open. -/
theorem strict_resume_finish_same_canonical_receiver_exact_powers_helper {D H : Type}
    (readerOps : AspisR1Stage2.ResumeOps)
    (digest : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (hash : H)
    (p : AspisR1Stage2.verifier.Prepared) (acc : AspisR1Stage2.verifier.Accumulator)
    (ops : AspisR1FinishRelationCurrent.FinishOps Weights D)
    (v : AspisR1FinishRelationCurrent.verifier.View)
    (a : AspisR1FinishRelationCurrent.verifier.Accumulator)
    (obs : Option (AspisR1FinishRelationCurrent.verifier.Phase → Result Unit))
    (hresume : AspisR1Stage2.verifier.resumeWithOps
      (AspisR1S9ResumeConstructorInputsCanonicalV1.withConstructorReaders readerOps)
      digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash = .ok (.Ok (p,acc)))
    (hfinish : AspisR1FinishRelationCurrent.verifier.finish_relation
      (AspisR1S9FinishActualConstructorSlotV1.installActualConstructor ops)
      v (stagePrepared p) a obs = .ok (.Ok ())) :
    ∃ (self : Weights) (selected : Slice FW) (nativeOut a0 a1 : NW) (ap0 ap1 libra : NA),
      AspisR1S9FinishActualConstructorSlotV1.actualNewWeightsSlot
        (stagePrepared p).variant (stagePrepared p).semantic_alpha (stagePrepared p).z = .ok (.Ok self) ∧
      self.variant = AspisR1S9ProductionPairCutV1.transport.Variant.S2 ∧
      AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical self ∧
      AspisR1S9ConstructorNativeReceiverCanonicalV1.PointsCanonical self ∧
      AspisR1S9ConstructorNativeReceiverCanonicalV1.ExtraCanonical self ∧
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
  let baseReaders := AspisR1S9ResumeSemanticAlphaCanonicalV1.withSemanticAlpha
    (AspisR1S9ResumeCircleReadsCanonicalV1.withReaderK readerOps)
  have hresumeE : AspisR1Stage2.verifier.resumeWithOps
      (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE baseReaders)
      digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash = .ok (.Ok (p,acc)) := hresume
  obtain ⟨self,selected,nativeOut,a0,a1,ap0,ap1,libra,hnew,hself,hselected,hpair,
      hr0,hp0,hr1,hp1,hc0,hc1,hs0,hs1,hhelper⟩ :=
    AspisR1S9ResumeFinishExactPowersV1.resume_finish_concrete_success_same_exact_powers_helper
      baseReaders digest bytes proof publicInput hash p acc ops v a obs hresumeE hfinish
  obtain ⟨halpha,hz⟩ :=
    AspisR1S9ResumeConstructorInputsCanonicalV1.resume_success_constructor_inputs_canonical
      readerOps digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash p acc hresume
  obtain ⟨hf,hp,he⟩ :=
    AspisR1S9ConstructorNativeReceiverCanonicalV1.actual_constructor_slot_success_receiver_canonical
      (stagePrepared p).variant (stagePrepared p).semantic_alpha (stagePrepared p).z self halpha hz hnew
  exact ⟨self,selected,nativeOut,a0,a1,ap0,ap1,libra,hnew,hself,hf,hp,he,hselected,hpair,
    hr0,hp0,hr1,hp1,hc0,hc1,hs0,hs1,hhelper⟩

#print axioms strict_resume_finish_same_canonical_receiver_exact_powers_helper
end AspisR1S9StrictResumeFinishReceiverCanonicalV1
