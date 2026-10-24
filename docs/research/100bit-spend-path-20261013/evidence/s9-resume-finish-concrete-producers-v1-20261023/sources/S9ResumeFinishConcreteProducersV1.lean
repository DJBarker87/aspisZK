import S9ResumeFinishNativePairBindingV1
import S9FinishActualConstructorSlotV1
import S9ActualPairReachedPowersCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ResumeFinishConcreteProducersV1
open AspisR1S9ResumeFinishNativePairBindingV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev NA := Array NW 4#usize

/-- Strict resume and accepted finish with BOTH concrete constructor and Pair
slots supply the same S2 receiver, exact native alpha/powers calls and the
same factored helper. No independent receiver-variant, native Pair/powers/
helper success, alpha canonicality or twofold-length contract is assumed.
The other finish slots and whole source/Box/runtime installation stay open. -/
theorem resume_finish_concrete_success_same_powers_helper {D H : Type}
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
      AspisR1S9ProductionPairCutV1.weights.factored_s2_libra_weights
        ap0 ap1 self.extra = .ok libra := by
  let installed := {ops with newWeights := AspisR1S9FinishActualConstructorSlotV1.actualNewWeightsSlot}
  obtain ⟨self,selected,nativeOut,hnew,hselected,hpair,hcanonical⟩ :=
    resume_finish_success_reaches_canonical_actual_pair readerOps digest bytes proof publicInput
      hash p acc installed v a obs hresume hfinish
  obtain ⟨fields⟩ := AspisR1.OraclePortCkptAbiSourceFields.successful_fields
    (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE readerOps)
    digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash p acc hresume
  have hv : (stagePrepared p).variant = AspisR1FinishRelationCurrent.transport.Variant.S2 := by
    change stageVariant p.variant = _
    rw [fields.variant]
    rfl
  have hself := AspisR1S9FinishActualConstructorSlotV1.actualNewWeightsSlot_success_variant
    (stagePrepared p).variant (stagePrepared p).semantic_alpha (stagePrepared p).z self hnew
  rw [hv] at hself
  have hfold : Slice.len (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) = 2#usize := by
    apply UScalar.eq_of_val_eq
    have he := AspisR1S9ArrayTwoPrefixSourceV1.successful_array_two_prefix_eq
      (stagePrepared p).alpha selected hselected
    rw [he]
    simpa [Slice.len,AspisR1S9FinishActualPairSlotV1.toNativeSlice,Array.to_slice]
      using (stagePrepared p).alpha.property
  obtain ⟨a0,a1,ap0,ap1,libra,hr0,hp0,hr1,hp1,hc0,hc1,hhelper⟩ :=
    AspisR1S9ActualPairReachedPowersCanonicalV1.actual_pair_success_reaches_canonical_powers_helper
      self (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message
      (AspisR1S9FinishActualPairSlotV1.toNative (stagePrepared p).kappa) nativeOut
      hself hfold hcanonical hpair
  exact ⟨self,selected,nativeOut,a0,a1,ap0,ap1,libra,hnew,hself,hselected,hpair,
    hr0,hp0,hr1,hp1,hc0,hc1,hhelper⟩

#print axioms resume_finish_concrete_success_same_powers_helper
end AspisR1S9ResumeFinishConcreteProducersV1
