import S9StrictResumeFinishReceiverCanonicalV1
import S9ActualPairHelperOriginalCoefficientsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9StrictResumeFinishOriginalCoefficientsV1
open AspisR1S9ResumeFinishNativePairBindingV1
open AspisR1S9ActualPairOldCarrierScalarV1
open AspisR1S9ActualPairHelperOriginalCoefficientsV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev mapArray := @AspisR1S9ActualPairOldCarrierScalarV1.mapArray
abbrev NA := Array NW 4#usize

def OriginalCoefficients (ap0 ap1 : NA)
    (extra : Array AspisR1S9ProductionPairCutV1.aspis_core.field.QM31 2#usize)
    (output : NA) : Prop :=
    GoodArray output ∧ ∃ q0 q1 : AspisR1S9ProductionPairCutV1.aspis_core.field.QM31,
      Array.index_usize extra 0#usize = .ok q0 ∧
      Array.index_usize extra 1#usize = .ok q1 ∧
      (∀ j : Fin 4, CW (cells (mapArray toHelperW output) j)) ∧
      (∀ j : Fin 4,
        TraceDecode (cells (mapArray toHelperW output) j) =
          AspisR1.S2LibraFactoredIdentity.original
            (ScaledBase (mapArray toHelperW ap0)) (ScaledBase (mapArray toHelperW ap1))
            (Seed (toHelperQ q0)) (Seed (toHelperQ q1)) j)

/-- The same strict-resume and concrete constructor/Pair finish execution
supplies canonical receiver state, exact powers, and the actual helper's
original S2 coefficient equations. No independent helper/input-canonicality
or arithmetic-success premise is added. Other finish slots and runtime remain
explicit outer boundaries. -/
theorem strict_resume_finish_same_original_coefficients {D H : Type}
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
        ap0 ap1 self.extra = .ok libra ∧
      OriginalCoefficients ap0 ap1 self.extra libra := by
  obtain ⟨self,selected,nativeOut,a0,a1,ap0,ap1,libra,hnew,hself,hf,hp,he,hselected,hpair,
      hr0,hp0,hr1,hp1,hc0,hc1,hs0,hs1,hhelper⟩ :=
    AspisR1S9StrictResumeFinishReceiverCanonicalV1.strict_resume_finish_same_canonical_receiver_exact_powers_helper
      readerOps digest bytes proof publicInput hash p acc ops v a obs hresume hfinish
  have hcoeff : OriginalCoefficients ap0 ap1 self.extra libra :=
    AspisR1S9ActualPairHelperOriginalCoefficientsV1.actual_helper_original_coefficients
      ap0 ap1 self.extra libra hc0 hc1 he hhelper
  exact ⟨self,selected,nativeOut,a0,a1,ap0,ap1,libra,hnew,hself,hf,hp,he,hselected,hpair,
    hr0,hp0,hr1,hp1,hc0,hc1,hs0,hs1,hhelper,hcoeff⟩

#print axioms strict_resume_finish_same_original_coefficients
end AspisR1S9StrictResumeFinishOriginalCoefficientsV1
