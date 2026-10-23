import S9CurrentResumeFinishTensorScalarsV1
import S9SharedHighScalarAssemblyV1
import S9RegularPartsCanonicalV1
import S9ActualPairSharedCallsV1
import S9SharedCommonConstructorModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CurrentResumeSharedHighAssemblyV1
open AspisR1S9ResumeFinishNativePairBindingV1
open AspisR1S9CurrentPairTensorModelV1
open AspisR1S9FinishActualConstructorSlotV1
open AspisR1S9FactorTableSemanticsV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- The current reader and accepted finish choose ONE constructor receiver and
model. If its actual source guard selects sharing, the SAME accepted Pair
produces a completely interpreted common buffer and passes that buffer to the
actual successful partial/high calls. It also supplies the four scalar
PERM/quarter equations, exact scale/product meanings, parts1/3 writes and
all-other-cell frame, and canonical parts before/after high assembly. No canonicality/model/child-success
premises are added. The guard condition describes the actual branch only. -/
theorem current_resume_finish_same_shared_high_assembly {D H : Type}
    (readerOps : AspisR1Stage2.ResumeOps)
    (digest : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (hash : H)
    (p : AspisR1Stage2.verifier.Prepared) (acc : AspisR1Stage2.verifier.Accumulator)
    (ops : AspisR1FinishRelationCurrent.FinishOps AspisR1S9ProductionPairCutV1.weights.Weights D)
    (v : AspisR1FinishRelationCurrent.verifier.View)
    (a : AspisR1FinishRelationCurrent.verifier.Accumulator)
    (obs : Option (AspisR1FinishRelationCurrent.verifier.Phase → Result Unit))
    (hresume : AspisR1Stage2.verifier.resumeWithOps
      (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders readerOps)
      digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash=.ok (.Ok (p,acc)))
    (hfinish : AspisR1FinishRelationCurrent.verifier.finish_relation
      (AspisR1S9FinishActualConstructorSlotV1.installActualConstructor ops)
      v (stagePrepared p) a obs=.ok (.Ok ())) :
    ∃ (self : AspisR1S9ProductionPairCutV1.weights.Weights) (selected : Slice FW)
      (nativeOut : NW) (w : CW) (model : Table),
      actualNewWeightsSlot (stagePrepared p).variant (stagePrepared p).semantic_alpha
        (stagePrepared p).z=.ok (.Ok self) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice FW))
        (stagePrepared p).alpha {«end»:=2#usize}=.ok selected ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.pair self
        (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message
        (AspisR1S9FinishActualPairSlotV1.toNative (stagePrepared p).kappa)=.ok (.Ok nativeOut) ∧
      self=AspisR1S9FinishActualConstructorSlotV1.fromCtorWeights w ∧ Meaning w.factors model ∧
      (AspisR1S9ProductionPairCutV1.weights.shared_two_point_guard self 2#usize=.ok true →
        ∃ (a0 a1 : NW) (ap0 ap1 : AspisR1S9ActualProcessKindTensorReachedV1.Powers)
          (partsRegular partsShared : AspisR1S9ActualProcessKindTensorReachedV1.Parts)
          (common : AspisR1S9SharedCommonBodyTraceV1.Common)
          (partials : Array NW 4#usize),
          AspisR1S9ProductionPairCutV1.weights.Weights.pair_loop1
            {start:=0#usize,«end»:=16#usize} self
            (Array.repeat 16#usize AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.ZERO)=
              .ok (self,common) ∧
          (∀ (j : Usize) (hj : j.val<16),
            AspisR1S9SharedCommonBodyMeaningV1.Can (AspisR1S9FactorArrayEntryV1.atN common j hj) ∧
            AspisR1S9ActualTensorArithmeticV1.decode (AspisR1S9FactorArrayEntryV1.atN common j hj)=
              model 0 2 (j.val%4)*model 0 3 (j.val/4)) ∧
          AspisR1S9ProductionPairCutV1.weights.shared_partials v.final_message common=.ok (.Ok partials) ∧
          AspisR1S9ProductionPairCutV1.weights.shared_high partials self ap0 ap1 partsRegular=
            .ok (.Ok (),partsShared) ∧
          AspisR1S9ActualFinalSumV1.Good partsRegular ∧
          AspisR1S9ActualPairScalarCallbackV1.GoodArray ap0 ∧
          AspisR1S9ActualPairScalarCallbackV1.GoodArray ap1 ∧
          Slice.index_usize (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) 0#usize=.ok a0 ∧
          AspisR1S9ProductionPairCutV1.weights.powers 4#usize a0=.ok ap0 ∧
          Slice.index_usize (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) 1#usize=.ok a1 ∧
          AspisR1S9ProductionPairCutV1.weights.powers 4#usize a1=.ok ap1 ∧
          AspisR1S9ActualIndexedPowersSemanticsV1.Output a0 ap0 ∧
          AspisR1S9ActualIndexedPowersSemanticsV1.Output a1 ap1 ∧
          AspisR1S9SharedHighScalarAssemblyV1.Assembly partials self ap0 ap1 partsRegular partsShared) := by
  obtain ⟨self,selected,nativeOut,b0,b1,bp0,bp1,libra,hnew,hs2,hf,hpc,hec,hselected,hpair,
    hrb0,hpb0,hrb1,hpb1,hcb0,hcb1,hsb0,hsb1,hhelper⟩ :=
    AspisR1S9CurrentReaderNativeProducersV1.current_resume_finish_same_canonical_receiver_exact_powers_helper
      readerOps digest bytes proof publicInput hash p acc ops v a obs hresume hfinish
  obtain ⟨halpha,hz⟩ :=
    AspisR1S9CurrentReaderConstructorInputsV1.current_resume_constructor_inputs_canonical
      readerOps digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash p acc hresume
  obtain ⟨w,hsource,hself⟩ := actualNewWeightsSlot_success
    (stagePrepared p).variant (stagePrepared p).semantic_alpha (stagePrepared p).z self hnew
  obtain ⟨model,hm,hrows,hcircle,hpoints,hvariant,hextra⟩ :=
    AspisR1S9ConstructorV3CompleteFactorSemanticsV1.constructor_success_complete_factor_semantics
      (toCtorVariant (stagePrepared p).variant) (AspisR1S9FinishActualConstructorSlotV1.mapArray toCtorQM (stagePrepared p).semantic_alpha)
      (AspisR1S9FinishActualConstructorSlotV1.mapArray toCtorPoint (stagePrepared p).z) w halpha hz hsource
  have hfold : Slice.len (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected)=2#usize := by
    apply UScalar.eq_of_val_eq
    have he := AspisR1S9ArrayTwoPrefixSourceV1.successful_array_two_prefix_eq
      (stagePrepared p).alpha selected hselected
    rw [he]
    simpa [Slice.len,AspisR1S9FinishActualPairSlotV1.toNativeSlice,Array.to_slice]
      using (stagePrepared p).alpha.property
  refine ⟨self,selected,nativeOut,w,model,hnew,hselected,hpair,hself,hm,?_⟩
  intro hguard
  obtain ⟨n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,partsShared,selfCommon,common,
      partials,hn,hn64,ha0,hap0,ha1,hap1,hfilled,hregular,hcommon,hpartials,hhigh⟩ :=
    AspisR1S9ActualPairSharedCallsV1.actual_pair_success_shared_calls self
      (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message
      (AspisR1S9FinishActualPairSlotV1.toNative (stagePrepared p).kappa) nativeOut hfold hguard hpair
  have hcan : AspisR1S9SharedCommonBodyMeaningV1.FactorsCanonical (AspisR1S9FinishActualConstructorSlotV1.fromCtorWeights w) := by
    rw [←hself]
    exact hf
  have hcommon' := hcommon
  rw [hself] at hcommon'
  obtain ⟨hreceiver,hmeaning⟩ :=
    AspisR1S9SharedCommonConstructorModelV1.constructor_common_loop_success
      w model hm hcan selfCommon _ common hcommon'
  have hreceiver' : selfCommon=self := hreceiver.trans hself.symm
  rw [hreceiver'] at hcommon hhigh
  have ea0 : a0=b0 := Result.ok.inj (ha0.symm.trans hrb0)
  have ea1 : a1=b1 := Result.ok.inj (ha1.symm.trans hrb1)
  have eap0 : ap0=bp0 := by
    rw [ea0] at hap0
    exact Result.ok.inj (hap0.symm.trans hpb0)
  have eap1 : ap1=bp1 := by
    rw [ea1] at hap1
    exact Result.ok.inj (hap1.symm.trans hpb1)
  have hcap0 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap0 := by
    rw [eap0]; exact hcb0
  have hcap1 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap1 := by
    rw [eap1]; exact hcb1
  have hparts := AspisR1S9RegularPartsCanonicalV1.regular_from_zero_success_good
    self true (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message
    n ap0 ap1 scratch scratchOut partsRegular hs2 hcap0 hcap1 hregular
  have hassembly := AspisR1S9SharedHighScalarAssemblyV1.shared_high_success_value_assembly
    partials self ap0 ap1 partsRegular partsShared hf hcap0 hcap1 hparts hhigh
  have hsFresh0 : AspisR1S9ActualIndexedPowersSemanticsV1.Output a0 ap0 := by
    rw [ea0,eap0]; exact hsb0
  have hsFresh1 : AspisR1S9ActualIndexedPowersSemanticsV1.Output a1 ap1 := by
    rw [ea1,eap1]; exact hsb1
  exact ⟨a0,a1,ap0,ap1,partsRegular,partsShared,common,partials,hcommon,hmeaning,hpartials,hhigh,
    hparts,hcap0,hcap1,ha0,hap0,ha1,hap1,hsFresh0,hsFresh1,hassembly⟩

#print axioms current_resume_finish_same_shared_high_assembly
end AspisR1S9CurrentResumeSharedHighAssemblyV1
