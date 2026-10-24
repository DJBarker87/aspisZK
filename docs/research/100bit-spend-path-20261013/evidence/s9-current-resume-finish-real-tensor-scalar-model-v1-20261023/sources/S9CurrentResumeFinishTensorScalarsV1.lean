import S9CurrentPairTensorScalarModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CurrentResumeFinishTensorScalarsV1
open AspisR1S9ResumeFinishNativePairBindingV1
open AspisR1S9CurrentPairTensorModelV1
open AspisR1S9CurrentPairTensorScalarModelV1 (ScalarRegularTrace actual_trace_tensor_and_scalars)
open AspisR1S9FinishActualConstructorSlotV1
open AspisR1S9FactorTableSemanticsV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- ONE constructor model for the SAME accepted current resume/finish and
all REAL regular tensor AND scalar calls in its native Pair. No input canonicality,
independent tensor/scalar success, factor canonicality, power canonicality or per-call model is assumed. Shared runs retain
only kinds2,5,6; unshared runs retain1,2,3,5,6. Other finish slots/raw/actual
caller/Box/runtime and full weighted-dot/shared-high equations remain open.
Actual trace ap0/ap1 canonicality follows by determinism from the SAME reads
and SAME powers calls in the proved producer, never independent hpowers. -/
theorem current_resume_finish_same_model_actual_tensor_scalars {D H : Type}
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
      digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash = .ok (.Ok (p,acc)))
    (hfinish : AspisR1FinishRelationCurrent.verifier.finish_relation
      (AspisR1S9FinishActualConstructorSlotV1.installActualConstructor ops)
      v (stagePrepared p) a obs = .ok (.Ok ())) :
    ∃ (self : AspisR1S9ProductionPairCutV1.weights.Weights) (selected : Slice FW) (nativeOut : NW) (w : CW) (model : Table),
      actualNewWeightsSlot (stagePrepared p).variant
        (stagePrepared p).semantic_alpha (stagePrepared p).z=.ok (.Ok self) ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.pair self
        (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message
        (AspisR1S9FinishActualPairSlotV1.toNative (stagePrepared p).kappa)=.ok (.Ok nativeOut) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice FW))
        (stagePrepared p).alpha { «end»:=2#usize }=.ok selected ∧
      AspisR1S9ActualWeightsNewBoxNewV3.weights_new (toCtorVariant (stagePrepared p).variant)
        (AspisR1S9FinishActualConstructorSlotV1.mapArray toCtorQM (stagePrepared p).semantic_alpha)
        (AspisR1S9FinishActualConstructorSlotV1.mapArray toCtorPoint (stagePrepared p).z)=.ok (.Ok w) ∧
      self=AspisR1S9FinishActualConstructorSlotV1.fromCtorWeights w ∧ Meaning w.factors model ∧
      AspisR1S9StatementFactorOuterSemanticsV1.RowsPrefix w.points model 3 ∧
      AspisR1S9ConstructorV3CompleteFactorSemanticsV1.CircleRows
        (AspisR1S9FinishActualConstructorSlotV1.mapArray toCtorPoint (stagePrepared p).z) model ∧
      ∃ (n expectedN : Usize) (a0 a1 : NW)
        (ap0 ap1 : AspisR1S9ActualProcessKindTensorReachedV1.Powers)
        (scratch scratchOut : AspisR1S9ActualProcessKindTensorReachedV1.Scratch)
        (shared : Bool) (partsOut : AspisR1S9ActualProcessKindTensorReachedV1.Parts),
        (Slice.len v.final_message /32#usize : Result Usize)=.ok n ∧
        AspisR1S9ProductionPairCutV1.weights.Weights.pair_loop0
          {start:=0#usize,«end»:=2#usize} 1024#usize=.ok expectedN ∧
        (n != expectedN)=false ∧
        Slice.index_usize (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) 0#usize=.ok a0 ∧
        AspisR1S9ProductionPairCutV1.weights.powers 4#usize a0=.ok ap0 ∧
        Slice.index_usize (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) 1#usize=.ok a1 ∧
        AspisR1S9ProductionPairCutV1.weights.powers 4#usize a1=.ok ap1 ∧
        AspisR1S9ProductionPairCutV1.aspis_core.r0.heap.filled
          AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.Insts.CoreMarkerCopy n
          AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.ZERO=.ok (.Ok scratch) ∧
        AspisR1S9ProductionPairCutV1.weights.shared_two_point_guard self 2#usize=.ok shared ∧
        AspisR1S9ActualPairScalarCallbackV1.GoodArray ap0 ∧
        AspisR1S9ActualPairScalarCallbackV1.GoodArray ap1 ∧
        ScalarRegularTrace model self shared
          (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message 2#usize n ap0 ap1
          scratch scratchOut (Array.repeat 7#usize
            AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ZERO) partsOut := by
  obtain ⟨self,selected,nativeOut,b0,b1,bp0,bp1,libra,hnew,hs2,hf,hpc,hec,hselected,hpair,hrb0,hpb0,hrb1,hpb1,hcb0,hcb1,hsb0,hsb1,hhelper⟩ :=
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
  obtain ⟨n,expectedN,a0,a1,ap0,ap1,scratch,scratchOut,shared,partsOut,
      hn,hexpected,hguard,ha0,hap0,ha1,hap1,hfilled,hshared,htrace⟩ :=
    AspisR1S9ActualPairTensorCallsV1.actual_pair_success_tensor_calls
      self (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message
      (AspisR1S9FinishActualPairSlotV1.toNative (stagePrepared p).kappa) nativeOut hs2 hfold hpair
  have hmtrace := actual_trace_same_model w model self hself hm hf shared
    (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message n ap0 ap1
    scratch scratchOut (Array.repeat 7#usize
      AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ZERO) partsOut htrace
  have ea0 : a0=b0 := Result.ok.inj (ha0.symm.trans hrb0)
  have ea1 : a1=b1 := Result.ok.inj (ha1.symm.trans hrb1)
  have eap0 : ap0=bp0 := by
    rw [ea0] at hap0
    exact Result.ok.inj (hap0.symm.trans hpb0)
  have eap1 : ap1=bp1 := by
    rw [ea1] at hap1
    exact Result.ok.inj (hap1.symm.trans hpb1)
  have hcap0 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap0 := by
    rw [eap0]
    exact hcb0
  have hcap1 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap1 := by
    rw [eap1]
    exact hcb1
  have hboth := actual_trace_tensor_and_scalars model self shared
    (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message n ap0 ap1
    scratch scratchOut (Array.repeat 7#usize
      AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ZERO) partsOut
    hs2 hf hcap0 hcap1 hmtrace
  exact ⟨self,selected,nativeOut,w,model,hnew,hpair,hselected,hsource,hself,hm,hrows,hcircle,
    n,expectedN,a0,a1,ap0,ap1,scratch,scratchOut,shared,partsOut,
    hn,hexpected,hguard,ha0,hap0,ha1,hap1,hfilled,hshared,hcap0,hcap1,hboth⟩

#print axioms current_resume_finish_same_model_actual_tensor_scalars
end AspisR1S9CurrentResumeFinishTensorScalarsV1
