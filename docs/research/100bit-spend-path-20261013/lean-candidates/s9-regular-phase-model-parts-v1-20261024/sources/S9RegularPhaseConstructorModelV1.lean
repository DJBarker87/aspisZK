import S9RegularPhaseModelPreludeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
open scoped BigOperators
namespace AspisR1S9RegularPhaseConstructorModelV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9RegularKindExecutionV1
open AspisR1S9ActualRegularKindsTraceV1
open AspisR1S9FactorArrayEntryV1
open AspisR1S9ConstructorTableNativeTensorV1
open AspisR1S9FactorTableSemanticsV1 (Table Meaning)
open AspisR1S9RegularRowIndicesV1
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
open AspisR1S9SharedHighConstructorModelV1 (rowValue)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- Actual3/5-kind regular phase, SAME final returned parts array. Each point
meaning follows its own accepted stored write and every later distinct-index
write frame. No independent kind/callee success or desired output premise. -/
theorem actual_regular_phase_model_parts
    (w : CW) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtorWeights w))
    (shared : Bool) (alpha : Slice W) (f : Slice U8) (a0 a1 : W)
    (ha0 : Can a0) (ha1 : Can a1) (ap0 ap1 : Powers)
    (hp0 : weights.powers 4#usize a0=.ok ap0) (hp1 : weights.powers 4#usize a1=.ok ap1)
    (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (hs2 : (fromCtorWeights w).variant=transport.Variant.S2)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hcall : weights.process_regular_kinds (fromCtorWeights w) shared alpha f 2#usize 64#usize ap0 ap1 scratch parts=
      .ok (.Ok (),scratchOut,partsOut)) :
    if shared then
      Means model (decodeNative a0) (decodeNative a1) f partsOut 2#usize (by decide) 1 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsOut 5#usize (by decide) 3 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsOut 6#usize (by decide) 4
    else
      Means model (decodeNative a0) (decodeNative a1) f partsOut 1#usize (by decide) 0 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsOut 2#usize (by decide) 1 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsOut 3#usize (by decide) 2 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsOut 5#usize (by decide) 3 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsOut 6#usize (by decide) 4 := by
  have value := kind_success_stored_model w model hm hc
  have frame := kind_success_other_index_frame (fromCtorWeights w)
  have ht := regular_success_trace (fromCtorWeights w) shared alpha f 2#usize 64#usize
    ap0 ap1 scratch scratchOut parts partsOut hcall
  cases shared with
  | true =>
    simp only [RegularTrace,↓reduceIte] at ht
    simp only [↓reduceIte]
    obtain ⟨s1,s2,p1,p2,h1,h2,h3⟩ := ht
    have m1 := value 2#usize (by decide) (by rw [row_two];decide)
      alpha f a0 a1 ha0 ha1 ap0 ap1 hp0 hp1 scratch s1 parts p1 hs2 hdiv h1
    have v1 : Means model (decodeNative a0) (decodeNative a1) f p1 2#usize (by decide) 1 := by
      simpa only [row_two] using m1
    have m2 := value 5#usize (by decide) (by rw [row_five];decide)
      alpha f a0 a1 ha0 ha1 ap0 ap1 hp0 hp1 s1 s2 p1 p2 hs2 hdiv h2
    have v2 : Means model (decodeNative a0) (decodeNative a1) f p2 5#usize (by decide) 3 := by
      simpa only [row_five] using m2
    have m3 := value 6#usize (by decide) (by rw [row_six];decide)
      alpha f a0 a1 ha0 ha1 ap0 ap1 hp0 hp1 s2 scratchOut p2 partsOut hs2 hdiv h3
    have v3 : Means model (decodeNative a0) (decodeNative a1) f partsOut 6#usize (by decide) 4 := by
      simpa only [row_six] using m3
    have f12 := frame 5#usize 2#usize alpha f 64#usize ap0 ap1
      s1 s2 p1 p2 hs2 (by decide) (by decide) (by decide) h2
    have f13 := frame 6#usize 2#usize alpha f 64#usize ap0 ap1
      s2 scratchOut p2 partsOut hs2 (by decide) (by decide) (by decide) h3
    have out1 : Means model (decodeNative a0) (decodeNative a1) f partsOut 2#usize (by decide) 1 :=
      (congrArg decodeNative (f13.trans (f12))).trans v1
    have f23 := frame 6#usize 5#usize alpha f 64#usize ap0 ap1
      s2 scratchOut p2 partsOut hs2 (by decide) (by decide) (by decide) h3
    have out2 : Means model (decodeNative a0) (decodeNative a1) f partsOut 5#usize (by decide) 3 :=
      (congrArg decodeNative (f23)).trans v2
    have out3 := v3
    exact ⟨out1,out2,out3⟩
  | false =>
    simp only [RegularTrace,Bool.false_eq_true,↓reduceIte] at ht
    simp only [Bool.false_eq_true,↓reduceIte]
    obtain ⟨s1,s2,s3,s4,p1,p2,p3,p4,h1,h2,h3,h4,h5⟩ := ht
    have m1 := value 1#usize (by decide) (by rw [row_one];decide)
      alpha f a0 a1 ha0 ha1 ap0 ap1 hp0 hp1 scratch s1 parts p1 hs2 hdiv h1
    have v1 : Means model (decodeNative a0) (decodeNative a1) f p1 1#usize (by decide) 0 := by
      simpa only [row_one] using m1
    have m2 := value 2#usize (by decide) (by rw [row_two];decide)
      alpha f a0 a1 ha0 ha1 ap0 ap1 hp0 hp1 s1 s2 p1 p2 hs2 hdiv h2
    have v2 : Means model (decodeNative a0) (decodeNative a1) f p2 2#usize (by decide) 1 := by
      simpa only [row_two] using m2
    have m3 := value 3#usize (by decide) (by rw [row_three];decide)
      alpha f a0 a1 ha0 ha1 ap0 ap1 hp0 hp1 s2 s3 p2 p3 hs2 hdiv h3
    have v3 : Means model (decodeNative a0) (decodeNative a1) f p3 3#usize (by decide) 2 := by
      simpa only [row_three] using m3
    have m4 := value 5#usize (by decide) (by rw [row_five];decide)
      alpha f a0 a1 ha0 ha1 ap0 ap1 hp0 hp1 s3 s4 p3 p4 hs2 hdiv h4
    have v4 : Means model (decodeNative a0) (decodeNative a1) f p4 5#usize (by decide) 3 := by
      simpa only [row_five] using m4
    have m5 := value 6#usize (by decide) (by rw [row_six];decide)
      alpha f a0 a1 ha0 ha1 ap0 ap1 hp0 hp1 s4 scratchOut p4 partsOut hs2 hdiv h5
    have v5 : Means model (decodeNative a0) (decodeNative a1) f partsOut 6#usize (by decide) 4 := by
      simpa only [row_six] using m5
    have f12 := frame 2#usize 1#usize alpha f 64#usize ap0 ap1
      s1 s2 p1 p2 hs2 (by decide) (by decide) (by decide) h2
    have f13 := frame 3#usize 1#usize alpha f 64#usize ap0 ap1
      s2 s3 p2 p3 hs2 (by decide) (by decide) (by decide) h3
    have f14 := frame 5#usize 1#usize alpha f 64#usize ap0 ap1
      s3 s4 p3 p4 hs2 (by decide) (by decide) (by decide) h4
    have f15 := frame 6#usize 1#usize alpha f 64#usize ap0 ap1
      s4 scratchOut p4 partsOut hs2 (by decide) (by decide) (by decide) h5
    have out1 : Means model (decodeNative a0) (decodeNative a1) f partsOut 1#usize (by decide) 0 :=
      (congrArg decodeNative (f15.trans (f14.trans (f13.trans (f12))))).trans v1
    have f23 := frame 3#usize 2#usize alpha f 64#usize ap0 ap1
      s2 s3 p2 p3 hs2 (by decide) (by decide) (by decide) h3
    have f24 := frame 5#usize 2#usize alpha f 64#usize ap0 ap1
      s3 s4 p3 p4 hs2 (by decide) (by decide) (by decide) h4
    have f25 := frame 6#usize 2#usize alpha f 64#usize ap0 ap1
      s4 scratchOut p4 partsOut hs2 (by decide) (by decide) (by decide) h5
    have out2 : Means model (decodeNative a0) (decodeNative a1) f partsOut 2#usize (by decide) 1 :=
      (congrArg decodeNative (f25.trans (f24.trans (f23)))).trans v2
    have f34 := frame 5#usize 3#usize alpha f 64#usize ap0 ap1
      s3 s4 p3 p4 hs2 (by decide) (by decide) (by decide) h4
    have f35 := frame 6#usize 3#usize alpha f 64#usize ap0 ap1
      s4 scratchOut p4 partsOut hs2 (by decide) (by decide) (by decide) h5
    have out3 : Means model (decodeNative a0) (decodeNative a1) f partsOut 3#usize (by decide) 2 :=
      (congrArg decodeNative (f35.trans (f34))).trans v3
    have f45 := frame 6#usize 5#usize alpha f 64#usize ap0 ap1
      s4 scratchOut p4 partsOut hs2 (by decide) (by decide) (by decide) h5
    have out4 : Means model (decodeNative a0) (decodeNative a1) f partsOut 5#usize (by decide) 3 :=
      (congrArg decodeNative (f45)).trans v4
    have out5 := v5
    exact ⟨out1,out2,out3,out4,out5⟩

#print axioms actual_regular_phase_model_parts
end AspisR1S9RegularPhaseConstructorModelV1
