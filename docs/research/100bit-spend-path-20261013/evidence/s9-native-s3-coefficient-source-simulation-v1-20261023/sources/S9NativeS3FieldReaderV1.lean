import S9NativeFieldS5BoundedReaderV1
import S9NativeFieldActualCanonicalV1
import S3ActualFieldOpsComplete
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9NativeS3FieldReaderV1
open AspisR1S9ProductionPairCutV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev PW := AspisR1S5PairCutFieldCallbackV1.PairWide

def nativeToOld (w : W) : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.S :=
  ⟨⟨⟨w.c0.c0.a,w.c0.c0.b⟩,⟨w.c0.c1.a,w.c0.c1.b⟩⟩,
   ⟨⟨w.c1.c0.a,w.c1.c0.b⟩,⟨w.c1.c1.a,w.c1.c1.b⟩⟩⟩
def pairToOld (w : PW) : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.S :=
  ⟨⟨⟨w.c0.c0.a,w.c0.c0.b⟩,⟨w.c0.c1.a,w.c0.c1.b⟩⟩,
   ⟨⟨w.c1.c0.a,w.c1.c0.b⟩,⟨w.c1.c1.a,w.c1.c1.b⟩⟩⟩

theorem pair_native_coordinates (w : W) : pairToOld (AspisR1S9NativeFieldS5BoundedReaderV1.toS5 w)=nativeToOld w := rfl
theorem pair_finish_coordinates (w : AspisR1CurrentWide.Proof.FinishE) :
    pairToOld (AspisR1S5PairCutFieldCallbackV1.finishToPair w)=AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.finishToS w := rfl
theorem native_current_coordinates (w : W) : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toE (nativeToOld w)=AspisR1S9ActualPairWideCanonicalV1.toCurrent w := rfl

/-- The SAME accepted native source field call supplies the SAME retained S3
reader result and decoded value. The fitting window is an actual arithmetic
caller domain; no decoder-success, input Can or desired old read is assumed. -/
theorem native_field_success_old_reader
    (bytes : Slice U8) (i : Usize) (w : W)
    (hfit : (i.val+1)*32 ≤ bytes.val.length)
    (hcall : weights.field bytes i=.ok w) :
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decodeField bytes i=.ok (nativeToOld w) ∧
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical (nativeToOld w) ∧
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decode (nativeToOld w)=AspisR1CurrentWide.Proof.decodeWide (AspisR1S9ActualPairWideCanonicalV1.toCurrent w) := by
  have hm := AspisR1S9NativeFieldS5BoundedReaderV1.native_field_maps_s5_reader bytes i (AspisR1S9NativeFieldS5BoundedReaderV1.fitting_window_safe bytes i hfit)
  rw [hcall] at hm
  have hs5 : AspisR1S5PairCutTransparentReaderV1.readerBody
      AspisR1S5PairCutTransparentReaderV1.actualPairDecoder bytes i=.ok (AspisR1S9NativeFieldS5BoundedReaderV1.toS5 w) := hm.symm
  rw [AspisR1S5PairCutTransparentReaderV1.actualReader_eq_checkedCallback] at hs5
  unfold AspisR1S5PairCutFieldCallbackV1.checkedFieldCallback at hs5
  cases hf : AspisR1CurrentWide.Proof.finishField bytes i with
  | fail e => simp only [hf,bind_tc_fail] at hs5;cases hs5
  | div => simp only [hf,bind_tc_div] at hs5;cases hs5
  | ok value =>
    simp only [hf,bind_tc_ok] at hs5
    have he := Result.ok.inj hs5
    have hv : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.finishToS value=nativeToOld w := by
      calc
        AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.finishToS value = pairToOld (AspisR1S5PairCutFieldCallbackV1.finishToPair value) :=
          (pair_finish_coordinates value).symm
        _ = pairToOld (AspisR1S9NativeFieldS5BoundedReaderV1.toS5 w) := congrArg pairToOld he
        _ = nativeToOld w := pair_native_coordinates w
    have hr : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decodeField bytes i=.ok (nativeToOld w) := by
      simp only [AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decodeField,hf,bind_tc_ok,hv]
    refine ⟨hr,AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decodeField_success_canonical bytes i (nativeToOld w) hr,?_⟩
    change AspisR1CurrentWide.Proof.decodeWide (AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toE (nativeToOld w))=_
    rw [native_current_coordinates]

#print axioms pair_native_coordinates
#print axioms pair_finish_coordinates
#print axioms native_current_coordinates
#print axioms native_field_success_old_reader
end AspisR1S9NativeS3FieldReaderV1
