import RPu_FJb_RawConversion
import RPu_FJb_RawRowCallbacks
import RPu_FJb_BuilderStable
import RPu_RawPoseidonExternalRowExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_RawRowValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon decode)
open FJb_RawRowCallbacks (Input)
abbrev callback := state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
abbrev oldCallback := AspisR1SelectedMaskProbe.state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
/-- Native row value, including its actual ordered from_fn constructor. -/
theorem value (input : Input) (output : Usize) (ho : output.val < 4)
    (out : NQ) (run : state_only_poseidon.external_linear_lazy_row input output=ok out) :
    Canon out ∧ decode out=R0P.poseidonMat4
      (fun i=>RawPoseidonRowField.decodeWords (RawPoseidonExternalRowExact.inputWords input i))
      ⟨output.val,ho⟩ := by
  unfold state_only_poseidon.external_linear_lazy_row at run
  obtain ⟨raw,hraw,converted⟩ := FIv_Map.bind_success _ _ _ run
  have oldRaw := FJb_BuilderStable.total 4#usize core.marker.CopyU64 callback 0#u64
    (input,output) (fun i hi=>FJb_RawRowCallbacks.total input output i ho hi) raw hraw
  have oldRaw' : AspisR1SelectedMaskProbe.array_from_fn_copy 4#usize core.marker.CopyU64
      oldCallback 0#u64 (input,output)=ok raw := by
    exact oldRaw
  have oldConverted : AspisR1SelectedMaskProbe.state_only_poseidon.extension_from_raw_limbs raw=ok (qm out) := by
    rw [←FJb_RawConversion.converted,converted,FIv_Map.map_ok]
  have oldRun : AspisR1SelectedMaskProbe.state_only_poseidon.external_linear_lazy_row input output=ok (qm out) := by
    unfold AspisR1SelectedMaskProbe.state_only_poseidon.external_linear_lazy_row
    rw [oldRaw',bind_tc_ok,oldConverted]
  obtain ⟨q,hq,hc,hv⟩ := RawPoseidonExternalRowExact.external_linear_lazy_row_exact input output ho
  have he : q=qm out := Result.ok.inj (hq.symm.trans oldRun)
  subst q
  exact ⟨hc,hv⟩
#print axioms value
end AspisR1.FJb_RawRowValue
end
