import FIt_PreparedNew
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_PreparedMul
open Aeneas Aeneas.Std Result
open FIr_NativeArithmetic
open FIt_PreparedNew (NP PP prepared)
open FIo_FieldBridge (map map_bind map_ok)
theorem component (a : Array U32 3#usize) (x : NC) :
    map cm (FIq_Native.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call () (a,x))=
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call () (a,cm x) := by
  unfold FIq_Native.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
  dsimp only
  simp only [cm,map_bind,map_ok,m31_mul,m31_add,m31_sub]

theorem mapped (p : NP) (x : NQ) : map qm (FIq_Native.field.PreparedQm31Multiplier.mul p x)=
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul (prepared p) (qm x) := by
  simp only [FIq_Native.field.PreparedQm31Multiplier.mul,
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul,prepared,qm,
    map_bind,map_ok,← component,← FIr_NativeCM.add,← FIr_NativeCM.sub,
    ← FIr_NativeCM.by_r,bind_map]
theorem value (p : NP) (theta x out : NQ)
    (ht : FIr_NativeValue.Canon theta) (hx : FIr_NativeValue.Canon x)
    (hp : ExtractedMaskPreparedState.PreparedFor (prepared p) (qm theta))
    (run : FIq_Native.field.PreparedQm31Multiplier.mul p x=ok out) :
    FIr_NativeValue.Canon out ∧ FIr_NativeValue.decode out=FIr_NativeValue.decode theta*FIr_NativeValue.decode x := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedMaskPreparedMul.prepared_mul_exact (prepared p) (qm theta) (qm x) ht hx hp
  have same := mapped p x
  rw [run,map_ok,hz] at same
  have eq := Result.ok.inj same
  refine ⟨?_,by change ExtractedMaskQM31Exact.decode (qm out)=_;rw [eq];exact hv⟩
  change ExtractedMaskQM31Exact.CurrentCanonicalQM (qm out)
  rw [eq]
  exact hc
#print axioms component
#print axioms mapped
#print axioms value
end AspisR1.FIv_PreparedMul
end
