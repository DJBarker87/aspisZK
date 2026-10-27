import RPu_FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_PreparedMul
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_PreparedNew (NP PP prepared)
open FIv_Map (map map_bind map_ok)
theorem component (a : Array U32 3#usize) (x : NC) :
    map cm (FIq_Native.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call () (a,x))=
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call () (a,cm x) := by
  unfold FIq_Native.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
  change map cm (do
    let m ← Array.index_usize a 0#usize
    let m0 ← FIq_Native.field.M31.mul m x.a
    let m1 ← Array.index_usize a 1#usize
    let m11 ← FIq_Native.field.M31.mul m1 x.b
    let m2 ← Array.index_usize a 2#usize
    let m3 ← FIq_Native.field.M31.add x.a x.b
    let m21 ← FIq_Native.field.M31.mul m2 m3
    let m4 ← FIq_Native.field.M31.sub m0 m11
    let m5 ← FIq_Native.field.M31.sub m21 m0
    let m6 ← FIq_Native.field.M31.sub m5 m11
    ok ⟨m4,m6⟩) = _
  simp only [map_bind,map_ok,cm,m31_mul,m31_add,m31_sub]

theorem mapped (p : NP) (x : NQ) : map qm (FIq_Native.field.PreparedQm31Multiplier.mul p x)=
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul (prepared p) (qm x) := by
  simp only [FIq_Native.field.PreparedQm31Multiplier.mul,
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul,prepared,qm,
    map_bind,map_ok,← component,← FIv_NativeCM.add,← FIv_NativeCM.sub,
    ← FIv_NativeCM.by_r,bind_map]
theorem value (p : NP) (theta x out : NQ)
    (ht : FIv_NativeValue.Canon theta) (hx : FIv_NativeValue.Canon x)
    (hp : ExtractedMaskPreparedState.PreparedFor (prepared p) (qm theta))
    (run : FIq_Native.field.PreparedQm31Multiplier.mul p x=ok out) :
    FIv_NativeValue.Canon out ∧ FIv_NativeValue.decode out=FIv_NativeValue.decode theta*FIv_NativeValue.decode x := by
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
