import LPh_NativeWords
import ExtractedMaskQM31Exact
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPh.Native
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)
abbrev PQ := AspisR1SelectedMaskProbe.field.QM31

def toProbe (x : NQ) : PQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromProbe (x : PQ) : NQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩

theorem q_projection_spec (x y : NQ) (hx : FIo_QMValues.Canon x) (hy : FIo_QMValues.Canon y) :
    qWords (decodeQM (qm x)*decodeQM (qm y)) =
      ExtractedMaskQM31Mul.qmMulWords (nativeQWords x) (nativeQWords y) := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedMaskQM31Exact.current_qm_mul_exact (toProbe x) (toProbe y) hx hy
  obtain ⟨w,hw,_,hword⟩ := ExtractedMaskQM31Mul.current_qm_mul_words (toProbe x) (toProbe y) hx hy
  have same : w=z := Result.ok.inj (hw.symm.trans hz)
  subst w
  have hv' : decodeQM (qm (fromProbe z))=decodeQM (qm x)*decodeQM (qm y) := hv
  calc
    qWords (decodeQM (qm x)*decodeQM (qm y)) = qWords (decodeQM (qm (fromProbe z))) := congrArg qWords hv'.symm
    _ = nativeQWords (fromProbe z) := qWords_decode _ hc
    _ = ExtractedMaskQM31Mul.qmMulWords (nativeQWords x) (nativeQWords y) := hword

theorem qm_mul_expanded (x y : NQ) (hx : FIo_QMValues.Canon x) (hy : FIo_QMValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul x y=ok z ∧ FIo_QMValues.Canon z ∧
      nativeQWords z=ExtractedMaskQM31Mul.qmMulWords (nativeQWords x) (nativeQWords y) := by
  obtain ⟨z,hz,hc,hv⟩ := qm_mul_words x y hx hy
  exact ⟨z,hz,hc,hv.trans (q_projection_spec x y hx hy)⟩
#print axioms q_projection_spec
#print axioms qm_mul_expanded
end AspisR1.LPh.Native
end
