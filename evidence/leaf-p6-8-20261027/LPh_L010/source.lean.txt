import LPh_ExpandedQ
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPh.Native
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC NQ cm qm)
open ExtractedMaskQM31Mul

def embedC (x : NC) : NQ := ⟨x,⟨0#u32,0#u32⟩⟩

theorem c_projection_spec (x y : NC) (hx : FIo_CMValues.Canon x) (hy : FIo_CMValues.Canon y) :
    cWords (decodeC (cm x)*decodeC (cm y)) = mulWords (nativeCWords x) (nativeCWords y) := by
  have hx' : FIo_QMValues.Canon (embedC x) := ⟨hx,by change (0 : Nat)<2147483647 ∧ (0 : Nat)<2147483647; omega⟩
  have hy' : FIo_QMValues.Canon (embedC y) := ⟨hy,by change (0 : Nat)<2147483647 ∧ (0 : Nat)<2147483647; omega⟩
  have h := congrArg Prod.fst (q_projection_spec (embedC x) (embedC y) hx' hy')
  have left : Prod.fst (qWords (decodeQM (qm (embedC x))*decodeQM (qm (embedC y)))) =
      cWords (decodeC (cm x)*decodeC (cm y)) := by
    change cWords ((decodeC (cm x)*decodeC (cm y))+AspisV8R15.ExactTowerBase.qm31R*0*0) = _
    simp only [mul_zero,add_zero]
  rw [left] at h
  simpa [nativeQWords,nativeCWords,embedC,qmMulWords,mulWords,addWords,rWords] using h

theorem cm_mul_expanded (x y : NC) (hx : FIo_CMValues.Canon x) (hy : FIo_CMValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y=ok z ∧ FIo_CMValues.Canon z ∧
      nativeCWords z=mulWords (nativeCWords x) (nativeCWords y) := by
  obtain ⟨z,hz,hc,hv⟩ := cm_mul_words x y hx hy
  exact ⟨z,hz,hc,hv.trans (c_projection_spec x y hx hy)⟩
#print axioms c_projection_spec
#print axioms cm_mul_expanded
end AspisR1.LPh.Native
end
