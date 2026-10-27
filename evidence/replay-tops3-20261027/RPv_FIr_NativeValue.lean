import RPv_FIr_NativeQM
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_NativeValue
open Aeneas Aeneas.Std Result
open FIr_NativeArithmetic
open FIo_FieldBridge (map map_ok)
abbrev K := ExtractedMaskQM31Exact.QM31Exact
abbrev Canon (x : NQ) := ExtractedMaskQM31Exact.CurrentCanonicalQM (qm x)
abbrev decode (x : NQ) : K := ExtractedMaskQM31Exact.decode (qm x)

theorem add (x y z : NQ) (hx : Canon x) (hy : Canon y)
    (run : FIq_Native.field.QM31.add x y=ok z) :
    Canon z ∧ decode z=decode x+decode y := by
  obtain ⟨r,returned,canon,value⟩ := ExtractedMaskQM31Exact.current_qm_add_exact (qm x) (qm y) hx hy
  have mapped := FIr_NativeQM.add x y
  rw [run,map_ok,returned] at mapped
  have same := Result.ok.inj mapped
  rw [← same] at canon value
  exact ⟨canon,value⟩

theorem mul (x y z : NQ) (hx : Canon x) (hy : Canon y)
    (run : FIq_Native.field.QM31.mul x y=ok z) :
    Canon z ∧ decode z=decode x*decode y := by
  obtain ⟨r,returned,canon,value⟩ := ExtractedMaskQM31Exact.current_qm_mul_exact (qm x) (qm y) hx hy
  have mapped := FIr_NativeQM.mul x y
  rw [run,map_ok,returned] at mapped
  have same := Result.ok.inj mapped
  rw [← same] at canon value
  exact ⟨canon,value⟩

theorem zero : Canon FIq_Native.field.QM31.ZERO ∧ decode FIq_Native.field.QM31.ZERO=0 := by
  constructor
  · rw [FIq_Native.field.QM31.ZERO]
    exact ⟨⟨by decide,by decide⟩,⟨by decide,by decide⟩⟩
  · simp only [FIq_Native.field.QM31.ZERO,decode,ExtractedMaskQM31Exact.decode,qm,cm]
    rfl

theorem one : Canon FIq_Native.field.QM31.ONE ∧ decode FIq_Native.field.QM31.ONE=1 := by
  constructor
  · rw [FIq_Native.field.QM31.ONE]
    exact ⟨⟨by decide,by decide⟩,⟨by decide,by decide⟩⟩
  · simp only [FIq_Native.field.QM31.ONE,decode,ExtractedMaskQM31Exact.decode,qm,cm]
    rfl

#print axioms add
#print axioms mul
#print axioms zero
#print axioms one
end AspisR1.FIr_NativeValue
end
