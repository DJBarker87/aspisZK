import RPv_FIr_NativeQM
import ExtractedMaskQM31Mul
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NDE_MulStubValue
open AspisR1.FIr_NativeArithmetic
open AspisR1.FIo_FieldBridge (map)
abbrev Canon (x : NQ) := AspisR1.ExtractedMaskTowerAdd.CanonicalQM (qm x)
abbrev words (x : NQ) := AspisR1.ExtractedMaskQM31Mul.wordsQM (qm x)
def fromProbe (q : PQ) : NQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem roundtrip (x : NQ) : fromProbe (qm x) = x := by
  cases x; rfl

theorem reflect_ok {α β : Type} (f : α → β) (g : β → α)
    (roundtrip : ∀ x, g (f x) = x) (r : Result α) (z : β)
    (h : map f r = ok z) : r = ok (g z) := by
  cases r with
  | ok x =>
    have e := Result.ok.inj h
    rw [← e, roundtrip]
  | fail e => cases h
  | div => cases h

theorem qm31_value (x y : NQ) (hx : Canon x) (hy : Canon y) :
    ∃ z, FIq_Native.field.QM31.mul x y = ok z ∧ Canon z ∧
      words z = AspisR1.ExtractedMaskQM31Mul.qmMulWords (words x) (words y) := by
  obtain ⟨z,hz,hc,hv⟩ := AspisR1.ExtractedMaskQM31Mul.current_qm_mul_words (qm x) (qm y) hx hy
  have run := reflect_ok qm fromProbe roundtrip _ z
    ((AspisR1.FIr_NativeQM.mul x y).trans hz)
  exact ⟨fromProbe z,run,hc,hv⟩

#print axioms roundtrip
#print axioms reflect_ok
#print axioms qm31_value
end NDE_MulStubValue
end
