import R1Z.PV_CBL_WrapperOutcomes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_WrapperSuccess
open PV_CBL_LibraryShapes
set_option autoImplicit false

theorem default_iff {T A : Type} (core : Result T) (buffer : Result (Buffer A))
    (w : Wrapper T A) :
    PV_CBL_WrapperReference.makeDefault core buffer=ok w ↔
      core=ok w.core ∧ buffer=ok w.buffer := by
  rw [PV_CBL_WrapperOutcomes.default_full_result]
  cases core <;> cases buffer <;> cases w <;> simp

theorem finalize_iff {T A Out : Type}
    (f : T→Buffer A→Out→Result (T×Buffer A×Out))
    (self : Wrapper T A) (out next : Out) :
    PV_CBL_WrapperReference.finalize f self out=ok next ↔
      ∃ c b, f self.core self.buffer out=ok (c,b,next) := by
  rw [PV_CBL_WrapperOutcomes.finalize_full_result]
  cases hf : f self.core self.buffer out with
  | fail e => simp [hf]
  | div => simp [hf]
  | ok v => rcases v with ⟨c,b,o⟩; simp [hf]
#print axioms default_iff
#print axioms finalize_iff
end R1Z.PV_CBL_WrapperSuccess
