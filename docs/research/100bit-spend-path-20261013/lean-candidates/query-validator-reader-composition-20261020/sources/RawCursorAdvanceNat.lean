import AspisR1Stage2AdoptedReader.RawCursorAdvance

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2AdoptedReader.RawCursorAdvanceNat

abbrev Reader := _root_.AspisR1Stage2AdoptedResume.verifier.Reader

theorem raw_success_advances_value
    (N : Usize) (self : Reader) (chunk : Array Std.U8 N) (next : Reader)
    (h : _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw N self = ok (chunk, next)) :
    next.«at».val = self.«at».val + N.val := by
  obtain ⟨target, hadd, hnext⟩ :=
    AspisR1Stage2AdoptedReader.RawCursorAdvance.raw_success_cursor_is_its_checked_add
      N self chunk next h
  have hadd_spec := UScalar.add_equiv self.«at» N
  rw [hadd] at hadd_spec
  simp only [Result.ok.injEq] at hadd_spec
  rcases hadd_spec with ⟨_, hval, _⟩
  rw [hnext, hval]

#print axioms raw_success_advances_value

end AspisR1Stage2AdoptedReader.RawCursorAdvanceNat
