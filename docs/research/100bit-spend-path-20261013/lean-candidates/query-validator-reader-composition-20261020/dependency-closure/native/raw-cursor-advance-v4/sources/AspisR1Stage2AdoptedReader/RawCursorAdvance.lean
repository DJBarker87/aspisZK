import AspisR1Stage2AdoptedResume.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2AdoptedReader.RawCursorAdvance

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem raw_success_cursor_is_its_checked_add
    (N : Usize) (self : _root_.AspisR1Stage2AdoptedResume.verifier.Reader)
    (chunk : Array Std.U8 N) (next : _root_.AspisR1Stage2AdoptedResume.verifier.Reader)
    (h : _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw N self = ok (chunk, next)) :
    ∃ target, self.«at» + N = ok target ∧ next.«at» = target := by
  unfold _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw at h
  obtain ⟨target, hadd, h⟩ := bind_success _ _ _ h
  obtain ⟨slice, hslice, h⟩ := bind_success _ _ _ h
  obtain ⟨array, harray, h⟩ := bind_success _ _ _ h
  obtain ⟨bytes, hbytes, h⟩ := bind_success _ _ _ h
  simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at h
  rcases h with ⟨_, hnext⟩
  exact ⟨target, hadd, by simpa only [_root_.AspisR1Stage2AdoptedResume.verifier.Reader.mk.injEq] using (congrArg _root_.AspisR1Stage2AdoptedResume.verifier.Reader.at hnext).symm⟩

#print axioms raw_success_cursor_is_its_checked_add

end AspisR1Stage2AdoptedReader.RawCursorAdvance
