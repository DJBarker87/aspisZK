import Stage2ReaderExplicitDecoders
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2AdoptedReader.ReaderSuccess
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem raw_cursor (d : ReaderDecoders) (n : Usize) (r r' : verifier.Reader) (bytes : Array U8 n)
    (h : verifier.Reader.raw d n r = ok (bytes,r')) :
    r'.bytes = r.bytes ∧ (r.«at» + n) = ok r'.«at» := by
  unfold verifier.Reader.raw at h
  obtain ⟨i, hi, h⟩ := bind_success _ _ _ h
  obtain ⟨sl, _, h⟩ := bind_success _ _ _ h
  obtain ⟨res, _, h⟩ := bind_success _ _ _ h
  obtain ⟨arr, _, h⟩ := bind_success _ _ _ h
  have he : arr = bytes ∧ { r with «at» := i } = r' := by
    simpa only [Result.ok.injEq, Prod.mk.injEq] using h
  rcases he with ⟨_, he⟩
  cases he
  exact ⟨rfl, hi⟩

theorem wide_success (d : ReaderDecoders) (r r' : verifier.Reader)
    (value : aspis_core.field.WideExact)
    (h : verifier.Reader.e d r = ok (.Ok value,r')) :
    ∃ bytes : Array U8 32#usize,
      verifier.Reader.raw d 32#usize r = ok (bytes,r') ∧
      d.wide bytes.to_slice = ok (some value) ∧
      r'.bytes = r.bytes ∧ (r.«at» + 32#usize) = ok r'.«at» := by
  unfold verifier.Reader.e at h
  obtain ⟨pair, hp, h⟩ := bind_success _ _ _ h
  rcases pair with ⟨bytes, rr⟩
  simp only [lift, bind_tc_ok] at h
  obtain ⟨o, ho, h⟩ := bind_success _ _ _ h
  cases o with
  | none => simp only [core.option.Option.ok_or, bind_tc_ok] at h; cases h
  | some v =>
    simp only [core.option.Option.ok_or, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq,
      core.result.Result.Ok.injEq] at h
    obtain ⟨hv, hr⟩ := h
    subst v; subst rr
    exact ⟨bytes,hp,ho,raw_cursor d _ _ _ _ hp⟩

theorem qm_success (d : ReaderDecoders) (r r' : verifier.Reader)
    (value : aspis_core.field.QM31)
    (h : verifier.Reader.k d r = ok (.Ok value,r')) :
    ∃ bytes : Array U8 16#usize,
      verifier.Reader.raw d 16#usize r = ok (bytes,r') ∧
      d.qm bytes.to_slice = ok (some value) ∧
      r'.bytes = r.bytes ∧ (r.«at» + 16#usize) = ok r'.«at» := by
  unfold verifier.Reader.k at h
  obtain ⟨pair, hp, h⟩ := bind_success _ _ _ h
  rcases pair with ⟨bytes, rr⟩
  simp only [lift, bind_tc_ok] at h
  obtain ⟨o, ho, h⟩ := bind_success _ _ _ h
  cases o with
  | none => simp only [core.option.Option.ok_or, bind_tc_ok] at h; cases h
  | some v =>
    simp only [core.option.Option.ok_or, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq,
      core.result.Result.Ok.injEq] at h
    obtain ⟨hv, hr⟩ := h
    subst v; subst rr
    exact ⟨bytes,hp,ho,raw_cursor d _ _ _ _ hp⟩
#print axioms raw_cursor
#print axioms wide_success
#print axioms qm_success
end AspisR1Stage2AdoptedReader.ReaderSuccess
