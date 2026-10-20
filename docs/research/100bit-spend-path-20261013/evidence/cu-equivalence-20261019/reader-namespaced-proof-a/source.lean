import AspisR1CanonicalReader.Funs
import CuSavingsCanonicalInputParser
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalReader
open Aeneas Aeneas.Std Result AspisR1CanonicalReader
abbrev E := field.wide_exact.WideExact
abbrev Canonical (e : E) : Prop := CuSavingsCanonicalInputPowers.Canonical (toInput e)

private theorem bind_ok {A B : Type} (r : Result A) (k : A→Result B) (out : B)
    (h : (r >>=k)=.ok out) : ∃ value,r=.ok value ∧ k value=.ok out := by
  cases r with
  | fail e => cases h
  | div => cases h
  | ok value => exact ⟨value,rfl,h⟩

/-- The unchanged raw-byte reader is universally quantified: any success of
its exact e consumer returns a canonical value, regardless of what bytes or
cursor the raw operation produced. Its failures/divergence remain failures or
divergence, never converted into a successful read. -/
theorem e_success [Runtime] (reader finalReader : Reader) (value : E)
    (h : Reader.e reader=.ok (core.result.Result.Ok value,finalReader)) : Canonical value := by
  unfold Reader.e at h
  obtain ⟨raw,hraw,h⟩ := bind_ok _ _ _ h
  rcases raw with ⟨words,next⟩
  simp only [uncurry_apply_pair,lift,bind_tc_ok,
    field.wide_exact.WideExact.from_le_bytes,bind_assoc_eq] at h
  obtain ⟨parsed,hparsed,h⟩ := bind_ok _ _ _ h
  cases parsed with
  | none => simp [core.option.Option.ok_or,AspisR1CanonicalStd.ok_or] at h
  | some x =>
    simp only [Option.map_some,core.option.Option.ok_or,AspisR1CanonicalStd.ok_or,
      bind_tc_ok,Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at h
    rcases h with ⟨hx,hnext⟩
    subst value
    change CuSavingsCanonicalInputPowers.Canonical (toInput (fromInput x))
    rw [to_fromInput]
    exact CuSavingsCanonicalInputParser.from_bytes_success _ x hparsed

#print axioms e_success
end AspisR1.CuSavingsCanonicalReader
