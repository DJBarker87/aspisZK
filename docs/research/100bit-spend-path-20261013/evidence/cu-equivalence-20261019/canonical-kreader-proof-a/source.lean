import AspisR1CanonicalKReader.Funs
import CuSavingsRhoParserCanonicality
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalKReader
open Aeneas Aeneas.Std Result AspisR1CanonicalKReader
abbrev E := field.QM31
def Canonical (e : E) : Prop :=
  e.c0.a.val<2147483647 ∧ e.c0.b.val<2147483647 ∧ e.c1.a.val<2147483647 ∧ e.c1.b.val<2147483647

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
theorem k_success [Runtime] (reader finalReader : Reader) (value : E)
    (h : Reader.k reader=.ok (core.result.Result.Ok value,finalReader)) : Canonical value := by
  unfold Reader.k at h
  obtain ⟨raw,hraw,h⟩ := bind_ok _ _ _ h
  rcases raw with ⟨words,next⟩
  simp only [uncurry_apply_pair,lift,bind_tc_ok,
    field.QM31.from_le_bytes,bind_assoc_eq] at h
  obtain ⟨parsed,hparsed,h⟩ := bind_ok _ _ _ h
  cases parsed with
  | none => simp [core.option.Option.ok_or,AspisR1CanonicalStd.ok_or] at h
  | some x =>
    simp only [Option.map_some,core.option.Option.ok_or,AspisR1CanonicalStd.ok_or,
      bind_tc_ok,Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at h
    rcases h with ⟨hx,hnext⟩
    subst value
    have hc := CuSavingsRhoParserCanonicality.qm31_from_le_bytes_success_canonical _ x hparsed
    simpa only [Canonical,fromRho,AspisR1CuRho.field.P] using hc


#print axioms k_success
end AspisR1.CuSavingsCanonicalKReader
