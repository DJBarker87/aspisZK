import AspisR1RhoPrepared.FunsExternal
import CuSavingsRhoScalarK
import CuSavingsRhoPowerTail

/-! The actual preparation scalar call is bound to the checked source sampler,
not to an assumed canonical callback. Nominal QM31 transport is invertible;
the original transcript and Digest32 carriers are shared without conversion. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoPreparedScalar
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem to_from (q : AspisR1CuRho.field.QM31) : toRhoSource (fromRhoSource q) = q := rfl

theorem from_to (q : aspis_core.field.QM31) : fromRhoSource (toRhoSource q) = q := rfl

theorem canonical_source (q : AspisR1CuRho.field.QM31)
    (h : CuSavingsRhoInitRow.Canonical q) :
    CuSavingsRhoPowerTail.Canonical (fromRhoSource q) :=
  ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩

variable [AspisR1CuRho.ScalarKBlocks]

theorem scalar_success {H : Type} (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (q : aspis_core.field.QM31)
    (h : transcript.Transcript.scalar_k D self row payload = .ok (q,after)) :
    CuSavingsRhoPowerTail.Canonical q ∧ ∃ source,
      AspisR1CuRho.transcript.Transcript.scalar_k D self row payload = .ok (source,after) ∧
      fromRhoSource source=q := by
  unfold transcript.Transcript.scalar_k at h
  obtain ⟨⟨source,last⟩,hs,h⟩ := bind_ok _ _ _ h
  simp only [uncurry_apply_pair] at h
  have heq := Result.ok.inj h
  have hq : fromRhoSource source=q := congrArg Prod.fst heq
  have ht : last=after := congrArg Prod.snd heq
  have hc := (CuSavingsRhoScalarK.source_success D self last row payload source hs).1
  refine ⟨?_,source,?_,hq⟩
  · rw [← hq]
    exact canonical_source source hc
  · simpa only [ht] using hs

#print axioms to_from
#print axioms from_to
#print axioms canonical_source
#print axioms scalar_success
end AspisR1.CuSavingsRhoPreparedScalar
