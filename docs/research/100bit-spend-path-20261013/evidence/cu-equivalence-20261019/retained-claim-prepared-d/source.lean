import CuSavingsRetainedClaimBinding
import CuSavingsRetainedCompositionTx1Source
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedClaimBindingPrepared
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRetainedClaimBinding CuSavingsRetainedSamplerBinding
variable [AspisR1CanonicalDots.Shared] [AspisR1RetainedClaimBinding.Trace]
  [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
  [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]
abbrev Selector := ∀ {H : Type}, r1_semantic.Verified H→Slice U8→Usize→AspisR1CanonicalDots.VectorCommon
@[reducible] def binding (isNew : Bool) (select : Selector) (common : PreparedCommon) : PreparedCommon :=
  {CuSavingsRetainedSamplerBinding.binding common with
    claim := fun _ sem y1 inactive g kappa=>body isNew (select sem y1) inactive g kappa}

private theorem bind_ext {A B : Type} (m : Result A) (f g : A→Result B)
    (h : ∀ x,f x=g x) : (m >>= f)=(m >>= g) := by
  cases m with | fail e=>rfl | div=>rfl | ok x=>exact h x

/-- Complete actual emitted preparation, with fixed source claim context and
actual sampler/powers. The gamma origin is derived at the actual sample bind. -/
theorem prepared_equivalence {H : Type} (common : PreparedCommon) (select : Selector)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (initial : Array R.E 29#usize) :
    (@gamma_new.Prepared.gamma_new_new (binding true select common) _ H D sem v hash initial)=
      (@gamma_new.Prepared.gamma_new_new (binding false select common) _ H D sem v hash initial) := by
  unfold gamma_new.Prepared.gamma_new_new
  simp only [gamma_new.prepared_claim,binding,CuSavingsRetainedSamplerBinding.binding]
  apply bind_ext
  intro state
  apply bind_ext
  intro t
  apply (bind_eq_iff _ _ _).mpr
  rintro ⟨gamma,t1⟩ hgamma
  have origin := (scalar_origins D t t1 27#u8 v.y1 true gamma hgamma).1
  simp only [uncurry_apply_pair]
  apply bind_ext
  intro inactiveBytes
  simp only [lift,bind_tc_ok]
  apply bind_ext
  rintro ⟨kappa,t2⟩
  simp only [uncurry_apply_pair]
  apply bind_ext
  rintro ⟨alpha0,t3⟩
  simp only [uncurry_apply_pair]
  apply bind_ext
  intro folds
  split
  · apply bind_ext
    intro capacity
    apply bind_ext
    intro root
    try simp only [lift,bind_tc_ok]
    apply bind_ext
    intro bytes1
    apply bind_ext
    intro bytes2
    apply bind_ext
    rintro ⟨alpha1,t4⟩
    simp only [uncurry_apply_pair]
    apply bind_ext
    rintro ⟨r,t5⟩
    simp only [uncurry_apply_pair]
    cases r with
    | Err e=>rfl
    | Ok queries=>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply bind_ext
      intro row
      try simp only [lift,bind_tc_ok]
      apply bind_ext
      rintro ⟨rho,t6⟩
      simp only [uncurry_apply_pair]
      apply (bind_eq_iff _ _ _).mpr
      intro g hg
      obtain ⟨source,hs,heq⟩ := powers_source 29#usize gamma g hg
      rw [heq]
      change (body true (select sem v.y1) v.inactive (table source) kappa >>= _) =
        (body false (select sem v.y1) v.inactive (table source) kappa >>= _)
      rw [body_equivalence (select sem v.y1) v.inactive kappa (input gamma) origin source hs]
  · apply bind_ext
    rintro ⟨r,t4⟩
    simp only [uncurry_apply_pair]
    cases r with
    | Err e=>rfl
    | Ok queries=>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply bind_ext
      intro row
      try simp only [lift,bind_tc_ok]
      apply bind_ext
      rintro ⟨rho,t5⟩
      simp only [uncurry_apply_pair]
      apply (bind_eq_iff _ _ _).mpr
      intro g hg
      obtain ⟨source,hs,heq⟩ := powers_source 29#usize gamma g hg
      rw [heq]
      change (body true (select sem v.y1) v.inactive (table source) kappa >>= _) =
        (body false (select sem v.y1) v.inactive (table source) kappa >>= _)
      rw [body_equivalence (select sem v.y1) v.inactive kappa (input gamma) origin source hs]

#print axioms prepared_equivalence
end AspisR1.CuSavingsRetainedClaimBindingPrepared
