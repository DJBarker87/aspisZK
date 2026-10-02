import AspisV8R19.R353AfterGuardsCriterion
import AspisV8R19.R354ReverseInverseModel

/-! Mathematical output entries of the exact selected after-guards execution.
These statements do not prove the enclosing source guards or independent
Rust-standard-library/compiler correspondence. -/
set_option autoImplicit false
namespace AspisV8R19.R355AfterGuardsInverseValues
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R332PrefixInitializationSelectors
open AspisV8R19.R341PrefixNonzero
open AspisV8R19.R311BatchReverseLoopExecution
open AspisV8R19.R342OutputSetup
open AspisV8R19.R350AfterGuardsExecution
open AspisV8R19.R353AfterGuardsCriterion
open AspisV8R19.R354ReverseInverseModel
open AspisR346AfterGuardsRaw (selectedAfterGuards)
noncomputable section

theorem sourceOutput_length (xs : Slice U32) (f : Nat → M31Exact) (x : M31Exact) :
    (sourceOutput xs f x).val.length = xs.val.length := by
  unfold sourceOutput
  change (setNat (reverseModel f (sourcePrefixValue f) (xs.val.length - 1)
    x (zeroVec xs)).2 0 _).length = _
  rw [setNat_length]
  exact (reverseModel_output_length _ _ _ _ _).trans (zeroVec_length xs)

theorem after_guards_nonzero_inverse_outputs
    (xs ys : Slice U32) (f g : Nat → M31Exact)
    (hx : 0 < xs.val.length) (hy : 0 < ys.val.length)
    (hf : ∀ j, j < xs.val.length → xs.val[j]? = some (encodeBase (f j)))
    (hg : ∀ j, j < ys.val.length → ys.val[j]? = some (encodeBase (g j)))
    (hnf : ∀ j, j < xs.val.length → f j ≠ 0)
    (hng : ∀ j, j < ys.val.length → g j ≠ 0) :
    selectedAfterGuards xs ys = .ok (core.result.Result.Ok
      (sourceOutput xs f (sourcePrefixValue f (xs.val.length - 1))⁻¹,
       sourceOutput ys g (sourcePrefixValue g (ys.val.length - 1))⁻¹)) := by
  have ht := (initialized_pair_total_ne_zero_iff f g
    xs.val.length ys.val.length hx hy).mpr ⟨hnf, hng⟩
  obtain ⟨hp, hq⟩ := mul_ne_zero_iff.mp ht
  have hyseed : (sourcePrefixValue f (xs.val.length - 1) *
      sourcePrefixValue g (ys.val.length - 1))⁻¹ *
      sourcePrefixValue f (xs.val.length - 1) =
      (sourcePrefixValue g (ys.val.length - 1))⁻¹ := by
    rw [mul_comm (sourcePrefixValue f (xs.val.length - 1))
      (sourcePrefixValue g (ys.val.length - 1))]
    exact product_inverse_times_right _ _ hp
  have hrun := after_guards_complete xs ys f g hx hy hf hg
  simpa only [if_neg ht, product_inverse_times_right _ _ hq, hyseed] using hrun

/-- On actual suffix success, nonzero inputs and every inverse output read are
derived, without a caller-supplied nonzero or output-length premise. -/
theorem after_guards_success_inverse_bundle
    (xs ys : Slice U32) (f g : Nat → M31Exact)
    (hx : 0 < xs.val.length) (hy : 0 < ys.val.length)
    (hf : ∀ j, j < xs.val.length → xs.val[j]? = some (encodeBase (f j)))
    (hg : ∀ j, j < ys.val.length → ys.val[j]? = some (encodeBase (g j)))
    (ox oy : VecU32)
    (hok : selectedAfterGuards xs ys = .ok (core.result.Result.Ok (ox, oy))) :
    ox.val.length = xs.val.length ∧ oy.val.length = ys.val.length ∧
    (∀ j, j < xs.val.length → ox.val[j]? = some (encodeBase (f j)⁻¹)) ∧
    (∀ j, j < ys.val.length → oy.val[j]? = some (encodeBase (g j)⁻¹)) ∧
    (∀ j, j < xs.val.length → f j ≠ 0) ∧
    (∀ j, j < ys.val.length → g j ≠ 0) := by
  obtain ⟨hnf, hng⟩ := (after_guards_succeeds_iff xs ys f g hx hy hf hg).mp
    ⟨ox, oy, hok⟩
  have hrun := after_guards_nonzero_inverse_outputs xs ys f g hx hy hf hg hnf hng
  have heq := hok.symm.trans hrun
  have hpair := core.result.Result.Ok.inj (Result.ok.inj heq)
  obtain ⟨hox, hoy⟩ := Prod.mk.inj hpair
  subst ox
  subst oy
  exact ⟨sourceOutput_length xs f _, sourceOutput_length ys g _,
    sourceOutput_inverse_read xs f hx hnf, sourceOutput_inverse_read ys g hy hng,
    hnf, hng⟩

#print axioms sourceOutput_length
#print axioms after_guards_nonzero_inverse_outputs
#print axioms after_guards_success_inverse_bundle
end
end AspisV8R19.R355AfterGuardsInverseValues
