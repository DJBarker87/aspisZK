import R0Z.PayloadSplit
import R0Z.HelperInvariant

/-! Joint trace affinity, using the proved invariance of the honest H1 helper.
Neither its reciprocals nor any literal registry are normalized here. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.JointTrace
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.PayloadSplit
attribute [local instance] Classical.propDecidable
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows
variable {K : Type} [Field K] {F : Subfield K}

/-- Generic finite-set balancing; the set stays abstract in its evaluation proof. -/
def balanceLinear {V : Type} [AddCommGroup V] [Module F V]
    (S : Finset (Fin 1024)) (d : Fin 1024) (f : Fin 1024 → V →ₗ[F] K)
    (r : Fin 1024) : V →ₗ[F] K := if r = d then -(∑ s ∈ S, f s) else f r

theorem balanceLinear_apply {V : Type} [AddCommGroup V] [Module F V]
    (S : Finset (Fin 1024)) (d : Fin 1024) (f : Fin 1024 → V →ₗ[F] K)
    (r : Fin 1024) (v : V) : balanceLinear S d f r v =
      if r = d then -(∑ s ∈ S, f s v) else f r v := by
  unfold balanceLinear
  split_ifs <;> simp only [LinearMap.neg_apply, LinearMap.sum_apply]

theorem balance_add_generic (S : Finset (Fin 1024)) (d r : Fin 1024)
    (u v : Fin 1024 → K) :
    (if r = d then -(∑ s ∈ S, (u s + v s)) else u r + v r) =
      (if r = d then -(∑ s ∈ S, u s) else u r) +
      (if r = d then -(∑ s ∈ S, v s) else v r) := by
  split_ifs <;> simp only [Finset.sum_add_distrib, neg_add]

def noiseRead (c : Fin 29) (r : Fin 1024) : EligibleNoise K F →ₗ[F] K :=
  if h : eligible c r then
    { toFun := fun e => e ⟨(c,r),h⟩
      map_add' := fun _ _ => by simp
      map_smul' := fun a e => by
        change ((a * e ⟨(c,r),h⟩ : F) : K) = (a : K) * (e ⟨(c,r),h⟩ : K)
        exact map_mul F.subtype _ _ }
  else 0

theorem noiseRead_apply (c : Fin 29) (r : Fin 1024) (e : EligibleNoise K F) :
    noiseRead c r e = semanticNoise (Sum.elim e 0) c r := by
  unfold noiseRead semanticNoise
  split_ifs <;> rfl

def eligibleLinear : EligibleNoise K F →ₗ[F] Trace K :=
  LinearMap.pi fun c => LinearMap.pi fun r => if c.val < 16 then
    balanceLinear (copyInactiveRows.erase 1023) 1023 (noiseRead c) r else 0

theorem eligibleLinear_apply (e : EligibleNoise K F) (c : Fin 29) (r : Fin 1024) :
    eligibleLinear e c r = if c.val < 16 then
      balance 1023 (fun s => semanticNoise (Sum.elim e 0) c s) r else 0 := by
  simp only [eligibleLinear, LinearMap.pi_apply]
  split_ifs <;> simp only [balanceLinear_apply, noiseRead_apply, balance, LinearMap.zero_apply]

theorem applyEligible_add (t : Trace K) (e : EligibleNoise K F) :
    applyEligible t e = applyEligible (F := F) t 0 + eligibleLinear e := by
  have hz (c : Fin 29) (r : Fin 1024) :
      semanticNoise (Sum.elim (0 : EligibleNoise K F) 0) c r = 0 := by
    unfold semanticNoise
    split_ifs <;> rfl
  funext c r
  simp only [applyEligible, Pi.add_apply, eligibleLinear_apply, hz, add_zero]
  by_cases hc : c.val < 16
  · simp only [if_pos hc, balance]
    exact balance_add_generic _ _ _ _ _
  · simp only [if_neg hc, add_zero]

/-- Prepared and retained base trace is affine in eligible noise; H1 is
constant because its Boolean-row endpoint tuples are protected. -/
theorem prepared_add (pub : Public K) (t : Trace K) (ch : Challenges K)
    (e : EligibleNoise K F) :
    traceBase (prepare pub (applyEligible t e) ch) =
      traceBase (prepare pub (applyEligible (F := F) t 0) ch) + eligibleLinear e := by
  have he := applyEligible_add t e
  funext c r
  by_cases hc : c.val < 16
  · have h26 : ¬c.val = 26 := by omega
    simpa only [traceBase, hc, true_or, if_true, prepare, if_neg h26, Pi.add_apply]
      using congrFun (congrFun he c) r
  · by_cases h26 : c.val = 26
    · simp only [traceBase, if_pos (Or.inr h26), prepare, if_pos h26,
        HelperInvariant.helper_eligible, Pi.add_apply, eligibleLinear_apply, if_neg hc, add_zero]
    · simp only [traceBase, hc, h26, or_self, if_false, Pi.add_apply,
        eligibleLinear_apply, if_neg hc, add_zero]

def tapeLinear (B : PackBasis F) : T K F →ₗ[F] Trace K :=
  eligibleLinear.comp ((LinearMap.snd F _ _).comp (LinearMap.snd F _ _)) +
    (traceLinear B).comp aff

theorem actual_affine (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : T K F) :
    actual pub B t ch r = actual pub B t ch 0 + tapeLinear B r := by
  simp only [actual, applyAff_eq_base_add, map_zero, add_zero, tapeLinear,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.snd_apply]
  rw [prepared_add, add_assoc]
  rfl

theorem tapeLinear_pure (B : PackBasis F) (m : M K F) :
    tapeLinear B (m,0) = pureTrace B m := by
  simp only [tapeLinear, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.snd_apply, map_zero, zero_add]
  rfl

#print axioms prepared_add
#print axioms actual_affine
end R0Z.JointTrace
