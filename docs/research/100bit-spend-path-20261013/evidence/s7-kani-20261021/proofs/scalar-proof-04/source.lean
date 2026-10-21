import S7OwnedP6ScalarExtracted
import ExtractedCurrentReducer
import ExtractedCurrentCM31Mul
import AspisR1BatchedFoldSourceStep

/-! Scalar part of the P6 route, over the actual freshly emitted declaration.
The caller/raw-vector and loop simulation are separate obligations. -/
set_option autoImplicit false
namespace S7OwnedP6ScalarProof
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedCurrentReducerOps AspisR1.ExtractedCurrentReducer
open AspisV8R17.RawReducer

theorem emitted_step (raw1 : U64) (limb basis : U32) (flush : Bool)
    (product sum : U64)
    (hmul : UScalar.mul (core.convert.num.FromU64U32.from limb)
      (core.convert.num.FromU64U32.from basis) = .ok product)
    (hadd : UScalar.add raw1 product = .ok sum) :
    S7OwnedP6Scalar.residue_scalar_owned raw1 limb basis flush =
      if flush then foldExecution sum else .ok sum := by
  have hm : ((core.convert.num.FromU64U32.from limb) *
      (core.convert.num.FromU64U32.from basis) : Result U64) = .ok product := hmul
  have ha : (raw1 + product : Result U64) = .ok sum := hadd
  simp only [S7OwnedP6Scalar.residue_scalar_owned, lift, bind_tc_ok, hm, ha]
  cases flush
  · rfl
  · simp only [foldExecution, mask64, mask32]
    rfl

/-- The extracted owned scalar succeeds for every overflow-free input and
returns the existing bit-level Mersenne-fold model, with no callee premise. -/
theorem scalar_success (raw1 : U64) (limb basis : U32) (flush : Bool)
    (hbound : raw1.val + limb.val * basis.val < 2^64) :
    ∃ result : U64,
      S7OwnedP6Scalar.residue_scalar_owned raw1 limb basis flush = .ok result ∧
      result.val = if flush then foldBits (raw1.val + limb.val*basis.val)
        else raw1.val + limb.val*basis.val := by
  let a := core.convert.num.FromU64U32.from limb
  let b := core.convert.num.FromU64U32.from basis
  have ha : a.val = limb.val := AspisR1.ExtractedCurrentCM31Mul.widen_value limb
  have hb : b.val = basis.val := AspisR1.ExtractedCurrentCM31Mul.widen_value basis
  have hp : a.val * b.val < 2^64 := by rw [ha,hb]; omega
  obtain ⟨product,hmul,hpv⟩ := mul_success a b hp
  have hpv' : product.val=limb.val*basis.val := by simpa only [ha,hb] using hpv
  have hs : raw1.val + product.val < 2^64 := by rw [hpv']; exact hbound
  obtain ⟨sum,hadd,hsv⟩ := add_success raw1 product hs
  have hsv' : sum.val=raw1.val+limb.val*basis.val := by rw [hsv,hpv']
  rw [emitted_step raw1 limb basis flush product sum hmul hadd]
  cases flush with
  | false => exact ⟨sum,rfl,hsv'⟩
  | true =>
    obtain ⟨result,hr,hv⟩ := foldExecution_success sum
    exact ⟨result,hr,by simpa [hsv'] using hv⟩

/-- The transaction phase invariant supplies the scalar precondition. This
is the exact four-product bound, rather than a solver arithmetic assumption. -/
theorem phase_bound (raw1 : U64) (limb basis : U32) (phase : Nat)
    (hphase : phase < 4) (hl : limb.val < 2^31-1) (hb : basis.val < 2^31-1)
    (hr : raw1.val < 2^34 + phase * (2^31-2)^2) :
    raw1.val + limb.val * basis.val < 2^64 := by
  have hp := AspisR1BatchedFoldSourceStep.product_bound hl hb
  change limb.val * basis.val ≤ (2^31-2)^2 at hp
  have hphase' : phase ≤ 3 := by omega
  have hmul := Nat.mul_le_mul_right ((2^31-2)^2) hphase'
  omega

/-- The real phase/canonicality invariant connects the newly extracted scalar
with the existing batched source model at every symbolic transaction ordinal. -/
theorem scalar_eq_source_push (raw1 : U64) (limb basis : U32) (terms : Nat)
    (hl : limb.val < 2^31-1) (hb : basis.val < 2^31-1)
    (hr : raw1.val < 2^34 + (terms%4) * (2^31-2)^2) :
    ∃ result : U64,
      S7OwnedP6Scalar.residue_scalar_owned raw1 limb basis (decide (terms%4=3)) =
        .ok result ∧
      result.val = AspisR1BatchedFoldSourceStep.sourcePush terms raw1.val
        (limb.val*basis.val) := by
  have hbound := phase_bound raw1 limb basis (terms%4)
    (Nat.mod_lt _ (by decide)) hl hb hr
  obtain ⟨result,hrun,hvalue⟩ := scalar_success raw1 limb basis _ hbound
  refine ⟨result,hrun,?_⟩
  rw [foldBits_eq_fold31] at hvalue
  simpa only [AspisR1BatchedFoldSourceStep.sourcePush, fold31,
    AspisR1BatchedFoldSourceStep.fold, AspisR1BatchedFoldSourceStep.limbBase,
    decide_eq_true_eq] using hvalue

#print axioms scalar_eq_source_push
#print axioms emitted_step
#print axioms scalar_success
#print axioms phase_bound
end S7OwnedP6ScalarProof
