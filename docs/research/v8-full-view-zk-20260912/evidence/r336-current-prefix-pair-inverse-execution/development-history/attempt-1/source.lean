import AspisR335PrefixPairInverseRaw
import AspisV8R19.R332PrefixInitializationSelectors
import AspisV8R19.R279PrivateScalarInverse

/-! Exact second-prefix and pair-inverse fragments. Caller canonical/nonempty
conditions are explicit; zero total is preserved, not ruled out by assumption.
Full batch guards, compiler/stdlib correspondence and output setup remain open. -/
set_option autoImplicit false
namespace AspisV8R19.R336PrefixPairInverseExecution
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R332PrefixInitializationSelectors
open AspisV8R19.R329PrefixInitializationExecution
open AspisV8R19.R317SliceLastExecution
open AspisV8R19.R250PrivateBaseExecution
open AspisV8R19.R279PrivateScalarInverse
open AspisR335PrefixPairInverseRaw
noncomputable section

theorem second_prefix_eq_first (ys : Slice U32) :
    selectedPrefix1 ys = AspisR328PrefixInitializationRaw.selectedPrefix0 ys := by
  rfl

theorem second_prefix_empty (ys : Slice U32) (hy : ys.val.length = 0) :
    selectedPrefix1 ys = .fail .arrayOutOfBounds := by
  rw [second_prefix_eq_first]
  exact selectedPrefix0_empty ys hy

theorem second_prefix_bundle (ys : Slice U32) (g : Nat → M31Exact)
    (hy : 0 < ys.val.length)
    (hg : ∀ j, j < ys.val.length → ys.val[j]? = some (encodeBase (g j))) :
    ∃ py : alloc.vec.Vec U32,
      py.val.length = ys.val.length ∧
      (∀ j, j < ys.val.length →
        py.val[j]? = some (encodeBase (sourcePrefixValue g j))) ∧
      py.val.getLast? = some (encodeBase (sourcePrefixValue g (ys.val.length - 1))) ∧
      selectedPrefix1 ys = .ok py := by
  rw [second_prefix_eq_first]
  exact selected_prefix_initialization_bundle ys g hy hg

theorem pair_inverse_complete (px py : alloc.vec.Vec U32) (p q : M31Exact)
    (hp : px.val.getLast? = some (encodeBase p))
    (hq : py.val.getLast? = some (encodeBase q)) :
    selectedPairInverse px py =
      if p * q = 0 then .fail .assertionFailure
      else .ok (encodeBase ((p * q)⁻¹ * q), encodeBase ((p * q)⁻¹ * p)) := by
  unfold selectedPairInverse
  rw [last_complete]
  change (do
    let a ← Result.ok px.val.getLast?
    let p ← core.option.Option.unwrap a
    let b ← AspisR316SliceLastRaw.core.slice.Slice.last (alloc.vec.Vec.deref py)
    let q ← core.option.Option.unwrap b
    let c ← AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B.mul p q
    let t ← AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.inv c
    let ix ← AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B.mul t q
    let iy ← AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B.mul t p
    Result.ok (ix,iy)) = _
  rw [hp]
  simp only [bind_tc_ok, core.option.Option.unwrap]
  rw [last_complete]
  change (do
    let a ← Result.ok py.val.getLast?
    let q ← core.option.Option.unwrap a
    let c ← AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B.mul (encodeBase p) q
    let t ← AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.inv c
    let ix ← AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B.mul t q
    let iy ← AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B.mul t (encodeBase p)
    Result.ok (ix,iy)) = _
  rw [hq]
  simp only [bind_tc_ok, core.option.Option.unwrap]
  rw [mul_encoded]
  simp only [bind_tc_ok]
  by_cases hz : p * q = 0
  · rw [if_pos hz, hz, b_inv_zero]
    simp only [bind_tc_fail]
  · rw [if_neg hz, b_inv_encode (p * q) hz]
    simp only [bind_tc_ok, mul_encoded]

theorem initialized_pair_inverse (xs ys : Slice U32) (f g : Nat → M31Exact)
    (hx : 0 < xs.val.length) (hy : 0 < ys.val.length)
    (hf : ∀ j, j < xs.val.length → xs.val[j]? = some (encodeBase (f j)))
    (hg : ∀ j, j < ys.val.length → ys.val[j]? = some (encodeBase (g j))) :
    ∃ px py : alloc.vec.Vec U32,
      AspisR328PrefixInitializationRaw.selectedPrefix0 xs = .ok px ∧
      selectedPrefix1 ys = .ok py ∧
      selectedPairInverse px py =
        if sourcePrefixValue f (xs.val.length - 1) *
            sourcePrefixValue g (ys.val.length - 1) = 0 then .fail .assertionFailure
        else .ok
          (encodeBase ((sourcePrefixValue f (xs.val.length - 1) *
             sourcePrefixValue g (ys.val.length - 1))⁻¹ *
             sourcePrefixValue g (ys.val.length - 1)),
           encodeBase ((sourcePrefixValue f (xs.val.length - 1) *
             sourcePrefixValue g (ys.val.length - 1))⁻¹ *
             sourcePrefixValue f (xs.val.length - 1))) := by
  obtain ⟨px, _, _, hpx, hsx⟩ := selected_prefix_initialization_bundle xs f hx hf
  obtain ⟨py, _, _, hpy, hsy⟩ := second_prefix_bundle ys g hy hg
  exact ⟨px, py, hsx, hsy, pair_inverse_complete px py _ _ hpx hpy⟩

#print axioms second_prefix_eq_first
#print axioms second_prefix_empty
#print axioms second_prefix_bundle
#print axioms pair_inverse_complete
#print axioms initialized_pair_inverse
end
end AspisV8R19.R336PrefixPairInverseExecution
