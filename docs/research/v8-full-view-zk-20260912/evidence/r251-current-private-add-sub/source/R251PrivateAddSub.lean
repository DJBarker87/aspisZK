import AspisV8R19.R250PrivateBaseExecution
import AspisV8R19.R158WordBounds

/-! Canonical execution for the private R110 scalar addition and subtraction
leaves, plus their transport to exact M31 addition and subtraction. -/
set_option autoImplicit false
namespace AspisV8R19.R251PrivateAddSub
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase (M31Exact P)
open AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm (B P110)
open ComplexBaseExecution (encodeBase encodeBase_val encodeBase_cast eq_encodeBase)
noncomputable section

theorem b_add_canonical (a b : U32) (ha : a.val < P) (hb : b.val < P) :
    ∃ z : U32, B.add a b = .ok z ∧
      z.val = (a.val + b.val) % P ∧ z.val < P := by
  let s := U32.wrapping_add a b
  have hsum : a.val + b.val < 2^32 := by
    unfold P at *
    omega
  have hs : s.val = a.val + b.val := by
    dsimp only [s]
    rw [U32.wrapping_add_val_eq]
    simp only [UScalar.size, UScalarTy.numBits]
    exact Nat.mod_eq_of_lt hsum
  have h2p : s.val < 2 * AspisV8R17.RawReducer.P := by
    rw [hs]
    unfold P AspisV8R17.RawReducer.P at *
    omega
  obtain ⟨z, hz, hzv, hzc⟩ :=
    AspisV8R19.R161WrappedMulExecution.finish32_success s h2p
  have hpw : P110 = AspisR156FullFreeze.aspis_core.field.P := by
    apply UScalar.eq_of_val_eq
    simp [AspisV8R19.R250PrivateBaseExecution.p110_val,
      AspisR156FullFreeze.aspis_core.field.P, P]
  have heq : B.add a b = AspisV8R19.R161WrappedMulExecution.finish32 s := by
    simp only [B.add, AspisV8R19.R161WrappedMulExecution.finish32,
      lift, bind_tc_ok]
    rw [hpw]
    simp only [UScalar.le_equiv, AspisV8R19.R159WideBaseExecution.p_val]
    rfl
  have hzv' : z.val = (a.val + b.val) % P := by
    rw [hs, show AspisV8R17.RawReducer.P = P by rfl] at hzv
    exact hzv
  refine ⟨z, ?_, hzv', hzc⟩
  rw [heq]
  exact hz

theorem b_sub_canonical (a b : U32) (ha : a.val < P) (hb : b.val < P) :
    ∃ z : U32, B.sub a b = .ok z ∧
      z.val = (a.val + P - b.val) % P ∧ z.val < P := by
  let top := U32.wrapping_add a AspisR156FullFreeze.aspis_core.field.P
  have htop : top.val = a.val + P := by
    dsimp only [top]
    rw [U32.wrapping_add_val_eq]
    simp only [UScalar.size, UScalarTy.numBits,
      AspisV8R19.R159WideBaseExecution.p_val]
    exact Nat.mod_eq_of_lt (by unfold P AspisV8R17.RawReducer.P at *; omega)
  have hge : b.val ≤ top.val := by rw [htop]; unfold P at *; omega
  obtain ⟨d, hd, hdv⟩ :=
    AspisV8R19.InverseRuntimeMul.sub_success top b hge
  have hw := AspisV8R19.R158WordBounds.checked_sub_eq_wrapping top b hge
  have hdeq : d = U32.wrapping_sub top b := Result.ok.inj (hd.symm.trans hw)
  let s := U32.wrapping_sub top b
  have hs : s.val = a.val + P - b.val := by
    dsimp only [s]
    rw [← hdeq, hdv, htop]
  have h2p : s.val < 2 * AspisV8R17.RawReducer.P := by
    rw [hs]
    unfold P AspisV8R17.RawReducer.P at *
    omega
  obtain ⟨z, hz, hzv, hzc⟩ :=
    AspisV8R19.R161WrappedMulExecution.finish32_success s h2p
  have hpw : P110 = AspisR156FullFreeze.aspis_core.field.P := by
    apply UScalar.eq_of_val_eq
    simp [AspisV8R19.R250PrivateBaseExecution.p110_val,
      AspisR156FullFreeze.aspis_core.field.P, P]
  have heq : B.sub a b = AspisV8R19.R161WrappedMulExecution.finish32 s := by
    rw [R250PrivateBaseExecution.sub_raw]
    simp only [AspisR156FullFreeze.aspis_core.field.r91_raw_sub,
      AspisV8R19.R161WrappedMulExecution.finish32,lift,bind_tc_ok]
    simp only [UScalar.le_equiv,AspisV8R19.R159WideBaseExecution.p_val]
    rfl
  have hzv' : z.val = (a.val + P - b.val) % P := by
    rw [hs, show AspisV8R17.RawReducer.P = P by rfl] at hzv
    exact hzv
  refine ⟨z, ?_, hzv', hzc⟩
  rw [heq]
  exact hz

theorem b_add_encode (x y : M31Exact) :
    B.add (encodeBase x) (encodeBase y) = .ok (encodeBase (x + y)) := by
  have hx : (encodeBase x).val < P := by
    simpa only [encodeBase_val] using (ZMod.val_lt x)
  have hy : (encodeBase y).val < P := by
    simpa only [encodeBase_val] using (ZMod.val_lt y)
  obtain ⟨z, hz, hzv, hzc⟩ := b_add_canonical (encodeBase x) (encodeBase y) hx hy
  rw [hz]
  congr 1
  apply eq_encodeBase z (x + y) hzc
  rw [hzv, ZMod.natCast_mod, Nat.cast_add, encodeBase_cast, encodeBase_cast]

theorem b_sub_encode (x y : M31Exact) :
    B.sub (encodeBase x) (encodeBase y) = .ok (encodeBase (x - y)) := by
  have hx : (encodeBase x).val < P := by
    simpa only [encodeBase_val] using (ZMod.val_lt x)
  have hy : (encodeBase y).val < P := by
    simpa only [encodeBase_val] using (ZMod.val_lt y)
  obtain ⟨z, hz, hzv, hzc⟩ := b_sub_canonical (encodeBase x) (encodeBase y) hx hy
  rw [hz]
  congr 1
  apply eq_encodeBase z (x - y) hzc
  rw [hzv, ZMod.natCast_mod, encodeBase_val, encodeBase_val]
  have hyv : y.val < P := ZMod.val_lt y
  rw [Nat.cast_sub (by omega), Nat.cast_add,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  simp [P, M31Exact]

#print axioms b_add_canonical
#print axioms b_sub_canonical
#print axioms b_add_encode
#print axioms b_sub_encode
end
end AspisV8R19.R251PrivateAddSub
