import AspisR156FullFreeze.FunsCore
import AspisV8R19.ComplexBaseExecution

/-! Canonical addition/subtraction for the selected release source.
The wide guards are discharged from actual operand bounds, without equating
the newer implementation to the older checked implementation on raw inputs. -/
set_option autoImplicit false
namespace AspisV8R19.R159WideBaseExecution
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R17.RawReducer (P)
open AspisV8R19.InverseRuntimeMul

@[simp] theorem p_val : field.P.val = P := by simp [field.P, P]

theorem add64_val (a b : U64) (h : a.val+b.val < 2^64) :
    (U64.wrapping_add a b).val = a.val+b.val := by
  rw [U64.wrapping_add_val_eq]
  simp only [UScalar.size, UScalarTy.numBits]
  exact Nat.mod_eq_of_lt h

theorem sub64_val (a b : U64) (h : b.val ≤ a.val) :
    (U64.wrapping_sub a b).val = a.val-b.val := by
  rw [U64.wrapping_sub_val_eq]
  have hb : b.val < 2^64 := b.bv.isLt
  have ha : a.val < 2^64 := a.bv.isLt
  have he : a.val + (2^64-b.val) = (a.val-b.val)+2^64 := by omega
  simp only [UScalar.size, UScalarTy.numBits]
  change (a.val+(2^64-b.val)) % 2^64 = a.val-b.val
  rw [he, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem add_success (x y : U32) (hx : x.val < P) (hy : y.val < P) :
    ∃ z : U32, field.M31.add x y = .ok z ∧
      z.val = (x.val+y.val)%P ∧ z.val < P := by
  let s := U64.wrapping_add (core.convert.num.FromU64U32.from x)
    (core.convert.num.FromU64U32.from y)
  have hv : s.val = x.val+y.val := by
    dsimp only [s]
    rw [add64_val, core.convert.num.FromU64U32.from_val_eq,
      core.convert.num.FromU64U32.from_val_eq]
    rw [core.convert.num.FromU64U32.from_val_eq,
      core.convert.num.FromU64U32.from_val_eq]
    unfold P at *; omega
  have h32 : s.val < 2^32 := by rw [hv]; unfold P at *; omega
  have hmax : ¬ s > core.convert.num.FromU64U32.from core.num.U32.MAX := by
    simp only [UScalar.lt_equiv, core.convert.num.FromU64U32.from_val_eq]
    change ¬ (4294967295 < s.val)
    omega
  by_cases h : P ≤ s.val
  · let d := U64.wrapping_sub s (core.convert.num.FromU64U32.from field.P)
    have hd : d.val = s.val-P := by
      dsimp only [d]
      rw [sub64_val, core.convert.num.FromU64U32.from_val_eq, p_val]
      simpa only [core.convert.num.FromU64U32.from_val_eq, p_val] using h
    have hc : d.val < P := by rw [hd,hv]; omega
    refine ⟨UScalar.cast .U32 d, ?_, ?_, ?_⟩
    · simp only [field.M31.add, lift, bind_tc_ok]
      change (if s > core.convert.num.FromU64U32.from core.num.U32.MAX then _ else _) = _
      simp only [hmax, if_false]
      simp only [UScalar.le_equiv, core.convert.num.FromU64U32.from_val_eq, p_val]
      change (if P ≤ s.val then _ else _) = _
      simp only [h, if_true]
      rfl
    · rw [narrow_exact d (by unfold P at hc; omega), hd, hv]
      rw [Nat.mod_eq_sub_mod (by rw [← hv]; exact h), Nat.mod_eq_of_lt (by omega)]
    · rw [narrow_exact d (by unfold P at hc; omega)]; exact hc
  · refine ⟨UScalar.cast .U32 s, ?_, ?_, ?_⟩
    · simp only [field.M31.add, lift, bind_tc_ok]
      change (if s > core.convert.num.FromU64U32.from core.num.U32.MAX then _ else _) = _
      simp only [hmax, if_false]
      simp only [UScalar.le_equiv, core.convert.num.FromU64U32.from_val_eq, p_val]
      change (if P ≤ s.val then _ else _) = _
      simp only [h, if_false]
      rfl
    · rw [narrow_exact s h32, hv, Nat.mod_eq_of_lt (by omega)]
    · rw [narrow_exact s h32]; omega

theorem sub_success (x y : U32) (hx : x.val < P) (hy : y.val < P) :
    ∃ z : U32, field.M31.sub x y = .ok z ∧
      z.val = (x.val+P-y.val)%P ∧ z.val < P := by
  let top := U64.wrapping_add (core.convert.num.FromU64U32.from x)
    (core.convert.num.FromU64U32.from field.P)
  have ht : top.val = x.val+P := by
    dsimp only [top]
    rw [add64_val, core.convert.num.FromU64U32.from_val_eq,
      core.convert.num.FromU64U32.from_val_eq, p_val]
    rw [core.convert.num.FromU64U32.from_val_eq,
      core.convert.num.FromU64U32.from_val_eq, p_val]
    unfold P at *; omega
  have ht32 : top.val < 2^32 := by rw [ht]; unfold P at *; omega
  have hmax : ¬ top > core.convert.num.FromU64U32.from core.num.U32.MAX := by
    simp only [UScalar.lt_equiv, core.convert.num.FromU64U32.from_val_eq]
    change ¬ (4294967295 < top.val); omega
  have hlow : ¬ top < core.convert.num.FromU64U32.from y := by
    simp only [UScalar.lt_equiv, core.convert.num.FromU64U32.from_val_eq]
    rw [ht]; omega
  let s := U64.wrapping_sub top (core.convert.num.FromU64U32.from y)
  have hv : s.val = x.val+P-y.val := by
    dsimp only [s]
    rw [sub64_val, core.convert.num.FromU64U32.from_val_eq, ht]
    rw [core.convert.num.FromU64U32.from_val_eq, ht]; omega
  have h32 : s.val < 2^32 := by rw [hv]; unfold P at *; omega
  have h2p : s.val < 2*P := by rw [hv]; omega
  by_cases h : P ≤ s.val
  · let d := U64.wrapping_sub s (core.convert.num.FromU64U32.from field.P)
    have hd : d.val = s.val-P := by
      dsimp only [d]
      rw [sub64_val, core.convert.num.FromU64U32.from_val_eq, p_val]
      simpa only [core.convert.num.FromU64U32.from_val_eq,p_val] using h
    have hc : d.val < P := by rw [hd]; omega
    refine ⟨UScalar.cast .U32 d, ?_, ?_, ?_⟩
    · simp only [field.M31.sub, lift, bind_tc_ok]
      change (if top > core.convert.num.FromU64U32.from core.num.U32.MAX then _ else _) = _
      simp only [hmax,if_false]
      change (if top < core.convert.num.FromU64U32.from y then _ else _) = _
      simp only [hlow,if_false]
      simp only [UScalar.le_equiv, core.convert.num.FromU64U32.from_val_eq, p_val]
      change (if P ≤ s.val then _ else _) = _
      simp only [h,if_true]
      rfl
    · rw [narrow_exact d (by unfold P at hc; omega),hd,← hv]
      rw [Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
    · rw [narrow_exact d (by unfold P at hc; omega)]; exact hc
  · refine ⟨UScalar.cast .U32 s, ?_, ?_, ?_⟩
    · simp only [field.M31.sub,lift,bind_tc_ok]
      change (if top > core.convert.num.FromU64U32.from core.num.U32.MAX then _ else _) = _
      simp only [hmax,if_false]
      change (if top < core.convert.num.FromU64U32.from y then _ else _) = _
      simp only [hlow,if_false]
      simp only [UScalar.le_equiv, core.convert.num.FromU64U32.from_val_eq, p_val]
      change (if P ≤ s.val then _ else _) = _
      simp only [h,if_false]
      rfl
    · rw [narrow_exact s h32,← hv,Nat.mod_eq_of_lt (by omega)]
    · rw [narrow_exact s h32]; omega

open AspisV8R15.ExactTowerBase (M31Exact)
open ComplexBaseExecution (encodeBase encodeBase_val encodeBase_cast eq_encodeBase)

theorem add_encode (x y : M31Exact) :
    field.M31.add (encodeBase x) (encodeBase y) = .ok (encodeBase (x+y)) := by
  obtain ⟨z,hz,hv,hc⟩ := add_success (encodeBase x) (encodeBase y)
    (ZMod.val_lt x) (ZMod.val_lt y)
  rw [hz]
  congr 1
  apply eq_encodeBase z (x+y) hc
  rw [hv,ZMod.natCast_mod,Nat.cast_add,encodeBase_cast,encodeBase_cast]

theorem sub_encode (x y : M31Exact) :
    field.M31.sub (encodeBase x) (encodeBase y) = .ok (encodeBase (x-y)) := by
  obtain ⟨z,hz,hv,hc⟩ := sub_success (encodeBase x) (encodeBase y)
    (ZMod.val_lt x) (ZMod.val_lt y)
  rw [hz]
  congr 1
  apply eq_encodeBase z (x-y) hc
  have hy : y.val < P := by simpa [AspisV8R15.ExactTowerBase.P, P] using ZMod.val_lt y
  rw [hv,ZMod.natCast_mod,encodeBase_val,encodeBase_val]
  rw [Nat.cast_sub (by omega),Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
  simp [P,M31Exact]

theorem double_encode (x : M31Exact) :
    field.M31.double (encodeBase x) = .ok (encodeBase (x+x)) := add_encode x x

#print axioms p_val
#print axioms add64_val
#print axioms sub64_val
#print axioms add_success
#print axioms sub_success
#print axioms add_encode
#print axioms sub_encode
#print axioms double_encode
end AspisV8R19.R159WideBaseExecution
