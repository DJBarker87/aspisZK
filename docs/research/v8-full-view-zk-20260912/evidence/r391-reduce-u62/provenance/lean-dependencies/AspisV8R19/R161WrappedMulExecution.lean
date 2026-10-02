import AspisV8R19.R159WideBaseExecution
import AspisV8R19.R158WordBounds
import AspisV8R19.CanonicalProduct

/-! Exact release-mode M31 multiplication/reduction for all raw U32 inputs.
The symbolic fold bounds prove wrapping arithmetic agrees with the retained
checked execution. The full square loop and inverse result are transported
only after that equality has been proved. -/
set_option autoImplicit false
namespace AspisV8R19.R161WrappedMulExecution
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R17.RawReducer
open InverseRuntimeMul R159WideBaseExecution

theorem shift31_val (x : U64) :
    (U64.wrapping_shr x 31#u32).val = x.val >>> 31 := R158WordBounds.wrapping_shr31_value x

def wrappedFold (x : U64) : U64 :=
  U64.wrapping_add (UScalar.and x (UScalar.cast .U64 field.P))
    (U64.wrapping_shr x 31#u32)

theorem wrappedFold_val (x : U64) : (wrappedFold x).val = foldBits x.val := by
  have hm : (UScalar.and x (UScalar.cast .U64 field.P)).val = x.val &&& P := by
    rw [and_value,cast_widen_value,p_val]
  have hbound := first_fold_lt x.val x.bv.isLt
  have hs : (UScalar.and x (UScalar.cast .U64 field.P)).val +
      (U64.wrapping_shr x 31#u32).val < 2^64 := by
    rw [hm,shift31_val]
    unfold foldBits at hbound
    omega
  unfold wrappedFold
  rw [add64_val _ _ hs,hm,shift31_val]
  rfl

def finish64 (s : U64) : Result U32 :=
  if P ≤ s.val then .ok (UScalar.cast .U32
    (U64.wrapping_sub s (UScalar.cast .U64 field.P)))
  else .ok (UScalar.cast .U32 s)

theorem finish64_success (s : U64) (hs : s.val < 2*P) :
    ∃ z : U32, finish64 s = .ok z ∧ z.val = s.val%P ∧ z.val < P := by
  by_cases h : P ≤ s.val
  · let d := U64.wrapping_sub s (UScalar.cast .U64 field.P)
    have hv : d.val = s.val-P := by
      dsimp only [d]
      rw [sub64_val,cast_widen_value,p_val]
      simpa only [cast_widen_value,p_val] using h
    have hc : d.val < P := by rw [hv]; omega
    have hn : d.val < 2^32 := by unfold P at hc; omega
    refine ⟨UScalar.cast .U32 d, ?_, ?_, ?_⟩
    · simp only [finish64,h,if_true]; rfl
    · rw [narrow_exact d hn,hv,Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
    · rw [narrow_exact d hn]; exact hc
  · have hn : s.val < 2^32 := by unfold P at *; omega
    refine ⟨UScalar.cast .U32 s, ?_, ?_, ?_⟩
    · simp only [finish64,h,if_false]
    · rw [narrow_exact s hn,Nat.mod_eq_of_lt (by omega)]
    · rw [narrow_exact s hn]; omega

def finish32 (s : U32) : Result U32 :=
  if P ≤ s.val then .ok (U32.wrapping_sub s field.P) else .ok s

theorem finish32_success (s : U32) (hs : s.val < 2*P) :
    ∃ z : U32, finish32 s = .ok z ∧ z.val = s.val%P ∧ z.val < P := by
  by_cases h : P ≤ s.val
  · have hb : field.P.val ≤ s.val := by simpa only [p_val] using h
    obtain ⟨z,hz,hv⟩ := InverseRuntimeMul.sub_success s field.P hb
    have hw := R158WordBounds.checked_sub_eq_wrapping s field.P hb
    have he : z = U32.wrapping_sub s field.P := Result.ok.inj (hz.symm.trans hw)
    refine ⟨z, ?_, ?_, ?_⟩
    · simp only [finish32,h,if_true,← he]
    · rw [hv,p_val,Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
    · rw [hv,p_val]; omega
  · refine ⟨s, ?_, ?_, by omega⟩
    · simp only [finish32,h,if_false]
    · exact (Nat.mod_eq_of_lt (by omega)).symm

theorem reducer_success (x : U64) :
    ∃ z : U32, field.reduce_u64 x = .ok z ∧
      z.val = x.val%P ∧ z.val < P := by
  let s := wrappedFold (wrappedFold x)
  have hv : s.val = foldBits (foldBits x.val) := by
    dsimp only [s]
    rw [wrappedFold_val,wrappedFold_val]
  have h32 : s.val < 2^32 := by rw [hv]; exact second_fold_lt_two_pow32 _ x.bv.isLt
  have h2p : (UScalar.cast .U32 s).val < 2*P := by
    rw [narrow_exact s h32,hv]
    exact second_fold_lt_two_mul_P _ x.bv.isLt
  obtain ⟨z,hz,hzv,hzc⟩ := finish32_success (UScalar.cast .U32 s) h2p
  refine ⟨z, ?_, ?_, hzc⟩
  · simp only [field.reduce_u64,lift,bind_tc_ok,UScalar.le_equiv,p_val]
    change finish32 (UScalar.cast .U32 s) = .ok z
    exact hz
  · rw [hzv,narrow_exact s h32,hv]
    have hmod := rawReduceU64_eq_mod_nat x.val (by exact x.bv.isLt)
    rw [rawReduceU64,second_fold_cast_exact x.val (by exact x.bv.isLt)] at hmod
    have hcanon := second_fold_lt_two_mul_P x.val x.bv.isLt
    unfold condSubP at hmod
    by_cases h : P ≤ foldBits (foldBits x.val)
    · rw [if_pos h] at hmod
      rw [Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
      exact hmod
    · rw [if_neg h] at hmod
      rw [Nat.mod_eq_of_lt (by omega)]
      exact hmod

theorem mul64_val (a b : U64) (h : a.val*b.val < 2^64) :
    (U64.wrapping_mul a b).val = a.val*b.val := by
  rw [U64.wrapping_mul_val_eq]
  simp only [UScalar.size,UScalarTy.numBits]
  exact Nat.mod_eq_of_lt h

theorem mul_success (a b : U32) :
    ∃ z : U32, field.M31.mul a b = .ok z ∧
      z.val = (a.val*b.val)%P ∧ z.val < P := by
  let product := U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)
  have hp : product.val = a.val*b.val := by
    dsimp only [product]
    rw [mul64_val,cast_widen_value,cast_widen_value]
    rw [cast_widen_value,cast_widen_value]
    have hproduct : a.val*b.val < (2^32)*(2^32) :=
      Nat.mul_lt_mul_of_lt_of_lt a.bv.isLt b.bv.isLt
    exact hproduct
  by_cases ha : a.val < P
  · by_cases hb : b.val < P
    · let s := wrappedFold product
      have hsv : s.val = foldBits (a.val*b.val) := by rw [wrappedFold_val,hp]
      have hs : s.val < 2*P := by
        rw [hsv]
        exact CanonicalProduct.fold_lt _ (CanonicalProduct.product_lt _ _ ha hb)
      obtain ⟨z,hz,hv,hc⟩ := finish64_success s hs
      refine ⟨z, ?_, ?_, hc⟩
      · simp only [field.M31.mul,UScalar.lt_equiv,p_val,ha,hb,if_true,lift,bind_tc_ok,
          UScalar.le_equiv,cast_widen_value,p_val]
        change finish64 s = .ok z
        exact hz
      · rw [hv,hsv]
        have hm := CanonicalProduct.one_fold_mod (a.val*b.val) (CanonicalProduct.product_lt _ _ ha hb)
        unfold condSubP at hm
        by_cases h : P ≤ foldBits (a.val*b.val)
        · rw [if_pos h] at hm
          rw [Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by rw [← hsv]; omega)]
          exact hm
        · rw [if_neg h] at hm
          rw [Nat.mod_eq_of_lt (by omega)]
          exact hm
    · obtain ⟨z,hz,hv,hc⟩ := reducer_success product
      refine ⟨z, ?_, ?_, hc⟩
      · simp only [field.M31.mul,UScalar.lt_equiv,p_val,ha,hb,if_true,if_false,lift,bind_tc_ok]
        change (do let z1 ← field.reduce_u64 product; ok z1) = .ok z
        simp only [hz,bind_tc_ok]
      · rw [hv,hp]
  · obtain ⟨z,hz,hv,hc⟩ := reducer_success product
    refine ⟨z, ?_, ?_, hc⟩
    · simp only [field.M31.mul,UScalar.lt_equiv,p_val,ha,if_false,lift,bind_tc_ok]
      change (do let z1 ← field.reduce_u64 product; ok z1) = .ok z
      simp only [hz,bind_tc_ok]
    · rw [hv,hp]

theorem reducer_eq (x : U64) :
    field.reduce_u64 x = AspisR64Field.field.reduce_u64 x := by
  obtain ⟨z,hz,hv,hc⟩ := reducer_success x
  obtain ⟨w,hw,hwv,hwc⟩ := InverseRuntimeMul.generated_reducer_mod x
  have hold : AspisR64Field.field.reduce_u64 x = .ok w := by
    rw [GuardedM31Execution.reducer_eq]
    exact hw
  rw [hz,hold]
  congr 1
  exact UScalar.eq_of_val_eq (hv.trans hwv.symm)

theorem mul_eq (a b : U32) :
    field.M31.mul a b = AspisR64Field.field.M31.mul a b := by
  obtain ⟨z,hz,hv,hc⟩ := mul_success a b
  obtain ⟨w,hw,hwv,hwc⟩ := GuardedM31Execution.generated_mul_success a b
  rw [hz,hw]
  congr 1
  exact UScalar.eq_of_val_eq (hv.trans hwv.symm)

theorem square_body_eq (r : core.ops.range.Range Usize) (x : U32) :
    field.square_n_loop.body r x = AspisR64Field.field.square_n_loop.body r x := by
  simp only [field.square_n_loop.body,AspisR64Field.field.square_n_loop.body,mul_eq]
  rfl

theorem square_loop_eq (r : core.ops.range.Range Usize) (x : U32) :
    field.square_n_loop r x = AspisR64Field.field.square_n_loop r x := by
  simp only [field.square_n_loop,AspisR64Field.field.square_n_loop,square_body_eq]

theorem square_eq (x : U32) (n : Usize) :
    field.square_n x n = AspisR64Field.field.square_n x n := by
  simp only [field.square_n,AspisR64Field.field.square_n,square_loop_eq]

theorem inv_eq (x : U32) : field.M31.inv x = AspisR64Field.field.M31.inv x := by
  simp only [field.M31.inv,AspisR64Field.field.M31.inv,mul_eq,square_eq]

open ComplexBaseExecution (encodeBase encodeBase_val encodeBase_cast eq_encodeBase)

theorem mul_encode (x y : AspisV8R15.ExactTowerBase.M31Exact) :
    field.M31.mul (encodeBase x) (encodeBase y) = .ok (encodeBase (x*y)) := by
  obtain ⟨z,hz,hv,hc⟩ := mul_success (encodeBase x) (encodeBase y)
  rw [hz]
  congr 1
  apply eq_encodeBase z (x*y) hc
  rw [hv,ZMod.natCast_mod,Nat.cast_mul,encodeBase_cast,encodeBase_cast]

theorem reduce_encode (x : U64) :
    field.M31.reduce_u64 x = .ok (encodeBase (x.val : AspisV8R15.ExactTowerBase.M31Exact)) := by
  obtain ⟨z,hz,hv,hc⟩ := reducer_success x
  simp only [field.M31.reduce_u64,hz,bind_tc_ok]
  congr 1
  apply eq_encodeBase z (x.val : AspisV8R15.ExactTowerBase.M31Exact) hc
  rw [hv,ZMod.natCast_mod]

theorem inv_encode (x : AspisV8R15.ExactTowerBase.M31Exact) (hx : x ≠ 0) :
    field.M31.inv (encodeBase x) = .ok (encodeBase x⁻¹) := by
  rw [inv_eq]
  obtain ⟨z,hz,hc,hv⟩ := GuardedInverseExecution.inverse_correct (encodeBase x)
    (ZMod.val_lt x) (by
      intro hz
      have he := encodeBase_cast x
      rw [hz,Nat.cast_zero] at he
      exact hx he.symm)
  rw [hz]
  congr 1
  apply eq_encodeBase z x⁻¹ hc
  simpa only [encodeBase_cast] using hv

theorem inv_zero : field.M31.inv (encodeBase 0) = .fail .assertionFailure := by
  rw [inv_eq]
  exact GuardedInverseExecution.zero_rejected

theorem neg_eq (x : U32) (hc : x.val < P) :
    field.M31.neg x = AspisR65Field.field.M31.neg x := by
  by_cases hz : x = 0#u32
  · simp only [field.M31.neg,AspisR65Field.field.M31.neg,hz,if_true]
  · have hb : field.P.val ≥ x.val := by rw [p_val]; omega
    have hs := R158WordBounds.checked_sub_eq_wrapping field.P x hb
    have hp : field.P = AspisR65Field.field.P := by
      simp only [field.P,AspisR65Field.field.P]
    simp only [field.M31.neg,AspisR65Field.field.M31.neg,hz,if_false,
      ← hp,hs,lift,bind_tc_ok]

theorem neg_encode (x : AspisV8R15.ExactTowerBase.M31Exact) :
    field.M31.neg (encodeBase x) = .ok (encodeBase (-x)) := by
  rw [neg_eq (encodeBase x) (by simpa [AspisV8R15.ExactTowerBase.P,P] using ZMod.val_lt x)]
  exact ComplexBaseExecution.neg_encode x

#print axioms shift31_val
#print axioms wrappedFold_val
#print axioms finish64_success
#print axioms finish32_success
#print axioms reducer_success
#print axioms mul64_val
#print axioms mul_success
#print axioms reducer_eq
#print axioms mul_eq
#print axioms square_body_eq
#print axioms square_loop_eq
#print axioms square_eq
#print axioms inv_eq
#print axioms mul_encode
#print axioms reduce_encode
#print axioms inv_encode
#print axioms inv_zero
#print axioms neg_eq
#print axioms neg_encode
#print axioms AspisR156FullFreeze.aspis_core.field.M31.add
#print axioms AspisR156FullFreeze.aspis_core.field.M31.sub
#print axioms AspisR156FullFreeze.aspis_core.field.M31.mul
#print axioms AspisR156FullFreeze.aspis_core.field.M31.inv
#print axioms AspisR156FullFreeze.aspis_core.field.QM31.mul
#print axioms AspisR156FullFreeze.aspis_core.circle.secure_ood_circle_point_from_parameter
#print axioms AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_secure_circle_point
end AspisV8R19.R161WrappedMulExecution
