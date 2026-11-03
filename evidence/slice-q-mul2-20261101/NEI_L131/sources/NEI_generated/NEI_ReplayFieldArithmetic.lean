import NEI_FieldWide
import NEI_LineDomains
import NEI_ReductionWord
import FIo_ReduceBounds
import FIo_ScalarBridge
noncomputable section
-- Unchanged retained declarations from lean/FIo_FieldBridge.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NEI_FIo_FieldBridge
open Aeneas Aeneas.Std Result
abbrev NC := FIo_Native.aspis_core.field.CM31
abbrev NQ := FIo_Native.aspis_core.field.QM31
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact
abbrev CC := AspisR1CurrentWide.field.CM31
abbrev CQ := AspisR1CurrentWide.field.QM31
abbrev CE := AspisR1CurrentWide.field.wide_exact.WideExact

def cm (x : NC) : CC := ⟨x.a,x.b⟩
def qm (x : NQ) : CQ := ⟨cm x.c0,cm x.c1⟩
def wide (x : NE) : CE := ⟨qm x.c0,qm x.c1⟩
def map {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x) | .fail e => .fail e | .div => .div

theorem map_bind {A B C : Type} (f : B → C) (x : Result A) (k : A → Result B) :
    map f (do let v ← x; k v) = (do let v ← x; map f (k v)) := by
  cases x <;> rfl

theorem map_ok {A B : Type} (f : A → B) (x : A) : map f (.ok x)=.ok (f x) := rfl

#print axioms map_bind
#print axioms map_ok
end AspisR1.NEI_FIo_FieldBridge
end

-- Unchanged retained declarations from lean/FIo_ReduceBridge.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NEI_FIo_ReduceBridge
open Aeneas Aeneas.Std Result

theorem same (x : U64) :
    FIo_Native.aspis_core.field.reduce_u64 x=AspisR1CurrentWide.field.reduce_u64 x := by
  have cast_mask : UScalar.cast .U64 (2147483647#u32)=(2147483647#u64) := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  simp only [FIo_Native.aspis_core.field.reduce_u64,AspisR1CurrentWide.field.reduce_u64,
    FIo_Native.aspis_core.field.P,AspisR1CurrentWide.field.P,lift,bind_tc_ok,FIo_ReduceFacts.shr31,cast_mask]
  rw [FIo_ReduceBounds.checked x]
  simp only [bind_tc_ok,FIo_ReduceFacts.shr31]
  rw [FIo_ReduceBounds.checked (FIo_ReduceBounds.fold x)]
  simp only [bind_tc_ok,FIo_ReduceBounds.fold]
  split
  · rename_i h
    rw [FIo_ScalarBridge.sub _ (2147483647#u32) (by scalar_tac)]
    rfl
  · rfl

#print axioms same
end AspisR1.NEI_FIo_ReduceBridge
end

-- Unchanged retained declarations from lean/FIo_M31Bridge.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NEI_FIo_M31Bridge
open Aeneas Aeneas.Std Result

theorem add (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.add x y=AspisR1CurrentWide.field.M31.add x y := by
  have hadd : x+y=ok (U32.wrapping_add x y) :=
    FIo_ScalarBridge.add x y (by scalar_tac)
  simp only [FIo_Native.aspis_core.field.M31.add,AspisR1CurrentWide.field.M31.add,
    FIo_Native.aspis_core.field.P,AspisR1CurrentWide.field.P,hadd,lift,bind_tc_ok]
  split
  · rename_i h
    have hs : (2147483647#u32).val≤(U32.wrapping_add x y).val := by scalar_tac
    have hsub := FIo_ScalarBridge.sub (U32.wrapping_add x y) (2147483647#u32) hs
    rw [hsub]
    rfl
  · rfl

#print axioms add
end AspisR1.NEI_FIo_M31Bridge
end

-- Unchanged retained declarations from lean/FIo_M31SubBridge.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NEI_FIo_M31SubBridge
open Aeneas Aeneas.Std Result

theorem sub (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.sub x y=AspisR1CurrentWide.field.M31.sub x y := by
  have hadd : x+(2147483647#u32)=ok (U32.wrapping_add x (2147483647#u32)) :=
    FIo_ScalarBridge.add x (2147483647#u32) (by scalar_tac)
  have val : (U32.wrapping_add x (2147483647#u32)).val=x.val+2147483647 := by
    rw [U32.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
    rfl
  have hsub : (U32.wrapping_add x (2147483647#u32))-y=
      ok (U32.wrapping_sub (U32.wrapping_add x (2147483647#u32)) y) :=
    FIo_ScalarBridge.sub _ y (by rw [val]; omega)
  simp only [FIo_Native.aspis_core.field.M31.sub,AspisR1CurrentWide.field.M31.sub,
    FIo_Native.aspis_core.field.P,AspisR1CurrentWide.field.P,hadd,hsub,lift,bind_tc_ok]
  split
  · rename_i h
    have last := FIo_ScalarBridge.sub
      (U32.wrapping_sub (U32.wrapping_add x (2147483647#u32)) y) (2147483647#u32) (by scalar_tac)
    rw [last]
    rfl
  · rfl

#print axioms sub
end AspisR1.NEI_FIo_M31SubBridge
end

-- Unchanged retained declarations from lean/FIo_M31MulBridge.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NEI_FIo_M31MulBridge
open Aeneas Aeneas.Std Result

theorem product_bound (x y : U32) :
    (UScalar.cast .U64 x).val*(UScalar.cast .U64 y).val<UScalar.size .U64 := by
  have cx : (UScalar.cast .U64 x).val=x.val := by scalar_tac
  have cy : (UScalar.cast .U64 y).val=y.val := by scalar_tac
  have hx : x.val≤4294967295 := by scalar_tac
  have hy : y.val≤4294967295 := by scalar_tac
  have hp := Nat.mul_le_mul hx hy
  rw [cx,cy]
  scalar_tac

theorem same (x y : U32) :
    FIo_Native.aspis_core.field.M31.mul x y=AspisR1CurrentWide.field.M31.mul x y := by
  have hm := FIo_ScalarBridge.mul (UScalar.cast .U64 x) (UScalar.cast .U64 y) (product_bound x y)
  simp only [FIo_Native.aspis_core.field.M31.mul,AspisR1CurrentWide.field.M31.mul,
    lift,bind_tc_ok,hm,NEI_FIo_ReduceBridge.same]
  rfl

#print axioms product_bound
#print axioms same
end AspisR1.NEI_FIo_M31MulBridge
end

-- Unchanged retained declarations from lean/LPf_CoreReduction.lean
set_option autoImplicit false
namespace AspisR1.NEI_LPf_CoreReduction
open Aeneas Aeneas.Std Result

/-- The two frozen source reducers place the u32 cast on opposite sides of
subtraction. Their twice-folded bounds make those placements equivalent. -/
theorem same (x : U64) :
    FIo_Native.aspis_core.field.reduce_u64 x =
    FIo_Native.fast_pairing.canonical.reduce x := by
  let m := FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)
  have small : m.val < 4294967294 := by
    rw [_root_.NEI_ReductionWord.twice_value]
    apply LPe_MersenneReduction.fold_twice_lt
    scalar_tac
  have cv : (UScalar.cast .U32 m).val = m.val := by scalar_tac
  unfold FIo_Native.aspis_core.field.reduce_u64 FIo_Native.fast_pairing.canonical.reduce
  simp only [FIo_Native.aspis_core.field.P, FIo_Native.fast_pairing.canonical.P,
    lift, bind_tc_ok]
  change (if UScalar.cast .U32 m ≥ 2147483647#u32
    then ok (U32.wrapping_sub (UScalar.cast .U32 m) 2147483647#u32)
    else ok (UScalar.cast .U32 m)) =
    (if m ≥ 2147483647#u64
    then ok (UScalar.cast .U32 (U64.wrapping_sub m 2147483647#u64))
    else ok (UScalar.cast .U32 m))
  split
  · rename_i h
    have hm : m ≥ 2147483647#u64 := by scalar_tac
    rw [if_pos hm]
    congr 1
    apply UScalar.eq_of_val_eq
    unfold U32.wrapping_sub U64.wrapping_sub
    rw [UScalar.cast_val_eq, UScalar.wrapping_sub_val_eq,
      UScalar.wrapping_sub_val_eq]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits,U32.size,U32.numBits]
    omega
  · rename_i h
    have hm : ¬m ≥ 2147483647#u64 := by scalar_tac
    rw [if_neg hm]

/-- Total exact base-field reduction on every source word. -/
theorem source (x : U64) : ∃ z,
    FIo_Native.aspis_core.field.reduce_u64 x = ok z ∧
    z.val = x.val % 2147483647 ∧ z.val < 2147483647 := by
  rw [same]
  exact _root_.NEI_ReductionWord.native_reduce x

#print axioms same
#print axioms source
end AspisR1.NEI_LPf_CoreReduction

-- Unchanged retained declarations from lean/LPf_BaseMultiply.lean
set_option autoImplicit false
namespace AspisR1.NEI_LPf_BaseMultiply
open Aeneas Aeneas.Std Result

/-- Full u32 operands, without a canonical-input restriction. -/
theorem product_bound (x y : U32) : x.val * y.val < 18446744073709551616 := by
  have hx : x.val ≤ 4294967295 := by scalar_tac
  have hy : y.val ≤ 4294967295 := by scalar_tac
  have bound := Nat.mul_le_mul hx hy
  omega

theorem word_product (x y : U32) :
    (U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y)).val = x.val*y.val := by
  rw [U64.wrapping_mul_val_eq]
  have cx : (UScalar.cast .U64 x).val = x.val := by scalar_tac
  have cy : (UScalar.cast .U64 y).val = y.val := by scalar_tac
  rw [cx, cy]
  apply Nat.mod_eq_of_lt
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]
  exact product_bound x y

/-- The actual extracted frozen M31 multiplication is total and equals
natural multiplication modulo P. This is a Lean source theorem, not a claim
that the timed-out Kani exact contract passed. -/
theorem source (x y : U32) : ∃ z,
    FIo_Native.aspis_core.field.M31.mul x y = ok z ∧
    z.val = (x.val*y.val) % 2147483647 ∧ z.val < 2147483647 := by
  obtain ⟨z, run, val, canonical⟩ := NEI_LPf_CoreReduction.source
    (U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y))
  refine ⟨z, ?_, ?_, canonical⟩
  · simp only [FIo_Native.aspis_core.field.M31.mul,lift,bind_tc_ok,run]
  · rw [word_product] at val
    exact val

#print axioms product_bound
#print axioms word_product
#print axioms source
end AspisR1.NEI_LPf_BaseMultiply

-- Unchanged retained declarations from lean/LPi_Total.lean
set_option autoImplicit false
namespace AspisR1.NEI_LPi_Total
open Aeneas Aeneas.Std Result
abbrev NC := FIo_Native.aspis_core.field.CM31
abbrev NQ := FIo_Native.aspis_core.field.QM31
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact

def Total {α : Type} (r : Result α) : Prop := ∃ z, r = ok z

theorem bind_total {α β : Type} {r : Result α} {k : α → Result β}
    (hr : Total r) (hk : ∀ x, Total (k x)) : Total (r >>= k) := by
  obtain ⟨x,hx⟩ := hr
  rw [hx,bind_tc_ok]
  exact hk x

theorem m31_mul (x y : U32) : Total (FIo_Native.aspis_core.field.M31.mul x y) := by
  obtain ⟨z,h,_,_⟩ := NEI_LPf_BaseMultiply.source x y
  exact ⟨z,h⟩

theorem reduce (x : U64) : Total (FIo_Native.aspis_core.field.M31.reduce_u64 x) := by
  obtain ⟨z,h,_,_⟩ := NEI_LPf_CoreReduction.source x
  exact ⟨z,by simp only [FIo_Native.aspis_core.field.M31.reduce_u64,h,bind_tc_ok]⟩

theorem m31_add (x y : U32) : Total (FIo_Native.aspis_core.field.M31.add x y) := by
  simp only [FIo_Native.aspis_core.field.M31.add,lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩

theorem m31_sub (x y : U32) : Total (FIo_Native.aspis_core.field.M31.sub x y) := by
  simp only [FIo_Native.aspis_core.field.M31.sub,lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩

theorem cm_add (x y : NC) : Total (FIo_Native.aspis_core.field.CM31.add x y) := by
  unfold FIo_Native.aspis_core.field.CM31.add
  apply bind_total (m31_add _ _); intro a
  apply bind_total (m31_add _ _); intro b
  exact ⟨_,rfl⟩

theorem cm_sub (x y : NC) : Total (FIo_Native.aspis_core.field.CM31.sub x y) := by
  unfold FIo_Native.aspis_core.field.CM31.sub
  apply bind_total (m31_sub _ _); intro a
  apply bind_total (m31_sub _ _); intro b
  exact ⟨_,rfl⟩

theorem cm_mul (x y : NC) : Total (FIo_Native.aspis_core.field.CM31.mul x y) := by
  unfold FIo_Native.aspis_core.field.CM31.mul
  apply bind_total (m31_mul _ _); intro a
  apply bind_total (m31_mul _ _); intro b
  simp only [lift,bind_tc_ok]
  apply bind_total (reduce _); intro c
  apply bind_total (m31_sub _ _); intro d
  apply bind_total (m31_sub _ _); intro e
  apply bind_total (m31_sub _ _); intro f
  exact ⟨_,rfl⟩

theorem by_r (x : NC) : Total (FIo_Native.aspis_core.field.mul_by_r x) := by
  unfold FIo_Native.aspis_core.field.mul_by_r FIo_Native.aspis_core.field.M31.double
  apply bind_total (m31_add _ _); intro a
  apply bind_total (m31_sub _ _); intro b
  apply bind_total (m31_add _ _); intro c
  apply bind_total (m31_add _ _); intro d
  exact ⟨_,rfl⟩

theorem qm_add (x y : NQ) : Total (FIo_Native.aspis_core.field.QM31.add x y) := by
  unfold FIo_Native.aspis_core.field.QM31.add
  apply bind_total (cm_add _ _); intro a
  apply bind_total (cm_add _ _); intro b
  exact ⟨_,rfl⟩

theorem qm_sub (x y : NQ) : Total (FIo_Native.aspis_core.field.QM31.sub x y) := by
  unfold FIo_Native.aspis_core.field.QM31.sub
  apply bind_total (cm_sub _ _); intro a
  apply bind_total (cm_sub _ _); intro b
  exact ⟨_,rfl⟩

theorem qm_mul (x y : NQ) : Total (FIo_Native.aspis_core.field.QM31.mul x y) := by
  unfold FIo_Native.aspis_core.field.QM31.mul
  apply bind_total (cm_mul _ _); intro a
  apply bind_total (cm_mul _ _); intro b
  apply bind_total (cm_add _ _); intro c
  apply bind_total (cm_add _ _); intro d
  apply bind_total (cm_mul _ _); intro e
  apply bind_total (by_r _); intro f
  apply bind_total (cm_add _ _); intro g
  apply bind_total (cm_sub _ _); intro h
  apply bind_total (cm_sub _ _); intro i
  exact ⟨_,rfl⟩

theorem mul_u (x : NQ) : Total (FIo_Native.aspis_core.field.wide_exact.mul_u x) := by
  unfold FIo_Native.aspis_core.field.wide_exact.mul_u
  apply bind_total (by_r _); intro a
  exact ⟨_,rfl⟩

theorem wide_mul (x y : NE) : Total (FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y) := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.mul
  apply bind_total (qm_mul _ _); intro a
  apply bind_total (qm_mul _ _); intro b
  apply bind_total (qm_add _ _); intro c
  apply bind_total (qm_add _ _); intro d
  apply bind_total (qm_mul _ _); intro e
  apply bind_total (mul_u _); intro f
  apply bind_total (qm_add _ _); intro g
  apply bind_total (qm_sub _ _); intro h
  apply bind_total (qm_sub _ _); intro i
  exact ⟨_,rfl⟩

#print axioms bind_total
#print axioms m31_mul
#print axioms reduce
#print axioms m31_add
#print axioms m31_sub
#print axioms cm_add
#print axioms cm_sub
#print axioms cm_mul
#print axioms by_r
#print axioms qm_add
#print axioms qm_sub
#print axioms qm_mul
#print axioms mul_u
#print axioms wide_mul
end AspisR1.NEI_LPi_Total

-- Unchanged retained declarations from lean/LPi_NatBase.lean
set_option autoImplicit false
namespace AspisR1.NEI_LPi_NatBase
open Aeneas Aeneas.Std Result

theorem sub_word (x y : U32) (h : y.val ≤ x.val) :
    (U32.wrapping_sub x y).val = x.val-y.val := by
  rw [U32.wrapping_sub_val_eq]
  have hx := x.hSize
  have hy := y.hSize
  have he : x.val+(UScalar.size .U32-y.val)=(x.val-y.val)+UScalar.size .U32 := by omega
  rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]

theorem add (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.add x y = ok z ∧
    z.val = (x.val+y.val)%2147483647 ∧ z.val < 2147483647 := by
  let s := U32.wrapping_add x y
  have sv : s.val = x.val+y.val := by
    rw [U32.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
  simp only [FIo_Native.aspis_core.field.M31.add,FIo_Native.aspis_core.field.P,lift,bind_tc_ok]
  change ∃ z, (if s ≥ 2147483647#u32 then
    ok (U32.wrapping_sub s 2147483647#u32) else ok s) = ok z ∧ _
  by_cases h : s ≥ 2147483647#u32
  · rw [if_pos h]
    have hp : 2147483647 ≤ s.val := by scalar_tac
    refine ⟨_,rfl,?_,?_⟩
    · rw [sub_word s 2147483647#u32 hp]
      change s.val-2147483647 = (x.val+y.val)%2147483647
      rw [←sv,Nat.mod_eq_sub_mod hp,Nat.mod_eq_of_lt (by omega)]
    · rw [sub_word s 2147483647#u32 hp]; change s.val-2147483647 < 2147483647; omega
  · rw [if_neg h]
    have hp : s.val < 2147483647 := by scalar_tac
    exact ⟨_,rfl,by rw [←sv,Nat.mod_eq_of_lt hp],hp⟩

theorem sub (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.sub x y = ok z ∧
    z.val = (x.val+2147483647-y.val)%2147483647 ∧ z.val < 2147483647 := by
  let a := U32.wrapping_add x 2147483647#u32
  have av : a.val = x.val+2147483647 := by
    rw [U32.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
    rfl
  let s := U32.wrapping_sub a y
  have sv : s.val = x.val+2147483647-y.val := by
    rw [sub_word _ _ (by omega),av]
  simp only [FIo_Native.aspis_core.field.M31.sub,FIo_Native.aspis_core.field.P,lift,bind_tc_ok]
  change ∃ z, (if s ≥ 2147483647#u32 then
    ok (U32.wrapping_sub s 2147483647#u32) else ok s) = ok z ∧ _
  by_cases h : s ≥ 2147483647#u32
  · rw [if_pos h]
    have hp : 2147483647 ≤ s.val := by scalar_tac
    refine ⟨_,rfl,?_,?_⟩
    · rw [sub_word s 2147483647#u32 hp]
      change s.val-2147483647 = (x.val+2147483647-y.val)%2147483647
      rw [←sv,Nat.mod_eq_sub_mod hp,Nat.mod_eq_of_lt (by omega)]
    · rw [sub_word s 2147483647#u32 hp]; change s.val-2147483647 < 2147483647; omega
  · rw [if_neg h]
    have hp : s.val < 2147483647 := by scalar_tac
    exact ⟨_,rfl,by rw [←sv,Nat.mod_eq_of_lt hp],hp⟩

#print axioms sub_word
#print axioms add
#print axioms sub
end AspisR1.NEI_LPi_NatBase

-- Unchanged retained declarations from lean/LPi_CMProduct.lean
set_option autoImplicit false
namespace AspisR1.NEI_LPi_CMProduct
open Aeneas Aeneas.Std Result NEI_LPi_Total
abbrev NC := FIo_Native.aspis_core.field.CM31

def Canon (x : NC) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647

def realWord (a b c d : Nat) := ((a*c)%2147483647+2147483647-(b*d)%2147483647)%2147483647
def imagWord (a b c d : Nat) :=
  ((((a+b)*(c+d))%2147483647+2147483647-(a*c)%2147483647)%2147483647+
    2147483647-(b*d)%2147483647)%2147483647

def sum (x : NC) : U64 := U64.wrapping_add
  (core.convert.num.FromU64U32.from x.a) (core.convert.num.FromU64U32.from x.b)
def cross (x y : NC) : U64 := U64.wrapping_mul (sum x) (sum y)

theorem sum_value (x : NC) : (sum x).val=x.a.val+x.b.val := by
  unfold sum
  rw [U64.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
  rfl

theorem cross_value (x y : NC) (hx : Canon x) (hy : Canon y) :
    (cross x y).val=(x.a.val+x.b.val)*(y.a.val+y.b.val) := by
  unfold cross
  rw [U64.wrapping_mul_val_eq,sum_value,sum_value]
  apply Nat.mod_eq_of_lt
  have h0 : x.a.val+x.b.val < 4294967296 := by obtain ⟨_,_⟩ := hx; omega
  have h1 : y.a.val+y.b.val < 4294967296 := by obtain ⟨_,_⟩ := hy; omega
  have h := Nat.mul_lt_mul_of_lt_of_lt h0 h1
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits] at h ⊢
  exact h

theorem source (x y : NC) (hx : Canon x) (hy : Canon y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y = ok z ∧ Canon z ∧
      z.a.val = realWord x.a.val x.b.val y.a.val y.b.val ∧
      z.b.val = imagWord x.a.val x.b.val y.a.val y.b.val := by
  obtain ⟨m0,h0,v0,c0⟩ := NEI_LPf_BaseMultiply.source x.a y.a
  obtain ⟨m1,h1,v1,c1⟩ := NEI_LPf_BaseMultiply.source x.b y.b
  obtain ⟨m2,h2,v2,c2⟩ := NEI_LPf_CoreReduction.source (cross x y)
  have hr : FIo_Native.aspis_core.field.M31.reduce_u64 (cross x y) = ok m2 := by
    simp only [FIo_Native.aspis_core.field.M31.reduce_u64,h2,bind_tc_ok]
  obtain ⟨a,ha,va,ca⟩ := NEI_LPi_NatBase.sub m0 m1 c0 c1
  obtain ⟨b,hb,vb,cb⟩ := NEI_LPi_NatBase.sub m2 m0 c2 c0
  obtain ⟨c,hc,vc,cc⟩ := NEI_LPi_NatBase.sub b m1 cb c1
  refine ⟨⟨a,c⟩,?_,⟨ca,cc⟩,?_,?_⟩
  · simp only [FIo_Native.aspis_core.field.CM31.mul,h0,h1,lift,bind_tc_ok]
    change (do let t ← FIo_Native.aspis_core.field.M31.reduce_u64 (cross x y)
               let a ← FIo_Native.aspis_core.field.M31.sub m0 m1
               let b ← FIo_Native.aspis_core.field.M31.sub t m0
               let c ← FIo_Native.aspis_core.field.M31.sub b m1
               ok (⟨a,c⟩ : NC)) = _
    simp only [hr,ha,hb,hc,bind_tc_ok]
  · simpa only [realWord,v0,v1] using va
  · rw [cross_value x y hx hy] at v2
    simpa only [imagWord,vb,v2,v0,v1] using vc

#print axioms sum_value
#print axioms cross_value
#print axioms source
end AspisR1.NEI_LPi_CMProduct

-- Unchanged retained declarations from lean/LPi_FieldValues.lean
set_option autoImplicit false
namespace AspisR1.NEI_LPi_FieldValues
open Aeneas Aeneas.Std Result
abbrev NC := NEI_LPi_CMProduct.NC
abbrev NQ := NEI_LPi_Total.NQ
abbrev NE := NEI_LPi_Total.NE
abbrev CW := Nat × Nat
abbrev QW := CW × CW
abbrev EW := QW × QW
def cw (x : NC) : CW := (x.a.val,x.b.val)
def qw (x : NQ) : QW := (cw x.c0,cw x.c1)
def ew (x : NE) : EW := (qw x.c0,qw x.c1)
def canonC := NEI_LPi_CMProduct.Canon
def canonQ (x : NQ) : Prop := canonC x.c0 ∧ canonC x.c1
def canonE (x : NE) : Prop := canonQ x.c0 ∧ canonQ x.c1
def addM (a b : Nat) := (a+b)%2147483647
def subM (a b : Nat) := (a+2147483647-b)%2147483647
def addC (a b : CW) : CW := (addM a.1 b.1,addM a.2 b.2)
def subC (a b : CW) : CW := (subM a.1 b.1,subM a.2 b.2)
def mulC (a b : CW) : CW := (NEI_LPi_CMProduct.realWord a.1 a.2 b.1 b.2,
  NEI_LPi_CMProduct.imagWord a.1 a.2 b.1 b.2)
def byR (a : CW) : CW := (subM (addM a.1 a.1) a.2,addM a.1 (addM a.2 a.2))
def addQ (a b : QW) : QW := (addC a.1 b.1,addC a.2 b.2)
def subQ (a b : QW) : QW := (subC a.1 b.1,subC a.2 b.2)
def mulQ (a b : QW) : QW :=
  let ac := mulC a.1 b.1
  let bd := mulC a.2 b.2
  let cross := mulC (addC a.1 a.2) (addC b.1 b.2)
  (addC ac (byR bd),subC (subC cross ac) bd)
def mulU (a : QW) : QW := (byR a.2,a.1)
def mulE (a b : EW) : EW :=
  let ac := mulQ a.1 b.1
  let bd := mulQ a.2 b.2
  let cross := mulQ (addQ a.1 a.2) (addQ b.1 b.2)
  (addQ ac (mulU bd),subQ (subQ cross ac) bd)

theorem cm_mul (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y = ok z ∧ canonC z ∧
      cw z = mulC (cw x) (cw y) := by
  obtain ⟨z,h,c,a,b⟩ := NEI_LPi_CMProduct.source x y hx hy
  exact ⟨z,h,c,Prod.ext a b⟩

theorem cm_add (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.add x y = ok z ∧ canonC z ∧
      cw z = addC (cw x) (cw y) := by
  obtain ⟨a,ha,va,ca⟩ := NEI_LPi_NatBase.add x.a y.a hx.1 hy.1
  obtain ⟨b,hb,vb,cb⟩ := NEI_LPi_NatBase.add x.b y.b hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.add,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

theorem cm_sub (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.sub x y = ok z ∧ canonC z ∧
      cw z = subC (cw x) (cw y) := by
  obtain ⟨a,ha,va,ca⟩ := NEI_LPi_NatBase.sub x.a y.a hx.1 hy.1
  obtain ⟨b,hb,vb,cb⟩ := NEI_LPi_NatBase.sub x.b y.b hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.sub,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

theorem by_r (x : NC) (hx : canonC x) :
    ∃ z, FIo_Native.aspis_core.field.mul_by_r x = ok z ∧ canonC z ∧ cw z = byR (cw x) := by
  obtain ⟨a,ha,va,ca⟩ := NEI_LPi_NatBase.add x.a x.a hx.1 hx.1
  obtain ⟨b,hb,vb,cb⟩ := NEI_LPi_NatBase.sub a x.b ca hx.2
  obtain ⟨c,hc,vc,cc⟩ := NEI_LPi_NatBase.add x.b x.b hx.2 hx.2
  obtain ⟨d,hd,vd,cd⟩ := NEI_LPi_NatBase.add x.a c hx.1 cc
  refine ⟨⟨b,d⟩,?_,⟨cb,cd⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.mul_by_r,FIo_Native.aspis_core.field.M31.double,
      ha,hb,hc,hd,bind_tc_ok]
  · exact Prod.ext (by simpa only [cw,byR,addM,subM,va] using vb) (by simpa only [cw,byR,addM,subM,vc] using vd)

#print axioms cm_mul
#print axioms cm_add
#print axioms cm_sub
#print axioms by_r
end AspisR1.NEI_LPi_FieldValues

-- Unchanged retained declarations from lean/LPi_TowerValues.lean
set_option autoImplicit false
namespace AspisR1.NEI_LPi_TowerValues
open Aeneas Aeneas.Std Result NEI_LPi_FieldValues

theorem qm_add (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.add x y = ok z ∧ canonQ z ∧
      qw z = addQ (qw x) (qw y) := by
  obtain ⟨a,ha,ca,va⟩ := cm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := cm_add x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [FIo_Native.aspis_core.field.QM31.add,ha,hb,bind_tc_ok]

theorem qm_sub (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.sub x y = ok z ∧ canonQ z ∧
      qw z = subQ (qw x) (qw y) := by
  obtain ⟨a,ha,ca,va⟩ := cm_sub x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := cm_sub x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [FIo_Native.aspis_core.field.QM31.sub,ha,hb,bind_tc_ok]

theorem qm_mul (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul x y = ok z ∧ canonQ z ∧
      qw z = mulQ (qw x) (qw y) := by
  obtain ⟨ac,hac,cac,vac⟩ := cm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,vbd⟩ := cm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,va⟩ := cm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,vb⟩ := cm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,vcross⟩ := cm_mul a b ca cb
  obtain ⟨r,hr,cr,vr⟩ := by_r bd cbd
  obtain ⟨lo,hlo,clo,vlo⟩ := cm_add ac r cac cr
  obtain ⟨diff,hdiff,cdiff,vdiff⟩ := cm_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,vhi⟩ := cm_sub diff bd cdiff cbd
  refine ⟨⟨lo,hi⟩,?_,⟨clo,chi⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.QM31.mul,hac,hbd,ha,hb,hcross,hr,hlo,hdiff,hhi,bind_tc_ok]
  · simp only [qw,mulQ]
    rw [vlo,vhi,vdiff,vr,vcross,va,vb,vac,vbd]


theorem mul_u (x : NQ) (hx : canonQ x) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.mul_u x = ok z ∧ canonQ z ∧
      qw z = mulU (qw x) := by
  obtain ⟨a,ha,ca,va⟩ := by_r x.c1 hx.2
  refine ⟨⟨a,x.c0⟩,?_,⟨ca,hx.1⟩,Prod.ext va rfl⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.mul_u,ha,bind_tc_ok]

theorem wide_mul (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y = ok z ∧ canonE z ∧
      ew z = mulE (ew x) (ew y) := by
  obtain ⟨ac,hac,cac,vac⟩ := qm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,vbd⟩ := qm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,va⟩ := qm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,vb⟩ := qm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,vcross⟩ := qm_mul a b ca cb
  obtain ⟨r,hr,cr,vr⟩ := mul_u bd cbd
  obtain ⟨lo,hlo,clo,vlo⟩ := qm_add ac r cac cr
  obtain ⟨diff,hdiff,cdiff,vdiff⟩ := qm_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,vhi⟩ := qm_sub diff bd cdiff cbd
  refine ⟨⟨lo,hi⟩,?_,⟨clo,chi⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul,hac,hbd,ha,hb,hcross,hr,hlo,hdiff,hhi,bind_tc_ok]
  · simp only [ew,mulE]
    rw [vlo,vhi,vdiff,vr,vcross,va,vb,vac,vbd]

#print axioms qm_add
#print axioms qm_sub
#print axioms qm_mul
#print axioms mul_u
#print axioms wide_mul
end AspisR1.NEI_LPi_TowerValues

-- Unchanged retained declarations from lean/LPi_MixedValues.lean
set_option autoImplicit false
namespace AspisR1.NEI_LPi_MixedValues
open Aeneas Aeneas.Std Result NEI_LPi_FieldValues

theorem cm_m31 (x : NC) (s : U32) : ∃ z,
    FIo_Native.aspis_core.field.CM31.mul_m31 x s = ok z ∧ canonC z ∧
      cw z = ((x.a.val*s.val)%2147483647,(x.b.val*s.val)%2147483647) := by
  obtain ⟨a,ha,va,ca⟩ := NEI_LPf_BaseMultiply.source x.a s
  obtain ⟨b,hb,vb,cb⟩ := NEI_LPf_BaseMultiply.source x.b s
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.mul_m31,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

theorem qm_m31 (x : NQ) (s : U32) : ∃ z,
    FIo_Native.aspis_core.field.QM31.mul_m31 x s = ok z ∧ canonQ z ∧
      qw z = (((x.c0.a.val*s.val)%2147483647,(x.c0.b.val*s.val)%2147483647),
        ((x.c1.a.val*s.val)%2147483647,(x.c1.b.val*s.val)%2147483647)) := by
  obtain ⟨a,ha,ca,va⟩ := cm_m31 x.c0 s
  obtain ⟨b,hb,cb,vb⟩ := cm_m31 x.c1 s
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.QM31.mul_m31,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

#print axioms cm_m31
#print axioms qm_m31
end AspisR1.NEI_LPi_MixedValues

-- Unchanged retained declarations from evidence/slice-q-compose-20261029/NEB_FieldDomains.lean
set_option autoImplicit false
namespace NEI_NEB_FieldDomains
open Aeneas Aeneas.Std Result AspisR1 NEI_LPi_FieldValues

/-- Projection is the actual argument expression in CM31.add/sub/mul. -/
theorem cm_arguments (x y : NC) (hx : canonC x) (hy : canonC y) :
    x.a.val < 2147483647 ∧ y.a.val < 2147483647 ∧
    x.b.val < 2147483647 ∧ y.b.val < 2147483647 :=
  ⟨hx.1,hy.1,hx.2,hy.2⟩

/-- Two same-input calls, in source order, returning canonical carriers. -/
theorem cm_add_calls (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ a b,
      FIo_Native.aspis_core.field.M31.add x.a y.a = ok a ∧
      FIo_Native.aspis_core.field.M31.add x.b y.b = ok b ∧
      a.val < 2147483647 ∧ b.val < 2147483647 ∧
      FIo_Native.aspis_core.field.CM31.add x y = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,_,ca⟩ := NEI_LPi_NatBase.add x.a y.a hx.1 hy.1
  obtain ⟨b,hb,_,cb⟩ := NEI_LPi_NatBase.add x.b y.b hx.2 hy.2
  exact ⟨a,b,ha,hb,ca,cb,by simp only [FIo_Native.aspis_core.field.CM31.add,ha,hb,bind_tc_ok]⟩

theorem cm_sub_calls (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ a b,
      FIo_Native.aspis_core.field.M31.sub x.a y.a = ok a ∧
      FIo_Native.aspis_core.field.M31.sub x.b y.b = ok b ∧
      a.val < 2147483647 ∧ b.val < 2147483647 ∧
      FIo_Native.aspis_core.field.CM31.sub x y = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,_,ca⟩ := NEI_LPi_NatBase.sub x.a y.a hx.1 hy.1
  obtain ⟨b,hb,_,cb⟩ := NEI_LPi_NatBase.sub x.b y.b hx.2 hy.2
  exact ⟨a,b,ha,hb,ca,cb,by simp only [FIo_Native.aspis_core.field.CM31.sub,ha,hb,bind_tc_ok]⟩

theorem qm_arguments (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    canonC x.c0 ∧ canonC y.c0 ∧ canonC x.c1 ∧ canonC y.c1 :=
  ⟨hx.1,hy.1,hx.2,hy.2⟩

theorem wide_arguments (x y : NE) (hx : canonE x) (hy : canonE y) :
    canonQ x.c0 ∧ canonQ y.c0 ∧ canonQ x.c1 ∧ canonQ y.c1 :=
  ⟨hx.1,hy.1,hx.2,hy.2⟩

/-- An earlier addition's returned carrier establishes the later product's
input domain. The result is selected by the actual emitted call. -/
theorem cm_cross_arguments (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ a b,
      FIo_Native.aspis_core.field.CM31.add x y = ok a ∧ canonC a ∧
      FIo_Native.aspis_core.field.CM31.mul a x = ok b ∧ canonC b := by
  obtain ⟨a,ha,ca,_⟩ := cm_add x y hx hy
  obtain ⟨b,hb,cb,_⟩ := cm_mul a x ca hx
  exact ⟨a,b,ha,ca,hb,cb⟩

#print axioms cm_arguments
#print axioms cm_add_calls
#print axioms cm_sub_calls
#print axioms qm_arguments
#print axioms wide_arguments
#print axioms cm_cross_arguments
end NEI_NEB_FieldDomains

-- Unchanged retained declarations from evidence/slice-q-compose-20261029/NEB_CMCalls.lean
set_option autoImplicit false
namespace NEI_NEB_CMCalls
open Aeneas Aeneas.Std Result AspisR1 NEI_LPi_FieldValues

theorem multiply (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ m0 m1 m2 a b c : U32,
      FIo_Native.aspis_core.field.M31.mul x.a y.a = ok m0 ∧ m0.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul x.b y.b = ok m1 ∧ m1.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.reduce_u64 (NEI_LPi_CMProduct.cross x y) = ok m2 ∧ m2.val < 2147483647 ∧
      (NEI_LPi_CMProduct.cross x y).val=(x.a.val+x.b.val)*(y.a.val+y.b.val) ∧
      FIo_Native.aspis_core.field.M31.sub m0 m1 = ok a ∧ a.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.sub m2 m0 = ok b ∧ b.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.sub b m1 = ok c ∧ c.val < 2147483647 ∧
      FIo_Native.aspis_core.field.CM31.mul x y = ok ⟨a,c⟩ := by
  obtain ⟨m0,h0,_,c0⟩ := NEI_LPf_BaseMultiply.source x.a y.a
  obtain ⟨m1,h1,_,c1⟩ := NEI_LPf_BaseMultiply.source x.b y.b
  obtain ⟨m2,h2,_,c2⟩ := NEI_LPf_CoreReduction.source (NEI_LPi_CMProduct.cross x y)
  have hr : FIo_Native.aspis_core.field.M31.reduce_u64 (NEI_LPi_CMProduct.cross x y) = ok m2 := by
    simp only [FIo_Native.aspis_core.field.M31.reduce_u64,h2,bind_tc_ok]
  obtain ⟨a,ha,_,ca⟩ := NEI_LPi_NatBase.sub m0 m1 c0 c1
  obtain ⟨b,hb,_,cb⟩ := NEI_LPi_NatBase.sub m2 m0 c2 c0
  obtain ⟨c,hc,_,cc⟩ := NEI_LPi_NatBase.sub b m1 cb c1
  refine ⟨m0,m1,m2,a,b,c,h0,c0,h1,c1,hr,c2,NEI_LPi_CMProduct.cross_value x y hx hy,ha,ca,hb,cb,hc,cc,?_⟩
  simp only [FIo_Native.aspis_core.field.CM31.mul,h0,h1,lift,bind_tc_ok]
  change (do let t ← FIo_Native.aspis_core.field.M31.reduce_u64 (NEI_LPi_CMProduct.cross x y)
             let a ← FIo_Native.aspis_core.field.M31.sub m0 m1
             let b ← FIo_Native.aspis_core.field.M31.sub t m0
             let c ← FIo_Native.aspis_core.field.M31.sub b m1
             ok (⟨a,c⟩ : NC)) = _
  simp only [hr,ha,hb,hc,bind_tc_ok]

/-- The mixed-product packet accepts raw words. No canonical precondition is
introduced at either component call. -/
theorem scale (x : NC) (s : U32) :
    ∃ a b,
      FIo_Native.aspis_core.field.M31.mul x.a s = ok a ∧ a.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul x.b s = ok b ∧ b.val < 2147483647 ∧
      FIo_Native.aspis_core.field.CM31.mul_m31 x s = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,_,ca⟩ := NEI_LPf_BaseMultiply.source x.a s
  obtain ⟨b,hb,_,cb⟩ := NEI_LPf_BaseMultiply.source x.b s
  exact ⟨a,b,ha,ca,hb,cb,by
    simp only [FIo_Native.aspis_core.field.CM31.mul_m31,ha,hb,bind_tc_ok]⟩

#print axioms multiply
#print axioms scale
end NEI_NEB_CMCalls

-- Unchanged retained declarations from evidence/slice-q-compose-20261029/NEB_QMCalls.lean
set_option autoImplicit false
namespace NEI_NEB_QMCalls
open Aeneas Aeneas.Std Result AspisR1 NEI_LPi_FieldValues

/-- The selected witnesses are precisely the emitted body's sequential
returns. Every later domain follows from earlier returns, not an inner premise. -/
theorem multiply (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ ac bd a b cross r lo diff hi : NC,
      FIo_Native.aspis_core.field.CM31.mul x.c0 y.c0 = ok ac ∧ canonC ac ∧
      FIo_Native.aspis_core.field.CM31.mul x.c1 y.c1 = ok bd ∧ canonC bd ∧
      FIo_Native.aspis_core.field.CM31.add x.c0 x.c1 = ok a ∧ canonC a ∧
      FIo_Native.aspis_core.field.CM31.add y.c0 y.c1 = ok b ∧ canonC b ∧
      FIo_Native.aspis_core.field.CM31.mul a b = ok cross ∧ canonC cross ∧
      FIo_Native.aspis_core.field.mul_by_r bd = ok r ∧ canonC r ∧
      FIo_Native.aspis_core.field.CM31.add ac r = ok lo ∧ canonC lo ∧
      FIo_Native.aspis_core.field.CM31.sub cross ac = ok diff ∧ canonC diff ∧
      FIo_Native.aspis_core.field.CM31.sub diff bd = ok hi ∧ canonC hi ∧
      FIo_Native.aspis_core.field.QM31.mul x y = ok ⟨lo,hi⟩ := by
  obtain ⟨ac,hac,cac,_⟩ := cm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,_⟩ := cm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,_⟩ := cm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,_⟩ := cm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,_⟩ := cm_mul a b ca cb
  obtain ⟨r,hr,cr,_⟩ := by_r bd cbd
  obtain ⟨lo,hlo,clo,_⟩ := cm_add ac r cac cr
  obtain ⟨diff,hdiff,cdiff,_⟩ := cm_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,_⟩ := cm_sub diff bd cdiff cbd
  exact ⟨ac,bd,a,b,cross,r,lo,diff,hi,hac,cac,hbd,cbd,ha,ca,hb,cb,
    hcross,ccross,hr,cr,hlo,clo,hdiff,cdiff,hhi,chi,by
      simp only [FIo_Native.aspis_core.field.QM31.mul,hac,hbd,ha,hb,hcross,hr,hlo,hdiff,hhi,bind_tc_ok]⟩

theorem add (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ a b : NC,
      FIo_Native.aspis_core.field.CM31.add x.c0 y.c0 = ok a ∧ canonC a ∧
      FIo_Native.aspis_core.field.CM31.add x.c1 y.c1 = ok b ∧ canonC b ∧
      FIo_Native.aspis_core.field.QM31.add x y = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,ca,_⟩ := cm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,_⟩ := cm_add x.c1 y.c1 hx.2 hy.2
  exact ⟨a,b,ha,ca,hb,cb,by simp only [FIo_Native.aspis_core.field.QM31.add,ha,hb,bind_tc_ok]⟩

theorem sub (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ a b : NC,
      FIo_Native.aspis_core.field.CM31.sub x.c0 y.c0 = ok a ∧ canonC a ∧
      FIo_Native.aspis_core.field.CM31.sub x.c1 y.c1 = ok b ∧ canonC b ∧
      FIo_Native.aspis_core.field.QM31.sub x y = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,ca,_⟩ := cm_sub x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,_⟩ := cm_sub x.c1 y.c1 hx.2 hy.2
  exact ⟨a,b,ha,ca,hb,cb,by simp only [FIo_Native.aspis_core.field.QM31.sub,ha,hb,bind_tc_ok]⟩

#print axioms multiply
#print axioms add
#print axioms sub
end NEI_NEB_QMCalls

-- Unchanged retained declarations from evidence/slice-q-compose-20261029/NEB_ByRCalls.lean
set_option autoImplicit false
namespace NEI_NEB_ByRCalls
open Aeneas Aeneas.Std Result AspisR1 NEI_LPi_FieldValues

theorem source (x : NC) (hx : canonC x) :
    ∃ da re db im : U32,
      FIo_Native.aspis_core.field.M31.double x.a = ok da ∧ da.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.sub da x.b = ok re ∧ re.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.double x.b = ok db ∧ db.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.add x.a db = ok im ∧ im.val < 2147483647 ∧
      FIo_Native.aspis_core.field.mul_by_r x = ok ⟨re,im⟩ := by
  obtain ⟨da,ha,_,ca⟩ := NEI_LPi_NatBase.add x.a x.a hx.1 hx.1
  obtain ⟨re,hr,_,cr⟩ := NEI_LPi_NatBase.sub da x.b ca hx.2
  obtain ⟨db,hb,_,cb⟩ := NEI_LPi_NatBase.add x.b x.b hx.2 hx.2
  obtain ⟨im,hi,_,ci⟩ := NEI_LPi_NatBase.add x.a db hx.1 cb
  exact ⟨da,re,db,im,ha,ca,hr,cr,hb,cb,hi,ci,by
    simp only [FIo_Native.aspis_core.field.mul_by_r,FIo_Native.aspis_core.field.M31.double,
      ha,hr,hb,hi,bind_tc_ok]⟩

theorem mul_u (x : NQ) (hx : canonQ x) :
    canonC x.c1 ∧ ∃ r,
      FIo_Native.aspis_core.field.mul_by_r x.c1 = ok r ∧ canonC r ∧
      FIo_Native.aspis_core.field.wide_exact.mul_u x = ok ⟨r,x.c0⟩ ∧
      canonQ (⟨r,x.c0⟩ : NQ) := by
  obtain ⟨r,hr,cr,_⟩ := by_r x.c1 hx.2
  exact ⟨hx.2,r,hr,cr,by
    simp only [FIo_Native.aspis_core.field.wide_exact.mul_u,hr,bind_tc_ok],cr,hx.1⟩
#print axioms source
#print axioms mul_u
end NEI_NEB_ByRCalls

-- Unchanged retained declarations from lean/NBG_WideCarriers.lean
namespace NEI_NBG_WideCarriers
open Aeneas Aeneas.Std Result
theorem remainder (x : U32) : ∃ z, x % 2147483647#u32 = ok z ∧
    z.val = x.val % 2147483647 :=
  WP.spec_imp_exists (UScalar.rem_spec x (y:=2147483647#u32) (by decide))

theorem canonical_qm31 (x : PQ) : ∃ z,
    AspisR1Post25Sampler.field.canonical_qm31 x = ok z ∧ pw z = reduced x := by
  obtain ⟨a,ha,va⟩ := remainder x.c0.a
  obtain ⟨b,hb,vb⟩ := remainder x.c0.b
  obtain ⟨c,hc,vc⟩ := remainder x.c1.a
  obtain ⟨d,hd,vd⟩ := remainder x.c1.b
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,?_,Prod.ext va (Prod.ext vb (Prod.ext vc vd))⟩
  simp only [AspisR1Post25Sampler.field.canonical_qm31,
    AspisR1Post25Sampler.field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    AspisR1Post25Sampler.field.P,ha,hb,hc,hd,bind_tc_ok]

#print axioms remainder
end NEI_NBG_WideCarriers

-- Unchanged retained declarations from evidence/slice-q-compose-20261029/NEB_WideCalls.lean
set_option autoImplicit false
namespace NEI_NEB_WideCalls
open Aeneas Aeneas.Std Result AspisR1 NEI_LPi_FieldValues

theorem multiply (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ ac bd a b cross r lo diff hi : NQ,
      FIo_Native.aspis_core.field.QM31.mul x.c0 y.c0 = ok ac ∧ canonQ ac ∧
      FIo_Native.aspis_core.field.QM31.mul x.c1 y.c1 = ok bd ∧ canonQ bd ∧
      FIo_Native.aspis_core.field.QM31.add x.c0 x.c1 = ok a ∧ canonQ a ∧
      FIo_Native.aspis_core.field.QM31.add y.c0 y.c1 = ok b ∧ canonQ b ∧
      FIo_Native.aspis_core.field.QM31.mul a b = ok cross ∧ canonQ cross ∧
      FIo_Native.aspis_core.field.wide_exact.mul_u bd = ok r ∧ canonQ r ∧
      FIo_Native.aspis_core.field.QM31.add ac r = ok lo ∧ canonQ lo ∧
      FIo_Native.aspis_core.field.QM31.sub cross ac = ok diff ∧ canonQ diff ∧
      FIo_Native.aspis_core.field.QM31.sub diff bd = ok hi ∧ canonQ hi ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y = ok ⟨lo,hi⟩ := by
  obtain ⟨ac,hac,cac,_⟩ := NEI_LPi_TowerValues.qm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,_⟩ := NEI_LPi_TowerValues.qm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,_⟩ := NEI_LPi_TowerValues.qm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,_⟩ := NEI_LPi_TowerValues.qm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,_⟩ := NEI_LPi_TowerValues.qm_mul a b ca cb
  obtain ⟨r,hr,cr,_⟩ := NEI_LPi_TowerValues.mul_u bd cbd
  obtain ⟨lo,hlo,clo,_⟩ := NEI_LPi_TowerValues.qm_add ac r cac cr
  obtain ⟨diff,hdiff,cdiff,_⟩ := NEI_LPi_TowerValues.qm_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,_⟩ := NEI_LPi_TowerValues.qm_sub diff bd cdiff cbd
  exact ⟨ac,bd,a,b,cross,r,lo,diff,hi,hac,cac,hbd,cbd,ha,ca,hb,cb,
    hcross,ccross,hr,cr,hlo,clo,hdiff,cdiff,hhi,chi,by
      simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul,hac,hbd,ha,hb,hcross,hr,hlo,hdiff,hhi,bind_tc_ok]⟩

theorem scale (x : NE) (s : U32) :
    ∃ rhs a b,
      s % 2147483647#u32 = ok rhs ∧ rhs.val < 2147483647 ∧
      FIo_Native.aspis_core.field.QM31.mul_m31 x.c0 rhs = ok a ∧ canonQ a ∧
      FIo_Native.aspis_core.field.QM31.mul_m31 x.c1 rhs = ok b ∧ canonQ b ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x s = ok ⟨a,b⟩ := by
  obtain ⟨rhs,hr,vr⟩ := NEI_NBG_WideCarriers.remainder s
  have cr : rhs.val < 2147483647 := by rw [vr]; exact Nat.mod_lt _ (by decide)
  obtain ⟨a,ha,ca,_⟩ := NEI_LPi_MixedValues.qm_m31 x.c0 rhs
  obtain ⟨b,hb,cb,_⟩ := NEI_LPi_MixedValues.qm_m31 x.c1 rhs
  exact ⟨rhs,a,b,hr,cr,ha,ca,hb,cb,by
    simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31,
      FIo_Native.aspis_core.field.P,hr,ha,hb,bind_tc_ok]⟩

#print axioms multiply
#print axioms scale
end NEI_NEB_WideCalls

-- Unchanged retained declarations from evidence/slice-q-compose-20261029/NEB_AdditiveCalls.lean
set_option autoImplicit false
namespace NEI_NEB_AdditiveCalls
open Aeneas Aeneas.Std Result AspisR1 NEI_LPi_FieldValues

theorem wide_add (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ a b,
      FIo_Native.aspis_core.field.QM31.add x.c0 y.c0 = ok a ∧ canonQ a ∧
      FIo_Native.aspis_core.field.QM31.add x.c1 y.c1 = ok b ∧ canonQ b ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.add x y = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,ca,_⟩ := NEI_LPi_TowerValues.qm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,_⟩ := NEI_LPi_TowerValues.qm_add x.c1 y.c1 hx.2 hy.2
  exact ⟨a,b,ha,ca,hb,cb,by simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,ha,hb,bind_tc_ok]⟩

theorem qm_scale (x : NQ) (s : U32) :
    ∃ a b,
      FIo_Native.aspis_core.field.CM31.mul_m31 x.c0 s = ok a ∧ canonC a ∧
      FIo_Native.aspis_core.field.CM31.mul_m31 x.c1 s = ok b ∧ canonC b ∧
      FIo_Native.aspis_core.field.QM31.mul_m31 x s = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,ca,_⟩ := NEI_LPi_MixedValues.cm_m31 x.c0 s
  obtain ⟨b,hb,cb,_⟩ := NEI_LPi_MixedValues.cm_m31 x.c1 s
  exact ⟨a,b,ha,ca,hb,cb,by simp only [FIo_Native.aspis_core.field.QM31.mul_m31,ha,hb,bind_tc_ok]⟩

/-- Both double callers pass the same canonical value twice. -/
theorem double_arguments (x : NC) (hx : canonC x) :
    canonC x ∧ canonC x ∧
    FIo_Native.aspis_core.field.CM31.double x = FIo_Native.aspis_core.field.CM31.add x x :=
  ⟨hx,hx,rfl⟩

theorem base_double_arguments (x : U32) (hx : x.val<2147483647) :
    x.val<2147483647 ∧ x.val<2147483647 ∧
    FIo_Native.aspis_core.field.M31.double x = FIo_Native.aspis_core.field.M31.add x x :=
  ⟨hx,hx,rfl⟩

#print axioms wide_add
#print axioms qm_scale
#print axioms double_arguments
#print axioms base_double_arguments
end NEI_NEB_AdditiveCalls

-- Unchanged retained declarations from evidence/slice-q-compose-20261029/NEB_CMCarrier.lean
set_option autoImplicit false
namespace NEI_NEB_CMCarrier
open Aeneas Aeneas.Std Result AspisR1 NEI_LPi_FieldValues

theorem lossless (x : U32) :
    (core.convert.num.FromU64U32.from x).val=x.val := by scalar_tac

/-- The four actual u64::from arguments in the frozen complex product body. -/
theorem actual_casts (x y : NC) :
    (core.convert.num.FromU64U32.from x.a).val=x.a.val ∧
    (core.convert.num.FromU64U32.from x.b).val=x.b.val ∧
    (core.convert.num.FromU64U32.from y.a).val=y.a.val ∧
    (core.convert.num.FromU64U32.from y.b).val=y.b.val :=
  ⟨lossless _,lossless _,lossless _,lossless _⟩

#print axioms lossless
#print axioms actual_casts
end NEI_NEB_CMCarrier

-- Unchanged retained declarations from evidence/slice-q-compose-20261029/NEB_NativeFieldScalars.lean
set_option autoImplicit false
namespace NEI_NEB_NativeFieldScalars
open Aeneas Aeneas.Std Result AspisR1 NEI_LPi_FieldValues

theorem size64 : UScalar.size .U64=18446744073709551616 := by
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]

theorem sum_checked (x : NC) :
    (core.convert.num.FromU64U32.from x.a)+(core.convert.num.FromU64U32.from x.b)=
      ok (NEI_LPi_CMProduct.sum x) := by
  apply FIo_ScalarBridge.add
  rw [NEI_NEB_CMCarrier.lossless,NEI_NEB_CMCarrier.lossless,size64]
  have a : x.a.val<4294967296 := by scalar_tac
  have b : x.b.val<4294967296 := by scalar_tac
  change x.a.val+x.b.val<18446744073709551616
  omega

/-- This is the checked scalar expression in the ACTUAL frozen caller; its
sums and product equal the emitted raw recurrence input without overflow. -/
theorem cross_checked (x y : NC) (hx : canonC x) (hy : canonC y) :
    (do
      let a ← (core.convert.num.FromU64U32.from x.a)+(core.convert.num.FromU64U32.from x.b)
      let b ← (core.convert.num.FromU64U32.from y.a)+(core.convert.num.FromU64U32.from y.b)
      a*b)=ok (NEI_LPi_CMProduct.cross x y) := by
  rw [sum_checked x,sum_checked y]
  simp only [bind_tc_ok]
  apply FIo_ScalarBridge.mul
  rw [NEI_LPi_CMProduct.sum_value,NEI_LPi_CMProduct.sum_value,size64]
  have a : x.a.val+x.b.val<4294967296 := by rcases hx with ⟨_,_⟩;omega
  have b : y.a.val+y.b.val<4294967296 := by rcases hy with ⟨_,_⟩;omega
  exact Nat.mul_lt_mul_of_lt_of_lt a b

#print axioms size64
#print axioms sum_checked
#print axioms cross_checked
end NEI_NEB_NativeFieldScalars

end
