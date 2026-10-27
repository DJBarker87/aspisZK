import FIo_NativeFuns
import FIo_ReduceBounds
import FIo_ScalarBridge
set_option autoImplicit false
namespace AspisR1.LPn_Extend
open Aeneas Aeneas.Std Result
theorem extend (x : U32) : (core.convert.num.FromU64U32.from x).val=x.val := by
  change (BitVec.setWidth UScalarTy.U64.numBits x.bv).toNat=x.bv.toNat
  rw [BitVec.toNat_setWidth]
  apply Nat.mod_eq_of_lt
  have h:=x.hSize
  norm_num [UScalar.size,U32.size,U32.numBits,UScalarTy.numBits,U64.numBits] at h ⊢
  omega


#print axioms extend
end AspisR1.LPn_Extend

namespace AspisR1.LPn_FoldLane
open Aeneas Aeneas.Std Result
def R : Nat := 10737418238

theorem shift (x : U64) : x >>> 31#i32=ok (U64.wrapping_shr x 31#u32) := by rfl

theorem fold_bound (x : U64) : (FIo_ReduceBounds.fold x).val≤R := by
  unfold FIo_ReduceBounds.fold
  unfold U64.wrapping_add
  rw [UScalar.wrapping_add_val_eq,Nat.mod_eq_of_lt (FIo_ReduceBounds.sum_bound x)]
  have a:=FIo_ReduceFacts.low x
  have b:=FIo_ReduceBounds.shr_bound x
  unfold R
  omega


#print axioms shift
#print axioms fold_bound
end AspisR1.LPn_FoldLane

set_option autoImplicit false
namespace AspisR1.LPn_FoldValue
open Aeneas Aeneas.Std

def value (n : Nat) : Nat := n%2147483648+n/2147483648

theorem low (x : U64) : (x &&& 2147483647#u64).val=x.val%2147483648 := by
  change (x.bv &&& (2147483647 : BitVec 64)).toNat=x.val%2147483648
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.val 31

theorem source (x : U64) : (FIo_ReduceBounds.fold x).val=value x.val := by
  unfold FIo_ReduceBounds.fold U64.wrapping_add
  rw [UScalar.wrapping_add_val_eq,Nat.mod_eq_of_lt (FIo_ReduceBounds.sum_bound x),
    low,FIo_ReduceBounds.shr_val]
  rfl

#print axioms low
#print axioms source
end AspisR1.LPn_FoldValue

set_option autoImplicit false
namespace AspisR1.LPn_RawMath
open Aeneas Aeneas.Std Result
abbrev extend (x : U32) : U64 := core.convert.num.FromU64U32.from x

theorem mul (a b : U32) : extend a*extend b=ok (UScalar.wrapping_mul (extend a) (extend b)) := by
  apply FIo_ScalarBridge.mul
  rw [LPn_Extend.extend,LPn_Extend.extend]
  have ha:=a.hSize
  have hb:=b.hSize
  norm_num [UScalar.size,U32.size,U32.numBits,U64.size,U64.numBits,UScalarTy.numBits] at ha hb ⊢
  nlinarith

theorem fold (x : U64) :
    FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () x=
      ok (FIo_ReduceBounds.fold x) := by
  simp only [FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call,
    FIo_QRaw.canonical.P,lift,bind_tc_ok,LPn_FoldLane.shift]
  rfl

theorem twice_fold (x : U64) : 2#u64*FIo_ReduceBounds.fold x=
    ok (UScalar.wrapping_mul 2#u64 (FIo_ReduceBounds.fold x)) := by
  apply FIo_ScalarBridge.mul
  have h:=LPn_FoldLane.fold_bound x
  norm_num [LPn_FoldLane.R,UScalar.size,U64.size,U64.numBits,UScalarTy.numBits] at h ⊢
  omega

theorem pp : FIo_QRaw.canonical.Q.raw.PP=ok 4611686014132420609#u64 := by
  unfold FIo_QRaw.canonical.Q.raw.PP FIo_QRaw.canonical.P
  rfl

theorem twice_pp : 2#u64*4611686014132420609#u64=ok 9223372028264841218#u64 := by rfl

theorem triple_p : 3#u64*extend FIo_QRaw.canonical.P=ok 6442450941#u64 := by
  unfold FIo_QRaw.canonical.P
  rfl

#print axioms mul
#print axioms fold
#print axioms twice_fold
#print axioms pp
#print axioms twice_pp
#print axioms triple_p
end AspisR1.LPn_RawMath

set_option autoImplicit false
noncomputable section
namespace AspisR1.LPn_RawMap
open Aeneas Aeneas.Std Result

def pack {α : Type} (a b c d : α) : Array α 4#usize := Array.make 4#usize [a,b,c,d]

theorem left (a b c d : U32) : core.array.Array.map
    FIo_QRaw.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 (pack a b c d) ()=
      ok (pack (LPn_RawMath.extend a) (LPn_RawMath.extend b)
        (LPn_RawMath.extend c) (LPn_RawMath.extend d)) := by rfl

theorem right (a b c d : U32) : core.array.Array.map
    FIo_QRaw.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 (pack a b c d) ()=
      ok (pack (LPn_RawMath.extend a) (LPn_RawMath.extend b)
        (LPn_RawMath.extend c) (LPn_RawMath.extend d)) := by rfl

theorem shape {α : Type} (xs : Array α 4#usize) : ∃ a b c d, xs=pack a b c d := by
  rcases xs with ⟨xs,h⟩
  change xs.length=4 at h
  cases xs with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      cases xs with
      | nil => simp at h
      | cons c xs =>
        cases xs with
        | nil => simp at h
        | cons d xs =>
          cases xs with
          | nil => exact ⟨a,b,c,d,rfl⟩
          | cons e xs => simp at h

#print axioms left
#print axioms right
#print axioms shape
end AspisR1.LPn_RawMap
end

set_option autoImplicit false
namespace AspisR1.LPn_RawReference
open Aeneas Aeneas.Std Result
open LPn_RawMath (extend)
open LPn_RawMap (pack)
abbrev add := U64.wrapping_add
abbrev sub := U64.wrapping_sub
abbrev mul := U64.wrapping_mul

def product (a b : U32) : U64 := mul (extend a) (extend b)
def u (c d g h : U32) : U64 :=
  FIo_ReduceBounds.fold (sub (add (product c g) 4611686014132420609#u64) (product d h))
def v (c d g h : U32) : U64 := FIo_ReduceBounds.fold (add (product c h) (product d g))
def raw0 (a b c d e f g h : U32) : U64 :=
  sub (add (add (sub (add (product a e) 4611686014132420609#u64) (product b f))
    (mul 2#u64 (u c d g h))) 6442450941#u64) (v c d g h)
def raw1 (a b c d e f g h : U32) : U64 :=
  add (add (add (product a f) (product b e)) (u c d g h)) (mul 2#u64 (v c d g h))
def raw2 (a b c d e f g h : U32) : U64 :=
  sub (sub (add (add (product a g) (product c e)) 9223372028264841218#u64) (product b h)) (product d f)
def raw3 (a b c d e f g h : U32) : U64 :=
  add (add (add (product a h) (product b g)) (product c f)) (product d e)

theorem source (a b c d e f g h : U32) :
    FIo_Native.fast_pairing.canonical.Q.raw (pack a b c d) (pack e f g h)=
      ok (pack (raw0 a b c d e f g h) (raw1 a b c d e f g h)
        (raw2 a b c d e f g h) (raw3 a b c d e f g h)) := by
  have r0 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 0#usize=ok (extend a) := rfl
  have r1 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 1#usize=ok (extend b) := rfl
  have r2 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 2#usize=ok (extend c) := rfl
  have r3 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 3#usize=ok (extend d) := rfl
  have r4 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 0#usize=ok (extend e) := rfl
  have r5 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 1#usize=ok (extend f) := rfl
  have r6 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 2#usize=ok (extend g) := rfl
  have r7 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 3#usize=ok (extend h) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [LPn_RawMap.left,LPn_RawMap.right,bind_tc_ok,r0,r1,r2,r3,r4,r5,r6,r7,
    LPn_RawMath.mul,LPn_RawMath.pp,LPn_RawMath.fold,LPn_RawMath.twice_fold,
    LPn_RawMath.twice_pp,LPn_RawMath.triple_p,lift]
  rfl
#print axioms source
end AspisR1.LPn_RawReference

namespace AspisR1.LPn_RawArithmetic
open Aeneas Aeneas.Std Result
open LPn_RawReference
theorem product_value (a b : U32) : (product a b).val=a.val*b.val := by
  unfold product
  rw [U64.wrapping_mul_val_eq,LPn_Extend.extend,LPn_Extend.extend]
  have ha := a.hSize
  have hb := b.hSize
  apply Nat.mod_eq_of_lt
  norm_num [UScalar.size,UScalarTy.numBits,U32.size,U32.numBits,U64.size,U64.numBits] at ha hb ⊢
  nlinarith


#print axioms product_value
end AspisR1.LPn_RawArithmetic
