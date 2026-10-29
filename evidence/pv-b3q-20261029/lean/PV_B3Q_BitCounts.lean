import PV_B3P_ClosureLinks14227
namespace PV_B3Q_BitCounts
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
def bits (mask : U16) : BitVec 16 := BitVec.ofNat 16 mask.val
def word (x : BitVec 16) : U32 :=
 UScalar.cast .U32 (U16.ofNatCore x.toNat x.isLt)
attribute [local irreducible] BitVec.ctz BitVec.cpop

theorem bits_value (mask : U16) : (bits mask).toNat = mask.val := by
 rw [bits,BitVec.toNat_ofNat]
 exact Nat.mod_eq_of_lt mask.hBounds

theorem word_value (x : BitVec 16) : (word x).val = x.toNat := by
 simp only [word,UScalar.cast_val_eq]
 change x.toNat % (2^32) = x.toNat
 exact Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide : 2^16 < 2^32))

theorem bits_nonzero (mask : U16) (nonzero : mask ≠ 0#u16) : bits mask ≠ 0#16 := by
 intro zero
 have same := congrArg BitVec.toNat zero
 rw [bits_value] at same
 apply nonzero
 apply UScalar.eq_of_val_eq
 exact same

def trailing_zeros (mask : U16) : Result U32 := .ok (word (bits mask).ctz)
def count_ones (mask : U16) : Result U32 := .ok (word (bits mask).cpop)

theorem trailing_index_bound (mask : U16) (nonzero : mask ≠ 0#u16) :
    (word (bits mask).ctz).val < 16 := by
 rw [word_value]
 have bound := BitVec.ctz_lt_iff_ne_zero.mpr (bits_nonzero mask nonzero)
 simpa only [BitVec.lt_def,BitVec.toNat_ofNat] using bound

theorem population_bound (mask : U16) : (word (bits mask).cpop).val ≤ 16 := by
 rw [word_value]
 exact BitVec.toNat_cpop_le (bits mask)

theorem native_cast_index_bound (mask : U16) (nonzero : mask ≠ 0#u16) :
    (UScalar.cast .Usize (word (bits mask).ctz)).val < 16 := by
 rw [UScalar.cast_val_eq]
 exact lt_of_le_of_lt (Nat.mod_le _ _) (trailing_index_bound mask nonzero)

inductive Body where | trailing | population
def Signature : Body → Type := fun _ => U16 → Result U32
def source : (body : Body) → Signature body
 | .trailing => trailing_zeros
 | .population => count_ones
def model : (body : Body) → Signature body
 | .trailing => fun mask => lift (word (bits mask).ctz)
 | .population => fun mask => lift (word (bits mask).cpop)
/-- Source wrappers return the compiler intrinsic value unchanged. Executing
cttz/ctpop remains the named V370 / D381,D386 boundary. -/
theorem wrappers_link : PV_B3P_Link_std_dependency_closure14 Signature source model := by
 intro body
 cases body <;> rfl
#print axioms bits_value
#print axioms word_value
#print axioms bits_nonzero
#print axioms trailing_index_bound
#print axioms population_bound
#print axioms native_cast_index_bound
#print axioms wrappers_link
end PV_B3Q_BitCounts
