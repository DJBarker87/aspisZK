/- Mechanically reused R70/R71 proof script for the actual R72 closure.
Only identifier renaming and removal of the absent diagnostic-probe corollary.
Checked by tools/generate_r78_closure.py; original files are preserved. -/
import AspisR72Sampler.Funs
import AspisV8R19.QuarticBaseExecution
import AspisV8R19.PartialDot

/-! Symbolic U64 operations for the exact R69 generated product. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerClosureExplicitWord
open Aeneas Aeneas.Std Result AspisR72Sampler
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase encodeBase_val)

def word (n : Nat) : U64 := ⟨BitVec.ofNat 64 n⟩

theorem word_val (n : Nat) (h : n < 2^64) : (word n).val = n :=
  Nat.mod_eq_of_lt h

theorem word_add (a b : Nat) :
    core.num.U64.wrapping_add (word a) (word b) = word (a+b) := by
  change (⟨BitVec.ofNat 64 a + BitVec.ofNat 64 b⟩ : U64) = word (a+b)
  rw [BitVec.ofNat_add_ofNat]
  rfl

theorem word_sub (a b : Nat) (hb : b < 2^64) (hle : b ≤ a) :
    core.num.U64.wrapping_sub (word a) (word b) = word (a-b) := by
  change (⟨BitVec.ofNat 64 a - BitVec.ofNat 64 b⟩ : U64) = word (a-b)
  rw [BitVec.ofNat_sub_ofNat_of_le a b hb hle]
  rfl

theorem word_mul (a b : Nat) (ha : a < 2^64) (hb : b < 2^64)
    (hab : a*b < 2^64) : (word a * word b : Result U64) = .ok (word (a*b)) := by
  obtain ⟨z,hz,hv⟩ := InverseRuntimeMul.mul_success (word a) (word b)
    (by rw [word_val a ha,word_val b hb]; exact hab)
  have he : z = word (a*b) := by
    apply UScalar.eq_of_val_eq
    rw [hv,word_val a ha,word_val b hb,word_val (a*b) hab]
  rw [he] at hz
  exact hz

theorem widen_encode (x : M31Exact) :
    UScalar.cast .U64 (encodeBase x) = word x.val := by
  apply UScalar.eq_of_val_eq
  rw [InverseRuntimeMul.cast_widen_value,encodeBase_val,word_val]
  have hx := ZMod.val_lt x
  unfold P at hx
  omega

theorem prime_word : UScalar.cast .U64 field.P = word P := by simp only [field.P]; rfl
theorem prime_from : core.convert.num.FromU64U32.from field.P = word P := by simp only [field.P]; rfl
theorem two_word : (2#u64 : U64) = word 2 := rfl
theorem three_word : (3#u64 : U64) = word 3 := rfl

theorem pp_word : field.r24_canonical_mul.PP = .ok (word (P*P)) := by
  simp only [field.r24_canonical_mul.PP,lift,bind_tc_ok,prime_word]
  exact word_mul P P (by decide) (by decide) (by decide)

theorem reduce_word (n : Nat) (hn : n < 2^64) :
    field.M31.reduce_u64 (word n) = .ok (encodeBase (n : M31Exact)) := by
  have he : field.M31.reduce_u64 (word n) = AspisR66Field.field.M31.reduce_u64 (word n) := by
    simp only [field.M31.reduce_u64,AspisR66Field.field.M31.reduce_u64,
      field.reduce_u64,AspisR66Field.field.reduce_u64,field.P,AspisR66Field.field.P]
  rw [he,QuarticBaseExecution.reduce_encode,word_val n hn]

theorem partial_execution (x : U64) :
    field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call () x =
      .ok (word (PartialProduct.foldOnce x.val)) := by
  obtain ⟨high,hs,hv⟩ := InverseRuntimeMul.shift_success x 31 (by decide)
  have hs' : (x >>> 31#i32 : Result U64) = .ok high := hs
  have hm : (UScalar.and x (word P)).val = x.val &&& P := by
    rw [InverseRuntimeMul.and_value,word_val P (by decide)]
  have hfold := PartialDot.word_fold_bound x.val x.bv.isLt
  have he : core.num.U64.wrapping_add (UScalar.and x (word P)) high =
      word (PartialProduct.foldOnce x.val) := by
    apply UScalar.eq_of_val_eq
    rw [core.num.U64.wrapping_add_val_eq,hm,hv]
    rw [UScalar.size]
    change ((x.val &&& PartialProduct.p)+(x.val >>> 31)) % 2^64 = _
    rw [PartialProduct.source_fold,word_val _ (by omega),Nat.mod_eq_of_lt (by omega)]
  simp only [field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call,
    prime_from,lift,bind_tc_ok,hs']
  exact congrArg Result.ok he

theorem partial_word (n : Nat) (hn : n < 2^64) :
    field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call () (word n) =
      .ok (word (PartialProduct.foldOnce n)) := by
  rw [partial_execution,word_val n hn]

#print axioms word_val
#print axioms word_add
#print axioms word_sub
#print axioms word_mul
#print axioms widen_encode
#print axioms prime_word
#print axioms prime_from
#print axioms two_word
#print axioms three_word
#print axioms pp_word
#print axioms reduce_word
#print axioms partial_execution
#print axioms partial_word
end AspisV8R19.SamplerClosureExplicitWord
