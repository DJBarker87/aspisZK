import AspisV8R19.R486ParserCanonicalMask

/-! Bridge the parser mask invariant to pinned Aeneas unsigned scalar OR,
wrapping-add, and checked shift primitives. The parser's iteration and memory
operations are not proved by this arithmetic bridge. -/
set_option autoImplicit false
namespace AspisV8R19.R487ParserScalarMask
open Aeneas Aeneas.Std
open AspisV8R19.R486ParserCanonicalMask

def scalarStep (mask word : U32) : U32 :=
  UScalar.or mask (UScalar.or word (core.num.U32.wrapping_add word 1#u32))

def scalarAccumulated (mask : U32) (words : List U32) : U32 :=
  words.foldl scalarStep mask

theorem scalarStep_bv (mask word : U32) :
    (scalarStep mask word).bv = step mask.bv word.bv := rfl

theorem scalarAccumulated_bv (mask : U32) (words : List U32) :
    (scalarAccumulated mask words).bv = accumulated mask.bv (words.map UScalar.bv) := by
  induction words generalizing mask with
  | nil => rfl
  | cons head tail ih =>
      change (scalarAccumulated (scalarStep mask head) tail).bv = _
      rw [ih, scalarStep_bv]
      rfl

theorem canonical_scalar (word : U32) : canonical word.bv ↔ word.val < 2147483647 := by
  rfl

theorem scalarShift_exact (mask : U32) :
    UScalar.shiftRight mask 31 = .ok ⟨mask.bv >>> (31 : Nat)⟩ := rfl

theorem scalarShift_accepts (mask : U32) :
    UScalar.shiftRight mask 31 = .ok 0#u32 ↔ accepted mask.bv := by
  rw [scalarShift_exact]
  change (Aeneas.Result.ok (UScalar.mk (mask.bv >>> (31 : Nat))) =
    Aeneas.Result.ok (UScalar.mk 0#32)) ↔ mask.bv >>> (31 : Nat) = 0#32
  simp only [Result.ok.injEq, UScalar.mk.injEq]

theorem scalar_mask_complete (words : List U32) :
    UScalar.shiftRight (scalarAccumulated 0#u32 words) 31 = .ok 0#u32 ↔
      ∀ word ∈ words, word.val < 2147483647 := by
  rw [scalarShift_accepts, scalarAccumulated_bv, complete_mask]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    canonical_scalar]

#print axioms scalarStep
#print axioms scalarAccumulated
#print axioms scalarStep_bv
#print axioms scalarAccumulated_bv
#print axioms canonical_scalar
#print axioms scalarShift_exact
#print axioms scalarShift_accepts
#print axioms scalar_mask_complete
end AspisV8R19.R487ParserScalarMask
