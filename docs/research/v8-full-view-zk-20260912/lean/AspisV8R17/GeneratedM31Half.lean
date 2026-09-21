import AspisV8R17.SignedLiteralSupport
import AspisV8R17.GeneratedReducerExpanded
import AspisV8R17.HalfRotateNat

namespace Aeneas.Std
-- SOURCE Bitwise.lean
instance {ty0 ty1} : HShiftLeft (UScalar ty0) (IScalar ty1) (Result (UScalar ty0)) where
  hShiftLeft x y := UScalar.shiftLeft_IScalar x y
-- END SOURCE

-- SOURCE Bitwise.lean
instance {ty0 ty1} : HShiftRight (UScalar ty0) (IScalar ty1) (Result (UScalar ty0)) where
  hShiftRight x y := UScalar.shiftRight_IScalar x y
-- END SOURCE

-- SOURCE Bitwise.lean
instance {ty} : HOr (UScalar ty) (UScalar ty) (UScalar ty) where
  hOr x y := UScalar.or x y
-- END SOURCE
end Aeneas.Std

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- EXPANDED GENERATED FunsChunk06.lean
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::half"]
def aspis_core.field.M31.half
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  let i ← self >>> (I32.ofInt 1)
  let i1 ← lift (self &&& (U32.ofNat 1))
  let i2 ← i1 <<< (I32.ofInt 30)
  let i3 ← lift (i ||| i2)
  ok i3
-- END EXPANDED GENERATED

-- EXPANDED GENERATED FunsChunk06.lean
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::half"]
def aspis_core.field.CM31.half
  (self : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let m ← aspis_core.field.M31.half self.a
  let m1 ← aspis_core.field.M31.half self.b
  ok { a := m, b := m1 }
-- END EXPANDED GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedM31Half
open Aeneas.Std V7Tag73CurrentHelpersOpaque AspisV8.LineNorm
open SignedShiftSlice SignedLiteralSupport UnsignedReducerOps

theorem generated_half_word (x : aspis_core.field.M31) (hx : x.val < p) :
    ∃ z, aspis_core.field.M31.half x = .ok z ∧
      z.val = halfWord x.val ∧ z.val < p ∧ (2*z.val)%p=x.val := by
  obtain ⟨r, hr, vr⟩ := right_success x (I32.ofInt 1) (by decide) (by decide)
  obtain ⟨l, hl, vl⟩ := left_success (UScalar.and x (U32.ofNat 1))
    (I32.ofInt 30) (by decide) (by decide)
  rw [one_toNat] at vr
  rw [thirty_toNat, and_value] at vl
  change l.val = ((x.val &&& 1) <<< 30) % 2^32 at vl
  rw [Nat.mod_eq_of_lt (half_word_ranges x.val hx).2.1] at vl
  have vz : (UScalar.or r l).val = halfWord x.val := by
    rw [or_value, vr, vl]
    rfl
  refine ⟨UScalar.or r l, ?_, vz, ?_, ?_⟩
  · simp only [aspis_core.field.M31.half, HShiftRight.hShiftRight,
      HShiftLeft.hShiftLeft, HAnd.hAnd, HOr.hOr, hr, hl, lift, bind_tc_ok]
  · rw [vz]
    exact (half_range_and_double x.val hx).1
  · rw [vz]
    exact half_double_mod x.val hx

theorem generated_cm31_half_words (x : aspis_core.field.CM31)
    (ha : x.a.val < p) (hb : x.b.val < p) :
    ∃ z, aspis_core.field.CM31.half x = .ok z ∧
      z.a.val = halfWord x.a.val ∧ z.b.val = halfWord x.b.val ∧
      z.a.val < p ∧ z.b.val < p ∧
      (2*z.a.val)%p=x.a.val ∧ (2*z.b.val)%p=x.b.val := by
  obtain ⟨a, hea, va, hca, hda⟩ := generated_half_word x.a ha
  obtain ⟨b, heb, vb, hcb, hdb⟩ := generated_half_word x.b hb
  exact ⟨⟨a,b⟩, by simp only [aspis_core.field.CM31.half, hea, heb, bind_tc_ok],
    va, vb, hca, hcb, hda, hdb⟩

#print axioms generated_half_word
#print axioms generated_cm31_half_words
end AspisV8R17.GeneratedM31Half
