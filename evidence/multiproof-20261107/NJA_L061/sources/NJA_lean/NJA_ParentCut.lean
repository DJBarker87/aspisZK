import NJA_ParentAddress

set_option autoImplicit false
namespace NJA_ParentCut
open Aeneas Aeneas.Std
abbrev Digest := Array U8 32#usize

def byte (d : Digest) (k : Fin 32) : U8 := d.val[k.val]'(by have h : d.val.length = 32 := d.property; exact h ▸ k.isLt)

-- These are the coordinate assertions of K066/K068, universally closed over k.
-- No digest or model endpoint equality is a field of this cut.
structure Cut (left right reply out : Digest) where
  calls : Nat
  calls_one : calls = 1
  parts_len : Nat
  parts_three : parts_len = 3
  tag_len : Nat
  tag_one : tag_len = 1
  tag : U8
  tag_value : tag = 18#u8
  recorded_left : Digest
  recorded_right : Digest
  left_bytes : ∀ k, byte recorded_left k = byte left k
  right_bytes : ∀ k, byte recorded_right k = byte right k
  reply_bytes : ∀ k, byte out k = byte reply k

theorem ext (a b : Digest) (h : ∀ k, byte a k = byte b k) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.trans b.property.symm
  · intro i hi hb
    exact h ⟨i,by have ha : a.val.length = 32 := a.property;omega⟩

theorem arguments (l r reply out : Digest) (c : Cut l r reply out) :
    c.recorded_left = l ∧ c.recorded_right = r :=
  ⟨ext _ _ c.left_bytes,ext _ _ c.right_bytes⟩

theorem reply_unchanged (l r reply out : Digest) (c : Cut l r reply out) : out = reply :=
  ext _ _ c.reply_bytes

theorem address (l r reply out : Digest) (c : Cut l r reply out) :
    AspisR1.MultiproofConePhysicalDigest.parts c.recorded_left c.recorded_right =
      AspisR1.MultiproofConePhysicalDigest.parts l r := by
  rw [(arguments l r reply out c).1,(arguments l r reply out c).2]

-- Caller-established occupied/sibling index domains; no success premise.
theorem occupied_domain (n i : Nat) (hn : n ≤ 16) (active : i < n)
    (occupied : i+1 < n) : i < 16 ∧ i+1 < 16 := by omega

theorem sibling_domain (n i : Nat) (hn : n ≤ 16) (active : i < n) : i < 16 := by omega

#print axioms ext
#print axioms arguments
#print axioms reply_unchanged
#print axioms address
#print axioms occupied_domain
#print axioms sibling_domain
end NJA_ParentCut
