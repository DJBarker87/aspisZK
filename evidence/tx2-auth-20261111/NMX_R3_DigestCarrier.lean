import NMX_R3_DigestWords
set_option autoImplicit false
namespace NMX_R3_DigestCarrier
open Aeneas Aeneas.Std NMX_R3_ByteCarrier NMX_R3_DigestWords

theorem limb_value (b : Slice U8) (s k : Nat) :
 word (limb b s k) = NMX_R3_WordRead.valueAt b (s+4*k) := by
 exact NMX_R3_Word32.fixed _ _ _ _

def words (b : Slice U8) (s : Nat) : List UInt32 :=
 (List.range 8).map (fun k => NMX_R3_WordRead.valueAt b (s+4*k))

theorem words_exact (b : Slice U8) (s : Nat) :
 (target b s).val.map word = words b s := by
 apply List.ext_getElem
 · simp only [target, words, List.length_map, List.length_ofFn, List.length_range]
 · intro i hi hj
   simp only [target, words, List.getElem_map, List.getElem_ofFn, List.getElem_range]
   exact limb_value b s i

theorem canonical_limb (x : U32) : word x < RSL.P31 ↔ x.val < 2147483647 := by
 change (word x).toNat < 2147483647 ↔ x.val < 2147483647
 rw [NMX_R3_ByteCarrier.word_value]
#print axioms limb_value
#print axioms words_exact
#print axioms canonical_limb
end NMX_R3_DigestCarrier
