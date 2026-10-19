import BinMerkleLeafRecovery
import Mathlib.Data.List.Basic

/-! Mirrors `MerkleLeafCodec.lean`; see design/BIN-COMMITMENT-MODEL-20261019.md for line pins.
 Constructive parser for the fixed tagged Merkle leaf byte grammar. -/
set_option autoImplicit false
namespace AspisR1.BinMerkleLeafCodec

abbrev Byte := AspisR1.BinMerkle32Path.Byte
abbrev LeafData := AspisR1.BinMerkleLeafRecovery.LeafData

def parse (tag : Byte) (w : Nat) (input : List Byte) : Option LeafData :=
  let data := (input.drop 2 |>.take w, input.drop (2 + w))
  if data.1.length = w ∧ data.2.length = 32 ∧
      AspisR1.BinMerkle32Leaf.leafInput tag data.1 data.2 = input then
    some data
  else none

theorem parse_leafInput (tag : Byte) (packed salt : List Byte) (w : Nat)
    (hpacked : packed.length = w) (hsalt : salt.length = 32) :
    parse tag w (AspisR1.BinMerkle32Leaf.leafInput tag packed salt) =
      some (packed, salt) := by
  have htake :
      ((AspisR1.BinMerkle32Leaf.leafInput tag packed salt).drop 2).take w = packed := by
    simp [AspisR1.BinMerkle32Leaf.leafInput, hpacked]
  have hdrop :
      (AspisR1.BinMerkle32Leaf.leafInput tag packed salt).drop (2 + w) = salt := by
    rw [AspisR1.BinMerkle32Leaf.leafInput,
      show 2 + w = (1 + w) + 1 by omega, List.drop_succ_cons,
      show 1 + w = w + 1 by omega, List.drop_succ_cons]
    rw [List.drop_append_of_le_length (by omega : w ≤ packed.length)]
    rw [List.drop_of_length_le (by omega : packed.length ≤ w)]
    simp
  simp [parse, htake, hdrop, hpacked, hsalt]

theorem parse_sound (tag : Byte) (w : Nat) (input : List Byte)
    (data : LeafData) (h : parse tag w input = some data) :
    data.1.length = w ∧ data.2.length = 32 ∧
      AspisR1.BinMerkle32Leaf.leafInput tag data.1 data.2 = input := by
  let parsed : LeafData := (input.drop 2 |>.take w, input.drop (2 + w))
  have hparse :
      (if parsed.1.length = w ∧ parsed.2.length = 32 ∧
          AspisR1.BinMerkle32Leaf.leafInput tag parsed.1 parsed.2 = input
        then some parsed else none) = some data := by
    simpa [parse, parsed] using h
  by_cases hc : parsed.1.length = w ∧ parsed.2.length = 32 ∧
      AspisR1.BinMerkle32Leaf.leafInput tag parsed.1 parsed.2 = input
  · have heq : parsed = data := Option.some.inj (by simpa [hc] using hparse)
    subst data
    exact hc
  · simp [hc] at hparse


#print axioms parse_leafInput
#print axioms parse_sound

end AspisR1.BinMerkleLeafCodec
