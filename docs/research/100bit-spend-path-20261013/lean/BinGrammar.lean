import BinMerkleNodeCodec
import BinMerkle32Leaf
import R1Merkle32Path

/-! Literal prototype grammar. Mirrors multiproof.rs:48 and
Merkle32Leaf.lean:15 (unchanged private leaf grammar).
Arbitrary public-byte hashing has no domain separator; see the obstruction
in the design document. No universal separation axiom is introduced. -/
set_option autoImplicit false
namespace AspisR1.BinGrammar
open BinMerkle32Path BinMerkle32Leaf

/-- Exact concatenation passed to `hash.digest` in multiproof.rs:49. -/
theorem nodeInput_slices (cs : Children) :
    nodeInput cs = (0x12 : Byte) :: (List.ofFn (cs 0) ++ List.ofFn (cs 1)) := by
  apply congrArg (List.cons (0x12 : Byte))
  change List.ofFn (childByte cs) = List.ofFn (cs 0) ++ List.ofFn (cs 1)
  rw [List.ofFn_add (n := 32) (m := 32)]
  have hl : (fun i : Fin 32 => childByte cs (i.castLE (by omega))) = cs 0 := by
    funext i
    unfold childByte
    have hc : (⟨(i.castLE (by omega) : Fin 64).val / 32, by omega⟩ : Fin 2) = 0 := by
      apply Fin.ext
      simp only [Fin.val_castLE, Fin.val_zero]
      omega
    have hb : (⟨(i.castLE (by omega) : Fin 64).val % 32,
        Nat.mod_lt _ (by omega)⟩ : Fin 32) = i := by
      apply Fin.ext
      simp only [Fin.val_castLE]
      omega
    rw [hc, hb]
  have hr : (fun i : Fin 32 => childByte cs (i.natAdd 32)) = cs 1 := by
    funext i
    unfold childByte
    have hc : (⟨(i.natAdd 32).val / 32, by omega⟩ : Fin 2) = 1 := by
      apply Fin.ext
      simp only [Fin.val_natAdd, Fin.val_one]
      omega
    have hb : (⟨(i.natAdd 32).val % 32,
        Nat.mod_lt _ (by omega)⟩ : Fin 32) = i := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    rw [hc, hb]
  rw [hl, hr]

theorem node_ne_leaf (cs : Children) (tag : Byte) (packed salt : List Byte) :
    nodeInput cs ≠ leafInput tag packed salt := by
  intro h
  have hh := congrArg List.head? h
  have : (0x12 : Byte) = 0x10 := by simpa [nodeInput, leafInput] using hh
  exact (by decide : (0x12 : Byte) ≠ 0x10) this

theorem node_ne_eight (cs : Children) (eight : Merkle32Path.Children) :
    nodeInput cs ≠ Merkle32Path.nodeInput eight := by
  intro h
  have hh := congrArg List.head? h
  have : (0x12 : Byte) = 0x18 := by
    simpa [nodeInput, Merkle32Path.nodeInput] using hh
  exact (by decide : (0x12 : Byte) ≠ 0x18) this

/-- Applies to any *actually prefixed* record class with a distinct byte. -/
theorem node_ne_tagged (cs : Children) (tag : Byte) (rest : List Byte)
    (hne : (0x12 : Byte) ≠ tag) : nodeInput cs ≠ tag :: rest := by
  intro h
  exact hne (List.cons.inj h).1

/-- Length is a separate, useful discriminator for untagged frames. -/
theorem node_ne_length (cs : Children) (record : List Byte)
    (hlen : record.length ≠ 65) : nodeInput cs ≠ record := by
  intro h
  exact hlen (h ▸ nodeInput_length cs)

/-- Public bytes are unrestricted in verifier.rs:382. They can literally be
one of the Merkle preimages, independently of the oracle. -/
theorem unrestricted_public_overlap (cs : Children) :
    ∃ public : List Byte, public = nodeInput cs := ⟨nodeInput cs, rfl⟩

#print axioms nodeInput_slices
#print axioms node_ne_leaf
#print axioms node_ne_eight
#print axioms node_ne_tagged
#print axioms node_ne_length
#print axioms unrestricted_public_overlap
end AspisR1.BinGrammar
