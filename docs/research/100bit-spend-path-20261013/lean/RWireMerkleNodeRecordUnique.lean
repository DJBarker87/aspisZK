import BinMerkleRecordedLog

/-! Distinct parsed node children cannot share a digest when their literal
input records are separated by the supplied hash-separation premise. -/
set_option autoImplicit false
namespace AspisR1.RWireMerkleNodeRecordUnique

open BinMerkle32Path BinMerkleRecordedLog

theorem nodes_unique_by_digest (hash : List BinMerkle32Path.Byte → Digest) (log : Log)
    (hlog : Consistent hash log)
    (hsep : ∀ a b da db, (a, da) ∈ log → (b, db) ∈ log →
      hash a = hash b → a = b) :
    ∀ cs1 cs2 d, (cs1, d) ∈ nodes log → (cs2, d) ∈ nodes log → cs1 = cs2 := by
  intro cs1 cs2 d hentry1 hentry2
  obtain ⟨input1, hinput1, hparse1⟩ := mem_nodes.mp hentry1
  obtain ⟨input2, hinput2, hparse2⟩ := mem_nodes.mp hentry2
  have hhash1 : hash input1 = d := hlog input1 d hinput1
  have hhash2 : hash input2 = d := hlog input2 d hinput2
  have heq : input1 = input2 := hsep input1 input2 d d hinput1 hinput2
    (hhash1.trans hhash2.symm)
  apply nodeInput_injective
  calc
    nodeInput cs1 = input1 := BinMerkleNodeCodec.parse_sound hparse1
    _ = input2 := heq
    _ = nodeInput cs2 := (BinMerkleNodeCodec.parse_sound hparse2).symm

#print axioms nodes_unique_by_digest


end AspisR1.RWireMerkleNodeRecordUnique
