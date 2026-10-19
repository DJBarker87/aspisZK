import BinMerkle32Path

/-! Mirrors `MerkleTraceInputs.lean`; see design/BIN-COMMITMENT-MODEL-20261019.md for line pins.
 Structural shape of inputs recorded by a Merkle32 path trace. -/
set_option autoImplicit false
namespace AspisR1.BinMerkleTraceInputs

 theorem inputTrace_node_shape (hash : List BinMerkle32Path.Byte → BinMerkle32Path.Digest)
    {slots : List (Fin 2)} (path : BinMerkle32Path.Path slots)
    (current : BinMerkle32Path.Digest) {input : List BinMerkle32Path.Byte}
    (hin : input ∈ BinMerkle32Path.inputTrace hash path current) :
    ∃ children : BinMerkle32Path.Children, input = BinMerkle32Path.nodeInput children := by
  induction path generalizing current with
  | nil =>
      simp [BinMerkle32Path.inputTrace] at hin
  | cons siblings tail ih =>
      simp only [BinMerkle32Path.inputTrace, List.mem_cons] at hin
      rcases hin with hhead | htail
      · exact ⟨BinMerkle32Path.fillChild _ siblings current, hhead⟩
      · exact ih _ htail



#print axioms inputTrace_node_shape
end AspisR1.BinMerkleTraceInputs
