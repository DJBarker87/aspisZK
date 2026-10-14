import R1Merkle32Path

/-! Structural shape of inputs recorded by a Merkle32 path trace. -/
set_option autoImplicit false
namespace AspisR1.MerkleTraceInputs

 theorem inputTrace_node_shape (hash : List Merkle32Path.Byte → Merkle32Path.Digest)
    {slots : List (Fin 8)} (path : Merkle32Path.Path slots)
    (current : Merkle32Path.Digest) {input : List Merkle32Path.Byte}
    (hin : input ∈ Merkle32Path.inputTrace hash path current) :
    ∃ children : Merkle32Path.Children, input = Merkle32Path.nodeInput children := by
  induction path generalizing current with
  | nil =>
      simp [Merkle32Path.inputTrace] at hin
  | cons siblings tail ih =>
      simp only [Merkle32Path.inputTrace, List.mem_cons] at hin
      rcases hin with hhead | htail
      · exact ⟨Merkle32Path.fillChild _ siblings current, hhead⟩
      · exact ih _ htail

#print axioms inputTrace_node_shape

end AspisR1.MerkleTraceInputs
