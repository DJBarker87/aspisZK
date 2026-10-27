import R9PoolRuntimeBinding
set_option autoImplicit false
namespace AspisR1.P2P_PersistenceGap
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open R9PoolRuntimeBinding

/-- Equal preserved headers do not establish equality of the submitted bytes.
This refutes that logical step only, not the deployed accepted-source theorem. -/
theorem same_header_different_bytes (state : State) :
    ∃ written current : Inputs,
      written.proof.length = current.proof.length ∧
      written.pub.length = current.pub.length ∧
      digestMatches (fun _ => state) written current ∧
      ¬ P2Prime (fun _ => state) written current := by
  refine ⟨⟨[0],[0]⟩,⟨[1],[1]⟩,rfl,rfl,⟨rfl,rfl⟩,?_⟩
  intro binding
  have impossible := (List.cons.inj (binding ⟨rfl,rfl⟩).1).1
  norm_num at impossible

#print axioms same_header_different_bytes
end AspisR1.P2P_PersistenceGap
