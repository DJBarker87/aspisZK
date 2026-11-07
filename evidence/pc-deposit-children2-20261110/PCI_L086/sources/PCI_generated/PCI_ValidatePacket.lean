import PCI_ValidateFull
import PCI_SharedScanner
import PCI_DigestRoundtrip
import PCI_ValidateSub
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ValidatePacket
open PCA

theorem full (w : PairWitness) (state : PCA_State) :
    PCI_ValidateComplete.observe w state=ok ⟨state,[],match PCC.validatePair w with
      | .ok () => .ok () | .error e => .error (.leaf e)⟩ ∧
    (¬PCI_ValidateDomains.Entered w ∨ PCI_ValidateDomains.Domain w) ∧
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical
      (PCI_DigestRoundtrip.encode w.firstCommitment)=ok (PCC.canonical w.firstCommitment) ∧
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical
      (PCI_DigestRoundtrip.encode w.secondCommitment)=ok (PCC.canonical w.secondCommitment) := by
  obtain ⟨value,domains⟩ := PCI_ValidateFull.full w state
  refine ⟨value,domains,?_,?_⟩
  · rw [PCI_SharedScanner.result,PCI_DigestRoundtrip.roundtrip]
  · rw [PCI_SharedScanner.result,PCI_DigestRoundtrip.roundtrip]

#print axioms full
end PCI_ValidatePacket
