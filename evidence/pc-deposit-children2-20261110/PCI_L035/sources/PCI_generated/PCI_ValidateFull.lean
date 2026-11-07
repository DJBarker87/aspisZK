import PCI_ValidateComplete
import PCI_ValidateDomains
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ValidateFull
open PCA
/-- Full typed Result/state/effects plus every reached field caller domain.
    No child Result, child success, endpoint or free operation dictionary is a premise. -/
theorem full (w : PairWitness) (state : PCA_State) :
    PCI_ValidateComplete.observe w state=
      ok ⟨state,[],match PCC.validatePair w with
        | .ok () => .ok () | .error e => .error (.leaf e)⟩ ∧
    (¬PCI_ValidateDomains.Entered w ∨ PCI_ValidateDomains.Domain w) :=
  ⟨PCI_ValidateComplete.result_state_effects w state,PCI_ValidateDomains.reached_domains w⟩
#print axioms full
end PCI_ValidateFull
