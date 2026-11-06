import PCC_Reference
import PCA_ValidatorReferences
import PCA_RowSpec_POOL_332
set_option autoImplicit false
namespace PCC
open PCA
/-- Concrete adopted references reused read-only from PCA. -/
abbrev countReference := PCA.countReference
abbrev tokenProgramReference := PCA.tokenProgramReference
abbrev payerSystemReference := PCA.payerSystemReference
abbrev uniqueReference := PCA.uniqueReference
/-- Own argument domain includes bounds of exactly the dereferenced indices. -/
def accountDomain (a : Nat) (s : PCA_State) : Prop := a < s.accountCount

def RowSpec_POOL_332 (native : Nat → Reference Unit) : Prop :=
  Reference.RowSpec (fun _ _ => True) native countReference

def RowSpec_POOL_365 (native : Nat → Reference Unit) : Prop :=
  Reference.RowSpec accountDomain native tokenProgramReference

def RowSpec_POOL_364 (native : (Nat × Nat) → Reference Unit) : Prop :=
  Reference.RowSpec (fun args s => args.1 < s.accountCount ∧ args.2 < s.accountCount)
    native payerSystemReference

def RowSpec_POOL_367 (native : Unit → Reference Unit) : Prop :=
  Reference.RowSpec (fun _ _ => True) native uniqueReference
end PCC
