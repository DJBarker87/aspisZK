import PCC_PairValidation
set_option autoImplicit false
namespace PCC
open PCA

def singleWitness (commitment : Digest) : PairWitness :=
  ⟨commitment,0,Vector.replicate 8 0,0⟩

/-- POOL:222 retains the validator's first exact error; its silent pure
field work has no account/token/syscall effects. -/
def singleOutputReference (commitment : Digest) : Reference PairWitness := fun s =>
  let w := singleWitness commitment
  ⟨s,[],match validatePair w with | .error e => .error (.leaf e) | .ok () => .ok w⟩

def RowSpec_POOL_222 (native : Digest → Reference PairWitness) : Prop :=
  Reference.RowSpec (fun _ _ => True) native singleOutputReference
end PCC
