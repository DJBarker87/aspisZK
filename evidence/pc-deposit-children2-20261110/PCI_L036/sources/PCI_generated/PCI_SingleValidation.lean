import PCI_ValidateFull
import PCC_SingleOutputReference
set_option autoImplicit false
namespace PCI_SingleValidation
open PCA
@[simp] theorem mul_zero (x : UInt32) : PCC.fieldMul x 0=0 := by
  simp [PCC.fieldMul]
@[simp] theorem zero_mul (x : UInt32) : PCC.fieldMul 0 x=0 := by
  simp [PCC.fieldMul]

theorem empty_canonical : PCC.canonical (Vector.replicate 8 (0:UInt32))=true := by
  simp [PCC.canonical]

/-- Use zero sparsity before any concrete field normalization. -/
theorem validation (commitment : Digest) :
    PCC.validatePair (PCC.singleWitness commitment)=
      if PCC.canonical commitment then .ok () else .error .NonCanonicalCommitment := by
  cases h : PCC.canonical commitment <;>
    simp [PCC.validatePair,PCC.singleWitness,empty_canonical,h]

#print axioms mul_zero
#print axioms zero_mul
#print axioms empty_canonical
#print axioms validation
end PCI_SingleValidation
