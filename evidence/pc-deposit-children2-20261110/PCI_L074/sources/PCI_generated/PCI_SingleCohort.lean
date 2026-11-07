import PCI_SingleExtracted
import PCI_DigestCarrier
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_SingleCohort
open PCI_DigestCarrier PCI_ValidateCarrier

theorem zero_digest : digest (Array.repeat 8#usize 0#u32)=Vector.replicate 8 (0:UInt32) := by
  rfl

def decode (r : PCI_SingleRef.Single) : Except PCA.LeafError PCA.PairWitness :=
  if r.tag=0#u8 then .ok {
    firstCommitment:=digest r.first
    secondOccupied:=readWord r.occupied
    secondCommitment:=digest r.second
    secondOccupancyInverse:=readWord r.inverse}
  else .error .NonCanonicalCommitment

theorem answer (d : Array U32 8#usize) :
    decode (PCI_SingleExtracted.answer d (PCI_ArrayCanonical.model d))=
      if PCC.canonical (digest d) then .ok (PCC.singleWitness (digest d))
      else .error .NonCanonicalCommitment := by
  rw [←PCI_DigestCarrier.canonical]
  cases h : PCI_ArrayCanonical.model d <;>
    simp only [PCI_SingleExtracted.answer,h,decode,ite_false,ite_true,Bool.false_eq_true,
      zero_digest,PCC.singleWitness]
  all_goals rfl

theorem complete (d : Array U32 8#usize) :
    (do let out ← PCI_SingleRef.single_reference d;ok (decode out))=
      PCI_SingleComplete.source (digest d) := by
  rw [PCI_SingleExtracted.extracted,PCI_SingleComplete.complete]
  simp only [bind_tc_ok,answer]

#print axioms zero_digest
#print axioms answer
#print axioms complete
end PCI_SingleCohort
