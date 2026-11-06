import NJE_ParentPackets
import NJP_CohortNode

set_option autoImplicit false
noncomputable section
namespace NJV_ChildArguments
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef

/-- The occupied child is the CLOSED deployed child at this SAME prestate and
index. Both actual stored slices are encoded without copies or re-selection. -/
theorem occupied (H : Slice (Slice U8) → RefDigest) (s : reference.Scratch)
    (i next : Usize) (bound : i.val+1<16) (next_value : next.val=i.val+1) :
 NJA_Multiproof.multiproof.occupied_binary_parent (NJE_ParentPackets.backend H) () s.val i=
 ok (H (NJP_RequestTransport.address (NJP_RowModel.occupiedRequest (raw s) i.val))) := by
 rw [NJE_ParentPackets.TX2_089 H s.val i bound,
   NJP_CohortRead.occupied_address s i next (by omega) (by omega) next_value]
 simp only [NJE_ParentPackets.cell,next_value]

/-- Sibling child domain: the stored digest and supplied full 32-byte sibling
are used in the branch's actual left/right order. -/
theorem sibling (H : Slice (Slice U8) → RefDigest) (s : reference.Scratch)
    (i : Usize) (bound : i.val<16) (digest : RefDigest) (left : Bool) :
 NJA_Multiproof.multiproof.sibling_binary_parent (NJE_ParentPackets.backend H) () s.val i
   (Array.to_slice digest) left=
 ok (H (NJP_RequestTransport.address
   (if left then (NJP_RowModel.value (raw s) i.val,decode digest)
    else (decode digest,NJP_RowModel.value (raw s) i.val)))) := by
 rw [NJE_ParentPackets.TX2_091 H s.val i bound digest left]
 cases left <;> simp only [Bool.false_eq_true,ite_false,ite_true,NJP_RequestTransport.address,
   NJP_CohortRead.value s i bound,encode_decode,NJE_ParentPackets.cell]

/-- Caller invariants imply every occupied helper's bound and writable slot.
The sibling window domain is proved at the branch, not assumed of all inputs. -/
theorem domains (physical : Slice U8) (s : reference.Scratch) (i w : Usize)
    (domain : AspisR1.MultiproofConeNodeDomain.RowDomain physical s i w) (active : i.val<s.n.val) :
 i.val<16 ∧ w.val<16 ∧
 (NJP_RowModel.paired (raw s) i.val → i.val+1<16) := by
 have size := domain.2.1
 have write := domain.2.2.2.1
 refine ⟨by omega,by omega,?_⟩
 intro both
 have next := both.1
 change i.val+1<s.n.val at next
 omega

#print occupied
#print axioms occupied
#print sibling
#print axioms sibling
#print domains
#print axioms domains
end NJV_ChildArguments
end
