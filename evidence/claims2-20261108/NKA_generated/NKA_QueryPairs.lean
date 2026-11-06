import NJT_QPairs
import NJT_QReached
import NHB_OuterState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_QueryPairs
open Aeneas Aeneas.Std Result NJT_QBase NGQ_SamplerDriver

/-- The native carried state is advances[7] until the FIRST stop, then that
SAME block's advance. The list is exactly the eight source indices. -/
def inputs (blocks : Blocks) : List (Bytes32×Usize) :=
 blocks.val.zip [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]

theorem indices (blocks : Blocks) : ∀ pair∈inputs blocks,pair.2.val<8 := by
 apply NGQ_SamplerPacket.zip_bound
 intro i hi
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with h|h|h|h|h|h|h|h <;> subst i <;> decide

/-- Source-order composition, including finish rejection and selected advance.
No arbitrary default operation: initial is the derived all-zero QueryScan.
The only conditional input is the reviewed native word-step transcription. -/
theorem queries_from_pairs (native : NJT_QScan.Native) (cut : NJT_QScan.Cut native)
 (blocks advances : Blocks) :
 AspisR1Query31Transcript.queries_from_pairs_with_scan NGQ_SamplerPacket.Scan
  NGQ_SamplerPacket.initial blocks advances =
 NHB_OuterState.walk (NJT_QPairs.nativeScan native) advances
  (advances.val[7]'(by have h:=advances.property;change advances.val.length=8 at h;omega))
  (inputs blocks) NGQ_SamplerPacket.initial := by
 have association := NHB_OuterState.association (NJT_QPairs.nativeScan native) advances
  7#usize (by decide) (inputs blocks) (indices blocks) NGQ_SamplerPacket.initial
 exact (NJT_QPairs.reference native cut blocks advances).trans association.symm

/-- All eight scans and each entered finish have the bounds, canonical prefix
and inactive-cell frame derived from default and SAME preceding blocks. -/
theorem reached (native : NJT_QScan.Native) (cut : NJT_QScan.Cut native)
 (blocks : List Bytes) :
 NJT_QDomains.Domain (NJT_QReached.carry native blocks NGQ_SamplerPacket.initial) :=
 NJT_QReached.carry_domain native cut blocks _ NJT_QDomains.initial

#print queries_from_pairs
#print axioms indices
#print axioms queries_from_pairs
#print axioms reached
end AspisR1.NKA_QueryPairs
end
