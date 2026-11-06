import NKV_LeafOrder
set_option autoImplicit false
noncomputable section
namespace NKV_ProducerDomain
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeRef OraclePortFrozenOrder
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

/-- An intermediate returning branch, not an entry premise: the scratch is
produced by exactly the source build whose sorted list supplies all domains. -/
theorem caller (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) (before after : reference.Scratch)
 (empty : before.n.val=0)
 (accepted : (NKV_LeafBuild.build H p q kind (sortedPositions q batch kind) before).2=ok (true,after)) :
 0<after.n.val ∧ after.n.val≤12 ∧ wellFormed (NJV_UnitDomain.keys after) := by
 have size:=NKV_LeafOrder.size H p q batch kind
 have chain:=NKV_LeafBuild.chain H p q kind (sortedPositions q batch kind) before after
   (by simpa only [NKV_LeafBuild.leaves,List.length_map,empty,Nat.zero_add] using size.trans (by decide : 12≤16)) accepted
 obtain ⟨positive,count,well⟩:=NKB_ProducerChain.caller _ before after empty
   (NKV_LeafOrder.nonempty H p q batch kind) size (NKV_LeafOrder.ordered H p q batch kind)
   (NKV_LeafOrder.canonical H p q kind _) chain
 exact ⟨positive,count.trans size,well⟩

theorem tx2_bytes (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) (before after : reference.Scratch) (slot : Slice U8)
 (empty : before.n.val=0)
 (accepted : (NKV_LeafBuild.build H p q kind (sortedPositions q batch kind) before).2=ok (true,after))
 (fits : 32*nodeCount 18 (NJV_UnitDomain.keys after)≤slot.val.length) :
 (MultiproofConeSlotTail.prefixNodes slot (nodeCount 18 (NJV_UnitDomain.keys after))).val.length≤9216 := by
 have size:=NKV_LeafOrder.size H p q batch kind
 exact NKB_ProducerChain.verifier_bytes _ before after slot empty
   (NKV_LeafOrder.nonempty H p q batch kind) size (NKV_LeafOrder.ordered H p q batch kind)
   (NKV_LeafOrder.canonical H p q kind _)
   (NKV_LeafBuild.chain H p q kind _ before after
     (by simpa only [NKV_LeafBuild.leaves,List.length_map,empty,Nat.zero_add] using size.trans (by decide : 12≤16)) accepted) fits

/-- The TX1 occurrence keeps its actual ten-query domain. -/
theorem tx1_count (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (kind : Nat) (before after : reference.Scratch)
 (empty : before.n.val=0)
 (accepted : (NKV_LeafBuild.build H p q kind (sortedPositions q 0 kind) before).2=ok (true,after)) :
 after.n.val≤10 := by
 have size:=NKV_LeafOrder.size H p q 0 kind
 have chain:=NKV_LeafBuild.chain H p q kind (sortedPositions q 0 kind) before after
   (by simpa only [NKV_LeafBuild.leaves,List.length_map,empty,Nat.zero_add] using size.trans (by decide : 12≤16)) accepted
 have count:=(NKB_ProducerChain.caller _ before after empty
   (NKV_LeafOrder.nonempty H p q 0 kind) size (NKV_LeafOrder.ordered H p q 0 kind)
   (NKV_LeafOrder.canonical H p q kind _) chain).2.1
 simpa only [NKV_LeafBuild.leaves,List.length_map,sortedPositions,List.length_mergeSort,
   batchPositions,if_pos rfl,List.length_range] using count

#print caller
#print tx2_bytes
#print tx1_count
#print axioms caller
#print axioms tx2_bytes
#print axioms tx1_count
end NKV_ProducerDomain
end
