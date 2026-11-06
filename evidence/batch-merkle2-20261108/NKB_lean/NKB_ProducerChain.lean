import NKB_LeafChain
import NKB_CallerDomain
import NKB_CallerPrefix

set_option autoImplicit false
namespace NKB_ProducerChain
open Aeneas Aeneas.Std Result MultiproofConeRef AspisR1
open MultiproofConeLiveFold OraclePortFrozenOrder

/-- The SAME cut chain produces the count/order/canonicality used at the
actual node-count/verifier call. No independently selected scratch is substituted.
These are local composition lemmas, not a CLOSED complete batch_tree root. -/
theorem caller (leaves : List Leaf) (before after : reference.Scratch)
    (empty : before.n.val=0) (nonempty : leaves≠[]) (size : leaves.length≤12)
    (ordered : (leaves.map (fun x => x.1.val)).Pairwise (·≤·))
    (canonical : ∀ leaf∈leaves,leaf.1.val<262144)
    (chain : NKB_LeafChain.Chain leaves before (some after)) :
 0<after.n.val ∧ after.n.val≤leaves.length ∧ wellFormed (NJV_UnitDomain.keys after) := by
 have run := NKB_LeafChain.source leaves before (some after) chain
 obtain ⟨positive,count,sorted,range⟩ := NKB_IndexFold.producer leaves before after
   empty nonempty size ordered canonical run
 exact ⟨positive,count,NKB_CallerDomain.well after positive (by omega) sorted range⟩

/-- Both occurrences instantiate NJV on the actual counted prefix of this
slot and this produced scratch. In particular the twelve-query caller derives
<=9216 directly, without a false twelve-implies-ten claim. -/
theorem verifier_bytes (leaves : List Leaf) (before after : reference.Scratch) (slot : Slice U8)
    (empty : before.n.val=0) (nonempty : leaves≠[]) (size : leaves.length≤12)
    (ordered : (leaves.map (fun x => x.1.val)).Pairwise (·≤·))
    (canonical : ∀ leaf∈leaves,leaf.1.val<262144)
    (chain : NKB_LeafChain.Chain leaves before (some after))
    (fits : 32*nodeCount 18 (NJV_UnitDomain.keys after)≤slot.val.length) :
 (MultiproofConeSlotTail.prefixNodes slot (nodeCount 18 (NJV_UnitDomain.keys after))).val.length≤9216 := by
 exact NKB_CallerPrefix.bytes slot after
   (caller leaves before after empty nonempty size ordered canonical chain).2.2 fits

#print axioms caller
#print axioms verifier_bytes
end NKB_ProducerChain
