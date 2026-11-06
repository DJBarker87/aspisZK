import NJS_Slot
import NKB_ProducerChain
set_option autoImplicit false
namespace NKL_TailGeometry
open Aeneas Aeneas.Std Result AspisR1

def capacity (s : Nat) : Nat := [146,146,128,172,172,150][s]!

theorem cap_bound (s : Nat) (bound : s<6) : capacity s≤172 := by
 unfold capacity
 interval_cases s <;> decide

theorem counted_prefix (s count : Nat) (bound : s<6) (fits : count≤capacity s) :
 32*count≤5504 ∧ 32*count≤9216 := by
 have cap:=cap_bound s bound
 omega

/-- Count guard is tested before any slice multiplication or padding read.
On its continuing branch both physical slices fit, even for count zero. -/
theorem suffix (s count : Nat) (bound : s<6) (fits : count≤capacity s) :
 32*count≤32*capacity s ∧ (32*capacity s-32*count)%8=0 := by
 constructor
 · omega
 · have multiple : 32*capacity s-32*count=8*(4*(capacity s-count)) := by omega
   rw [multiple,Nat.mul_mod_right]

/-- (bb)(3) preserves the predecessor's exact producer domain; the original
TX2 <=10 clause remains superseded-by-finding, never used here. -/
theorem tx2_bytes (leaves : List MultiproofConeLiveFold.Leaf)
 (before after : MultiproofConeRef.reference.Scratch) (slot : Slice U8)
 (empty : before.n.val=0) (nonempty : leaves≠[]) (size : leaves.length≤12)
 (ordered : (leaves.map (fun x => x.1.val)).Pairwise (·≤·))
 (canonical : ∀ leaf∈leaves,leaf.1.val<262144)
 (chain : NKB_LeafChain.Chain leaves before (some after))
 (fits : 32*OraclePortSelectedDraft.nodeCount 18 (NJV_UnitDomain.keys after)≤slot.val.length) :
 (MultiproofConeSlotTail.prefixNodes slot
   (OraclePortSelectedDraft.nodeCount 18 (NJV_UnitDomain.keys after))).val.length≤9216 :=
 NKB_ProducerChain.verifier_bytes leaves before after slot empty nonempty size ordered canonical chain fits

#print axioms cap_bound
#print axioms counted_prefix
#print axioms suffix
#print axioms tx2_bytes
end NKL_TailGeometry
