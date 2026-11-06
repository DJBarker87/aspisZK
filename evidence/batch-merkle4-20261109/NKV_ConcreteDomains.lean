import NKV_ConcreteChildren
import NKB_KeyStream
import NKB_ProducerChain
import NKL_ClosedChildren
set_option autoImplicit false
noncomputable section
namespace NKV_ConcreteDomains
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1
open NKV_StepErasure
open AspisV8R19.DuplexFrames
attribute [local instance] Classical.propDecidable
abbrev HashState := AspisV8R19.SourceDuplexStep.State

theorem count (indices : Slice U32) :
 ∃ out : Option Usize,NKV_ConcreteChildren.count .Two indices=ok out ∧
 out.map (fun x : Usize => x.val)=
 (if OraclePortFrozenOrder.wellFormed (indices.val.map (fun x : U32 => x.val)) then
    some (OraclePortFrozenOrder.nodeCount 18 (indices.val.map (fun x : U32 => x.val))) else none) :=
 NJE_CountPacket.TX2_088 indices

/-- Full byte payload at the SAME original proof/ordinal, supplied by the
CLOSED opening law, not inferred from a pointer equality. -/
theorem opening (H : Bytes → HashState) (proof : Slice U8) (width : proof.val.length=57607)
 (i : Usize) (bound : i.val<22) :
 ∃ view,(NKV_ConcreteChildren.ops H).op2 proof i=ok view ∧ view.val.length=832 ∧
 MultiproofConeCanonical.bytesOf view.val=
 OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) (10055+i.val*832) 832 :=
 NKL_ClosedChildren.opening proof width i bound

theorem leaf {X : Type} (H : Bytes → HashState) (D : aspis_core.digest.Digest32 X)
 (hash : X) (tree : Usize) (view : Slice U8) (width : view.val.length=832) :
 (NKV_ConcreteChildren.ops H).op6 D hash tree view=
 Port4B_LeafCode.native D hash tree view := by
 simpa only [NKV_ConcreteChildren.ops,NKV_ConcreteChildren.toExtract,NJS_BatchLeaf.modelDigest]
   using NJS_BatchLeaf.source (NKV_ConcreteChildren.toExtract D) hash tree view width

theorem leaf_domains (view : Slice U8) (width : view.val.length=832) :
 (MultiproofConeSlices.sub view 0#usize 480#usize).val.length=480 ∧
 (MultiproofConeSlices.sub view 480#usize 608#usize).val.length=128 ∧
 (MultiproofConeSlices.sub view 672#usize 800#usize).val.length=128 ∧
 (MultiproofConeSlices.sub view 608#usize 640#usize).val.length=32 ∧
 (MultiproofConeSlices.sub view 640#usize 672#usize).val.length=32 ∧
 (MultiproofConeSlices.sub view 800#usize 832#usize).val.length=32 :=
 NJS_BatchLeaf.domains view width

/-- TX2 must consume this SAME-produced-scratch gate, preserving the original
superseded ten-leaf clause in the ledger. No independent selected scratch. -/
theorem verifier_bytes (leaves : List MultiproofConeLiveFold.Leaf)
 (before after : MultiproofConeRef.reference.Scratch) (slot : Slice U8)
 (empty : before.n.val=0) (nonempty : leaves≠[]) (size : leaves.length≤12)
 (ordered : (leaves.map (fun x => x.1.val)).Pairwise (·≤·))
 (canonical : ∀ leaf∈leaves,leaf.1.val<262144)
 (chain : NKB_LeafChain.Chain leaves before (some after))
 (fits : 32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys after)≤slot.val.length) :
 (MultiproofConeSlotTail.prefixNodes slot
   (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys after))).val.length≤9216 :=
 NKB_ProducerChain.verifier_bytes leaves before after slot empty nonempty size ordered canonical chain fits

set_option pp.proofs false
#print opening
#print leaf
#print verifier_bytes
#print axioms count
#print axioms opening
#print axioms leaf
#print axioms leaf_domains
#print axioms verifier_bytes
end NKV_ConcreteDomains
end
