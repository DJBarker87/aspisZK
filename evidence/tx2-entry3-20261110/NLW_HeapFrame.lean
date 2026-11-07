import NLW_064Invocation
set_option autoImplicit false
noncomputable section
namespace NLW_HeapFrame
open Aeneas Aeneas.Std NLW_064Invocation
/-- Scalar native metadata alone has no payload interpretation. The decoder
also reads the live full memory and complete caller context. -/
structure Meta where
 publicAddress : Nat
 publicLength : Nat
 proofAddress : Nat
 proofLength : Nat
 checkpointAddress : Nat
 checkpointLength : Nat
 hashIdentity : Nat
 descriptors : Nat
 loans : Nat
 owned : Nat
 allocator : Nat
 cursor : Nat
structure Native (Heap : Type) where
 metadata : Meta
 heap : Heap
/-- Pre-existing value/memory relation, not an address-implies-payload rule.
The caller context may contain the full SDK/tokens/owned/allocator state. -/
def Decodes {Heap Ambient : Type}
 (read : Heap → Nat → Nat → Option (List U8))
 (context : Heap → Meta → Option (NLM_PacketTypes.World Ambient))
 (native : Native Heap) (frame : Frame Ambient) : Prop :=
 read native.heap native.metadata.publicAddress native.metadata.publicLength=some frame.args.publicBytes.val ∧
 read native.heap native.metadata.proofAddress native.metadata.proofLength=some frame.args.proof.val ∧
 read native.heap native.metadata.checkpointAddress native.metadata.checkpointLength=some frame.args.checkpoint.val ∧
 context native.heap native.metadata=some frame.world
/-- What empty modifies + full metadata equality actually transports. These
premises must come from the pinned cut contract and its actual decoder; this
generic lemma is NOT that producer and never supplies a row root by itself. -/
theorem preserve {Heap Ambient : Type}
 (read : Heap → Nat → Nat → Option (List U8))
 (context : Heap → Meta → Option (NLM_PacketTypes.World Ambient))
 (before after : Native Heap) (frame : Frame Ambient)
 (metadata : after.metadata=before.metadata) (heap : after.heap=before.heap)
 (input : Decodes read context before frame) : Decodes read context after frame := by
 unfold Decodes at input ⊢
 rw [metadata,heap]
 exact input
#print Decodes
#print preserve
#print axioms preserve
end NLW_HeapFrame
