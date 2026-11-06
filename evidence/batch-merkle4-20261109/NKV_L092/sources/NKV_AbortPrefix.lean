import NKV_VerifyInvocation
set_option autoImplicit false
noncomputable section
namespace NKV_AbortPrefix
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConePhysicalTransport

theorem take_prefix {A : Type} (leaf prior tail : List A) (known : tail.take prior.length=prior) :
 (leaf++tail).take (leaf.length+prior.length)=leaf++prior := by
 induction leaf with
 | nil => simpa only [List.nil_append,List.length_nil,Nat.zero_add] using known
 | cons x xs ih => simpa only [List.cons_append,List.length_cons,Nat.succ_add,List.take_succ_cons]
     using congrArg (List.cons x) ih

theorem pending {A : Type} (leaf tail : List A) (offset : Nat) :
 (leaf++tail)[leaf.length+offset]?=tail[offset]? := by
 induction leaf with
 | nil => rfl
 | cons x xs ih => simpa only [List.cons_append,List.length_cons,Nat.succ_add,List.getElem?_cons_succ] using ih

/-- The verifier abort is attached to the actual prior leaf history on the
same produced scratch. No reply or suffix event is invented for its pending
query; the byte gate is supplied by the twelve-index producer theorem. -/
theorem tx2 (H : Bytes → State) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) (before after : reference.Scratch) (slot : Slice U8)
 (empty : before.n.val=0)
 (accepted : (NKV_LeafBuild.build H p q kind (OraclePortFrozenOrder.sortedPositions q batch kind) before).2=ok (true,after))
 (fits : 32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys after)≤slot.val.length)
 (root : Array U8 32#usize)
 (events : List (NJP_RowModel.Request × NJP_RowModel.Digest))
 (request : NJP_RowModel.Request) (state : NJP_RowModel.Scratch)
 (native : NJV_AbortEntry.Invocation (NJP_RequestTransport.hash (rawOracle H)) root
   (MultiproofConeSlotTail.prefixNodes slot (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys after)))
   (NJV_EntryABI.initial after.idx after.val after.n) events request state) :
 let leaf:=(NKV_LeafBuild.build H p q kind (OraclePortFrozenOrder.sortedPositions q batch kind) before).1
 let physical:=MultiproofConeSlotTail.prefixNodes slot (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys after))
 let tail:=(eval H (NJV_TX2Returning.endpoint root physical after.idx after.val after.n)).1
 (leaf++tail).take (leaf.length+events.length)=leaf++NJV_AdoptedObservation.history events ∧
 ((leaf++tail)[leaf.length+events.length]?).map Prod.fst=
   some (flatten (NJP_RequestTransport.address request)) := by
 have bytes:=NKV_ProducerDomain.tx2_bytes H p q batch kind before after slot empty accepted fits
 have packet:=(NJV_TX2.abort H root _ after.idx after.val after.n bytes events request state native).1
 dsimp only
 constructor
 · have lengths : (NJV_AdoptedObservation.history events).length=events.length := by
     simp only [NJV_AdoptedObservation.history,List.length_map]
   rw [←lengths]
   exact take_prefix _ _ _ (by rw [lengths];exact packet.1)
 · rw [pending]
   exact packet.2

set_option pp.proofs false
#print tx2
#print axioms take_prefix
#print axioms pending
#print axioms tx2
end NKV_AbortPrefix
end
