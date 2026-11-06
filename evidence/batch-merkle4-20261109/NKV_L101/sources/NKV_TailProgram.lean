import NKV_TailContinue
set_option autoImplicit false
noncomputable section
namespace NKV_TailProgram
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
open AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

theorem source (p : OraclePortCompactDraft.Parsed) (batch kind : Nat) (nodes : Slice U8)
 (s : reference.Scratch) (width : nodes.val.length=32*OraclePortSelectedDraft.capacity (3*batch+kind))
 (root : Array U8 32#usize) (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot p kind)) :
 MultiproofConeVerifyState.tailState p batch kind nodes s=
 (if OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s) then
   if OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)≤OraclePortSelectedDraft.capacity (3*batch+kind) ∧
     MultiproofConePadding.scan
       (4*(OraclePortSelectedDraft.capacity (3*batch+kind)-OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
       ((MultiproofConeCanonical.bytesOf nodes.val).drop (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))=true then
     NJV_TX2Returning.endpoint root
       (MultiproofConeSlotTail.prefixNodes nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s))) s.idx s.val s.n
   else .done (false,s)
  else .done (false,s)) := by
 have countValue : MultiproofConeSlotTail.slotCount s=OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s) :=
   MultiproofConeSlotTail.slot_count_eq s
 have byteWidth : (MultiproofConeCanonical.bytesOf nodes.val).length=32*OraclePortSelectedDraft.capacity (3*batch+kind) := by
   simpa only [MultiproofConeCanonical.bytesOf,List.length_map] using width
 have initial : {s with «at»:=0#usize}=NJV_EntryABI.initial s.idx s.val s.n := by cases s;rfl
 unfold MultiproofConeVerifyState.tailState
 change (if OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s) then _ else _)=_
 rw [countValue]
 simp only [byteWidth,and_true,true_and,initial,NJV_TX2Returning.endpoint,rootValue]

set_option pp.proofs false
#print source
#print axioms source
end NKV_TailProgram
end
