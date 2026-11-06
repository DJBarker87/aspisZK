import NKV_TailProgram
import NKV_LeafSlot
set_option autoImplicit false
noncomputable section
namespace NKV_QueryPlan
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
abbrev HashState := AspisV8R19.SourceDuplexStep.State
attribute [local instance] Classical.propDecidable

def tail (H : Bytes → HashState) (batch kind : Nat) (nodes : Slice U8)
 (root : Array U8 32#usize) (s : reference.Scratch) : List (Bytes × HashState) :=
 if OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s) then
   if OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)≤OraclePortSelectedDraft.capacity (3*batch+kind) ∧
     MultiproofConePadding.scan
       (4*(OraclePortSelectedDraft.capacity (3*batch+kind)-OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
       ((MultiproofConeCanonical.bytesOf nodes.val).drop (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))=true then
     (eval H (NJV_TX2Returning.endpoint root
       (MultiproofConeSlotTail.prefixNodes nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s))) s.idx s.val s.n)).1
   else []
 else []

theorem tail_history (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed) (batch kind : Nat)
 (nodes : Slice U8) (s : reference.Scratch) (width : nodes.val.length=32*OraclePortSelectedDraft.capacity (3*batch+kind))
 (root : Array U8 32#usize) (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot p kind)) :
 (eval H (MultiproofConeVerifyState.tailState p batch kind nodes s)).1=tail H batch kind nodes root s := by
 rw [NKV_TailProgram.source p batch kind nodes s width root rootValue]
 unfold tail
 by_cases well : OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s)
 · simp only [if_pos well]
   by_cases checks : OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)≤OraclePortSelectedDraft.capacity (3*batch+kind) ∧
     MultiproofConePadding.scan
       (4*(OraclePortSelectedDraft.capacity (3*batch+kind)-OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
       ((MultiproofConeCanonical.bytesOf nodes.val).drop (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))=true
   · simp only [if_pos checks]
   · simp only [if_neg checks,eval]
 · simp only [if_neg well,eval]

def plan (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) (nodes : Slice U8) (root : Array U8 32#usize)
 (before : reference.Scratch) : List (Bytes × HashState) :=
 let leaf:=NKV_LeafBuild.build H p q kind (OraclePortFrozenOrder.sortedPositions q batch kind)
   (MultiproofConeSlotState.reset before)
 leaf.1++match leaf.2 with | .ok (true,after) => tail H batch kind nodes root after | _ => []

/-- Exact adopted query history: source-ordered leaf prefix, followed by the
SAME verifier history only after every guard. This is not yet the complete
native invocation association, which remains the row-level obligation. -/
theorem slot_history (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) (nodes : Slice U8)
 (width : nodes.val.length=32*OraclePortSelectedDraft.capacity (3*batch+kind))
 (root : Array U8 32#usize) (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot p kind))
 (before : reference.Scratch) :
 (eval H (MultiproofConeSlotState.slotState p q batch kind nodes before)).1=
 plan H p q batch kind nodes root before := by
 rw [NKV_LeafSlot.source]
 unfold plan
 dsimp only
 cases run : (NKV_LeafBuild.build H p q kind (OraclePortFrozenOrder.sortedPositions q batch kind)
     (MultiproofConeSlotState.reset before)).2 with
 | fail e => rfl
 | div => rfl
 | ok out =>
   rcases out with ⟨keep,after⟩
   cases keep with
   | false => rfl
   | true => exact congrArg (List.append _) (tail_history H p batch kind nodes after width root rootValue)

set_option pp.proofs false
#print tail_history
#print slot_history
#print axioms tail_history
#print axioms slot_history
end NKV_QueryPlan
end
