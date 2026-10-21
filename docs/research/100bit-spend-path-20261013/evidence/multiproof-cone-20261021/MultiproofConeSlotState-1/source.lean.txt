import MultiproofConeVerifyState
import MultiproofConeLeafFrozen

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeSlotState
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalViews MultiproofConePhysicalTransport
open MultiproofConeLeafFold MultiproofConeVerifyState MultiproofConeSlotTail
open OraclePortFrozenOrder OraclePortSelectedDraft OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- n and the node cursor are local to each batch_tree call. The shared idx
and val buffers are retained from the preceding slot, including their suffix. -/
def reset (s : reference.Scratch) : reference.Scratch := {s with n:=0#usize,«at»:=0#usize}

def slotState (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat)
    (nodes : Slice U8) (s : reference.Scratch) : Program Bytes State (Bool × reference.Scratch) :=
  bind (leaves p q kind (sortedPositions q batch kind) (reset s)) fun out =>
    match out with
    | .ok (some after) => tailState p batch kind nodes after
    | _ => .done (false,s)

/-- One accepted physical leaf/count/padding/root slot, retaining source
scratch for the next call and preserving all chronological oracle observations. -/
theorem accepted_slot {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input=ok (rawOracle H input))
    (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat)
    (nodes : Slice U8) (s : reference.Scratch)
    (view : MultiproofConeCanonical.bytesOf nodes.val=
      slice p.wire (slotStart (3*batch+kind)) (32*capacity (3*batch+kind)))
    (accepted : (eval H (slotState p q batch kind nodes s)).2.1=true) :
    ((eval H (slotState p q batch kind nodes s)).1,
      (eval H (slotState p q batch kind nodes s)).2.1)=
      eval H (verifySlot_frozen p q batch kind) := by
  have room : (reset s).n.val+(sortedPositions q batch kind).length≤16 := by
    have bound := MultiproofConeLeafFrozen.sorted_length q batch kind
    change 0+_≤16;omega
  obtain ⟨log,out,source,target,_⟩ := leaves_join H p q kind (sortedPositions q batch kind) (reset s) room
  have frozen := model_frozen H p q kind (sortedPositions q batch kind) (revLive (reset s))
  rw [target] at frozen
  have empty : revLive (reset s)=[] := rfl
  rw [empty] at frozen
  cases out with
  | none =>
    simp only [slotState,eval_bind,source,eval] at accepted
    cases accepted
  | some after =>
    have tailAccepted : (eval H (tailState p batch kind nodes after)).2.1=true := by
      simpa only [slotState,eval_bind,source] using accepted
    have projection := tail_projection H p batch kind nodes after
    have tailOK : (eval H (tail p batch kind nodes after)).2=true := by
      rw [←projection];exact tailAccepted
    have joined := accepted_tail D hash H law p batch kind nodes after view tailOK
    have leafTarget : eval H (hashLeaves p q kind (sortedPositions q batch kind) [])=
        (log,some (live after 0 after.n.val)) := by
      simpa only [Option.map_some,revLive,List.reverse_reverse] using frozen.symm
    simp only [slotState,verifySlot_frozen,eval_bind,source,leafTarget]
    rw [←joined,←projection]

#print axioms accepted_slot
end AspisR1.MultiproofConeSlotState
end
