import NKV_LeafTotal
set_option autoImplicit false
noncomputable section
namespace NKV_LeafSlot
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def following (H : Bytes → State) (p : OraclePortCompactDraft.Parsed) (batch kind : Nat)
 (nodes : Slice U8) (before : reference.Scratch) : Result NKV_LeafBuild.Answer →
   List (Bytes × State) × (Bool × reference.Scratch)
 | .ok (true,after) => eval H (MultiproofConeVerifyState.tailState p batch kind nodes after)
 | _ => ([],(false,before))

/-- Complete adopted slot decomposition, including leaf rejection and exact
chronological prefix. The adopted model is read-only. -/
theorem source (H : Bytes → State) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) (nodes : Slice U8) (before : reference.Scratch) :
 eval H (MultiproofConeSlotState.slotState p q batch kind nodes before)=
 (let leaf:=NKV_LeafBuild.build H p q kind (OraclePortFrozenOrder.sortedPositions q batch kind)
     (MultiproofConeSlotState.reset before)
  let tail:=following H p batch kind nodes before leaf.2
  (leaf.1++tail.1,tail.2)) := by
 unfold MultiproofConeSlotState.slotState
 rw [eval_bind,NKV_LeafBuild.adopted]
 cases run : (NKV_LeafBuild.build H p q kind (OraclePortFrozenOrder.sortedPositions q batch kind)
     (MultiproofConeSlotState.reset before)).2 with
 | fail e => rfl
 | div => rfl
 | ok out => rcases out with ⟨keep,s⟩;cases keep <;> rfl

/-- A rejected leaf consumes exactly its already-proved prefix and enters
neither padding nor the verifier, independently of every remaining H value. -/
theorem rejected (H : Bytes → State) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) (nodes : Slice U8) (before bad : reference.Scratch)
 (reject : (NKV_LeafBuild.build H p q kind (OraclePortFrozenOrder.sortedPositions q batch kind)
   (MultiproofConeSlotState.reset before)).2=ok (false,bad)) :
 eval H (MultiproofConeSlotState.slotState p q batch kind nodes before)=
 ((NKV_LeafBuild.build H p q kind (OraclePortFrozenOrder.sortedPositions q batch kind)
   (MultiproofConeSlotState.reset before)).1,(false,before)) := by
 rw [source,reject]
 simp only [following,List.append_nil]

set_option pp.proofs false
#print source
#print rejected
#print axioms source
#print axioms rejected
end NKV_LeafSlot
end
