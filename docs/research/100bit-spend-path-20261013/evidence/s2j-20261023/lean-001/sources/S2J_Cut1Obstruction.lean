import S2H_CutRelation
import S2F_Sequence

/-! First-cut interface diagnostic, not a native same-input counterexample.
CutRelated does not observe the native invocation. Adding that port is a
necessary representation obligation; no successful caller fact is assumed. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2J
open S2Trust S2H S2E_Reference.S2E_Reference

structure Invocation where
  instruction : Slice U8
  accountCount : Usize

/-- The SDK interpretation observes only W. The additional invocation remains
part of native state but no inherited Library observation reads it. -/
def withInvocation {W F : Type} (L : Library W F) : Library (W × Invocation) F where
  related := fun n h => L.related n.1 h
  accountData := fun n => L.accountData n.1
  accountLamports := fun n => L.accountLamports n.1
  cellPayload := fun n => L.cellPayload n.1
  cellCounter := fun n => L.cellCounter n.1
  liveGuard := fun n => L.liveGuard n.1
  allocated := fun n => L.allocated n.1
  run := fun n op => let next := L.run n.1 op; ((next.1,n.2),next.2)

/-- Exact blindness of the inherited full relation, not a finite projection. -/
theorem invocation_blind {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event))
    (o : Originals (W × Invocation) Child Alloc Event) (n : W)
    (r : OwnedCut Child Alloc Event) (a b : Invocation) :
    CutRelated (withInvocation L) o (n,a) r ↔
      CutRelated (withInvocation L) o (n,b) r := by
  constructor <;> intro h
  · exact ⟨h.nativeHeap,h.valid,h.image,h.ambient,h.program,h.instruction,h.tokens⟩
  · exact ⟨h.nativeHeap,h.valid,h.image,h.ambient,h.program,h.instruction,h.tokens⟩

/-- Source cut1 decision, before any account indexing, SDK or child call. -/
def shapeDecision (a : Invocation) : Bool :=
  if (a.instruction.val = [3#u8,10#u8] ∨ a.instruction.val = [3#u8,11#u8]) ∧
    a.accountCount = 3#usize then true else false

def acceptedArgs : Invocation := ⟨(Array.make 2#usize [3#u8,10#u8]).to_slice,3#usize⟩
def rejectedArgs : Invocation := ⟨(Array.make 0#usize []).to_slice,3#usize⟩

theorem decisions_differ : shapeDecision acceptedArgs ≠ shapeDecision rejectedArgs := by
  decide

/-- Even an existing full related cut can be paired with different native
invocation decisions. This does NOT claim that the runtime admits those pairs
as executions on the same external input. That missing binding is the point. -/
theorem cut1_relation_insufficient {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event))
    (o : Originals (W × Invocation) Child Alloc Event) (n : W)
    (r : OwnedCut Child Alloc Event)
    (related : CutRelated (withInvocation L) o (n,acceptedArgs) r) :
    CutRelated (withInvocation L) o (n,rejectedArgs) r ∧
      shapeDecision acceptedArgs ≠ shapeDecision rejectedArgs :=
  ⟨(invocation_blind L o n r acceptedArgs rejectedArgs).mp related,decisions_differ⟩

#print axioms invocation_blind
#print axioms decisions_differ
#print axioms cut1_relation_insufficient
end AspisR1.S2J
