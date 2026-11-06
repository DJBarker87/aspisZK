import NKV_ConcreteDomains
import NKV_TailArithmetic
import Port4B_Capacity
set_option autoImplicit false
noncomputable section
namespace NKV_SlotInvocation
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

theorem capacity (slot : Usize) (bound : slot.val<6) :
 ∃ cap,Array.index_usize (Array.make 6#usize
   [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize]) slot=ok cap ∧
 cap.val=OraclePortSelectedDraft.capacity slot.val ∧ cap.val≤172 := by
 have cases : slot.val=0 ∨ slot.val=1 ∨ slot.val=2 ∨ slot.val=3 ∨ slot.val=4 ∨ slot.val=5 := by omega
 rcases cases with h|h|h|h|h|h
 all_goals
   simp only [Array.index_usize,Array.make,Array.getElem?_Usize_eq,h]
   simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]
   first
   | exact ⟨146#usize,rfl,rfl,by scalar_tac⟩
   | exact ⟨128#usize,rfl,rfl,by scalar_tac⟩
   | exact ⟨172#usize,rfl,rfl,by scalar_tac⟩
   | exact ⟨150#usize,rfl,rfl,by scalar_tac⟩

theorem physical (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (batch kind : Nat) (hb : batch<2) (hk : kind<3) (slot : Usize) (value : slot.val=3*batch+kind) :
 ∃ view,(NKV_ConcreteChildren.ops H).op3 proof slot=ok view ∧
 view.val.length=32*OraclePortSelectedDraft.capacity (3*batch+kind) ∧
 MultiproofConeCanonical.bytesOf view.val=OraclePortCompactDraft.slice p.wire
   (OraclePortSelectedDraft.slotStart (3*batch+kind)) (32*OraclePortSelectedDraft.capacity (3*batch+kind)) := by
 obtain ⟨view,run,width,bytes⟩:=Port4B_SlotInstall.physical proof len p wire batch kind hb hk slot value
 refine ⟨view,?_,width,bytes⟩
 change NJS_Extract.verifier.candidate.slot NGD_SlotRef.slot_offset proof slot=ok view
 rw [NJS_Slot.source proof slot (by omega)]
 exact run

set_option pp.proofs false
#print capacity
#print physical
#print axioms capacity
#print axioms physical
end NKV_SlotInvocation
end
