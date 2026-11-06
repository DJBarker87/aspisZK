import NJP_CheckedWords
import NJP_RequestTransport
import MultiproofConePhysicalProgram

set_option autoImplicit false
noncomputable section
namespace NJP_CohortWrite
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def projectRow : reference.Row → NJP_RowModel.Row
 | .Stop s => .stop (raw s)
 | .Next s i w => .next (raw s) i.val w.val

def mapResult {α β : Type} (f : α → β) : Result α → Result β
 | .ok x => .ok (f x)
 | .fail e => .fail e
 | .div => .div

theorem finish (s : reference.Scratch) (digest : RefDigest) (ni cursor : Usize)
    (index : U32) (i : Nat) (w : Usize) (bound : w.val<16)
    (index_value : index.val=NJP_RowModel.index (raw s) i) :
 mapResult projectRow (AspisR1.MultiproofConePhysicalProgram.finish s digest ni cursor index w)=
 ok (.next (NJP_RowModel.write (raw s) i w.val cursor.val (decode digest)) ni.val (w.val+1)) := by
 obtain ⟨parent,division,parent_value⟩ := NJP_CheckedWords.half index
 obtain ⟨next,addition,next_value⟩ := NJP_CheckedWords.add_one w bound
 unfold AspisR1.MultiproofConePhysicalProgram.finish
 rw [division]
 simp only [bind_tc_ok]
 rw [NJE_CountArithmetic.update_result s.idx w parent bound]
 simp only [bind_tc_ok]
 rw [NJE_CountArithmetic.update_result s.val w digest bound]
 simp only [bind_tc_ok]
 rw [addition]
 simp only [bind_tc_ok,mapResult,projectRow]
 rw [NJP_WriteCarrier.complete_write s _ w cursor parent digest bound (by rw [parent_value,index_value]),next_value]

theorem writer (H : Slice (Slice U8) → RefDigest) (s : reference.Scratch)
    (left right : RefDigest) (ni cursor : Usize) (index : U32) (i : Nat) (w : Usize)
    (bound : w.val<16) (index_value : index.val=NJP_RowModel.index (raw s) i) :
 let observed := eval H (AspisR1.MultiproofConePhysicalProgram.writer s left right ni cursor index w)
 (observed.1,mapResult projectRow observed.2)=
 ([(AspisR1.MultiproofConePhysicalDigest.parts left right,H (AspisR1.MultiproofConePhysicalDigest.parts left right))],
  ok (.next (NJP_RowModel.write (raw s) i w.val cursor.val
    (decode (H (AspisR1.MultiproofConePhysicalDigest.parts left right)))) ni.val (w.val+1))) := by
 dsimp only
 simp only [AspisR1.MultiproofConePhysicalProgram.writer,eval]
 rw [finish s _ ni cursor index i w bound index_value]

#print finish
#print axioms finish
#print writer
#print axioms writer
end NJP_CohortWrite
end
