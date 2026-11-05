import NGV_SemanticStep
import NGV_RowFrame
import NCO_LoopSteps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_SemanticTrace
open AspisS1NativeCompact NGV_RowPayload
/-- The original 27-row native schedule, with same-output local write packets.
No whole-call output equality or successful emitted execution is a field. -/
inductive Run (input : Slice U8) : Nat → Slice U8 → Slice U8 → Prop where
 | done (before : Slice U8) : Run input 27 before before
 | next (r : Nat) (before : Slice U8) (live : r<27) (packet : Packet input before r)
   (final : Slice U8) (rest : Run input (r+1) (after packet) final) : Run input r before final
/-- Construct every local callee/frame packet, then the finite original trace. -/
theorem construct (input before : Slice U8) (r : Nat) (bound : r≤27)
 (inputSize : input.val.length=7015) (outputSize : before.val.length=13831) :
 ∃ final,Run input r before final := by
 have aux : ∀ (fuel r : Nat),27-r=fuel → r≤27 → ∀ before : Slice U8,
   before.val.length=13831 → ∃ final,Run input r before final := by
   intro fuel
   induction fuel with
   | zero =>
     intro r remaining bound before size
     have finish:r=27 := by omega
     subst r
     exact ⟨before,.done before⟩
   | succ fuel ih =>
     intro r remaining bound before size
     have live:r<27 := by omega
     obtain ⟨packet⟩:=NGV_RowPayload.construct input before r live inputSize size
     obtain ⟨final,rest⟩:=ih (r+1) (by omega) (by omega) (after packet)
       ((NGV_RowPayload.length packet).trans size)
     exact ⟨final,.next r before live packet final rest⟩
 exact aux (27-r) r rfl bound before outputSize
/-- Full result association by finite Lean induction, using ONE original
emitted step on arbitrary prestate and the actual stop terminal. -/
theorem result (input : Slice U8) (r : Nat) (before final : Slice U8)
 (run : Run input r before final) :
 ∀ (bound : r≤27) (inputSize : input.val.length=7015) (outputSize : before.val.length=13831)
   (row : U8) (same : row.val=r),
 compact.expand_semantic_loop AspisS1ValuesOwnedInstallation.nativeValues
   {start:=row,«end»:=27#u8} input before (NGV_Cursors.src r bound) (NGV_Cursors.dst r bound)=
 ok (.Ok (),final) := by
 induction run with
 | done before =>
   intro bound inputSize outputSize row same
   have rowEq:row=27#u8 := UScalar.eq_of_val_eq same
   subst row
   have sourceEq : NGV_Cursors.src 27 bound=Slice.len input := by
     apply UScalar.eq_of_val_eq;change 7015=input.val.length;exact inputSize.symm
   have outputEq : NGV_Cursors.dst 27 bound=Slice.len before := by
     apply UScalar.eq_of_val_eq;change 13831=before.val.length;exact outputSize.symm
   have stop : core.iter.range.IteratorRange.next core.iter.range.StepU8
     ({start:=27#u8,«end»:=27#u8}:core.ops.range.Range U8)=ok (none,{start:=27#u8,«end»:=27#u8}) := by rfl
   unfold compact.expand_semantic_loop
   apply NCO_LoopSteps.loop_done
   simp only [compact.expand_semantic_loop.body,stop,bind_tc_ok,sourceEq,outputEq,bne_self_eq_false,Bool.false_eq_true,if_false]
   rfl
 | next r before live packet final rest ih =>
   intro bound inputSize outputSize row same
   subst r
   obtain ⟨next,nextValue,step⟩:=NGV_SemanticStep.result input before row live inputSize outputSize packet
   have tail:=ih (by omega) inputSize ((NGV_RowPayload.length packet).trans outputSize) next nextValue
   unfold compact.expand_semantic_loop at tail ⊢
   let body : NGV_SemanticCut.State → Result (ControlFlow NGV_SemanticCut.State NGV_SemanticCut.Exit) :=
     fun (it,buf,s,d)=>compact.expand_semantic_loop.body AspisS1ValuesOwnedInstallation.nativeValues input it buf s d
   rw [NCO_LoopSteps.loop_continue body
     (({start:=row,«end»:=27#u8},before,NGV_Cursors.src row.val bound,NGV_Cursors.dst row.val bound):NGV_SemanticCut.State)
     (({start:=next,«end»:=27#u8},after packet,NGV_Cursors.src (row.val+1) (by omega),NGV_Cursors.dst (row.val+1) (by omega)):NGV_SemanticCut.State) step]
   exact tail
#print axioms construct
#print axioms result
end NGV_SemanticTrace
