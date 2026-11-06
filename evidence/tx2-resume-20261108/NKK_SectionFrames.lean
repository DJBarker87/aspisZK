import NJZ_CheckpointReaders
import CheckpointBytes4SectionContents
set_option autoImplicit false
noncomputable section
namespace NKK_SectionFrames
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
abbrev K := aspis_core.field.QM31

/-- SAME semantic child output determines the next Reader cursor. A successful
branch is inspected locally; no independent child-success root premise. -/
theorem semantic (bytes : Slice U8) (start finish : Usize)
 (values : Array K 10#usize) (bound : start.val+160≤bytes.val.length)
 (returned : NIL_FreshOps.semantic bytes start=ok (.Ok (values,finish))) :
 finish.val=start.val+160 := by
 unfold NIL_FreshOps.semantic at returned
 cases call : CheckpointBytes4Ops.readSemanticAlpha bytes start with
 | fail err => simp only [NIL_Carriers.outer,call] at returned;cases returned
 | div => simp only [NIL_Carriers.outer,call] at returned;cases returned
 | ok inner =>
  cases inner with
  | Err err => simp only [NIL_Carriers.outer,call,NIL_Carriers.unInner] at returned;cases returned
  | Ok pair =>
   rcases pair with ⟨old,last⟩
   obtain ⟨model,decode,contents,postCursor⟩:=CheckpointBytes4SectionContents.semantic_contents bytes start last old bound call
   simp only [NIL_Carriers.outer,call,NIL_Carriers.unInner] at returned
   have same:=core.result.Result.Ok.inj (Result.ok.inj returned)
   have cursor:=congrArg Prod.snd same
   dsimp only at cursor
   exact (congrArg UScalar.val cursor).symm.trans postCursor

/-- The complete weight child output retains its width and determines the
final1736 cursor. All quantities come from the SAME entered owned vector. -/
theorem weights (bytes : Slice U8) (start finish : Usize)
 (before after : alloc.vec.Vec K)
 (bound : start.val+before.val.length*16≤bytes.val.length)
 (returned : NIL_FreshOps.weights bytes start before=ok (.Ok (after,finish))) :
 finish.val=start.val+before.val.length*16 ∧ after.val.length=before.val.length := by
 unfold NIL_FreshOps.weights at returned
 cases call : CheckpointBytes4Ops.readWeights bytes start (NIL_Carriers.vec NIL_Carriers.k before) with
 | fail err => simp only [NIL_Carriers.outer,call] at returned;cases returned
 | div => simp only [NIL_Carriers.outer,call] at returned;cases returned
 | ok inner =>
  cases inner with
  | Err err => simp only [NIL_Carriers.outer,call,NIL_Carriers.unInner] at returned;cases returned
  | Ok pair =>
   rcases pair with ⟨old,last⟩
   have oldBound : start.val+(NIL_Carriers.vec NIL_Carriers.k before).val.length*16≤bytes.val.length := by
    simpa only [NIL_Carriers.vec,List.length_map] using bound
   obtain ⟨model,decode,contents,cursor⟩:=CheckpointBytes4SectionContents.weights_contents
    bytes start last (NIL_Carriers.vec NIL_Carriers.k before) old oldBound call
   simp only [NIL_Carriers.outer,call,NIL_Carriers.unInner] at returned
   have same:=core.result.Result.Ok.inj (Result.ok.inj returned)
   have value:=congrArg Prod.fst same
   have atEq:=congrArg Prod.snd same
   dsimp only at value atEq
   constructor
   · simpa only [NIL_Carriers.vec,List.length_map] using (congrArg UScalar.val atEq).symm.trans cursor
   · rw [←value]
     simp only [NIL_Carriers.vec,contents,List.length_map,List.length_ofFn]

#print axioms semantic
#print axioms weights
end NKK_SectionFrames
