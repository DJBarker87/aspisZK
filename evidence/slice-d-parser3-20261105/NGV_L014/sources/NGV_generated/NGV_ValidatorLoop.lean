import NGV_ValidatorStep
import NGO_ScheduleState
import NFU_CompactLeaves
import NCO_LoopSteps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ValidatorLoop
open AspisR1PrefixAggregateParser NGO_ScheduleState
abbrev CE := NGO_ScheduleState.CE
def reply (row : U8) : Option Nat → Result (core.result.Result Unit r1_wire.Error)
 | none => ok (.Ok ())
 | some i => if h : i≤UScalar.cMax .Usize then ok (.Err (.NonCanonical row (UScalar.ofNat i h))) else fail .panic
theorem window (bytes : Slice U8) (ce : CE)
 (values : ce.chunks.map (fun c=>c.val)=NGO_ChunkSchedule.windows bytes.val (bytes.val.length/32))
 (i : Nat) (live : i<bytes.val.length/32) :
 (ce.chunks[i]'(by have h:=congrArg List.length values;simp only [List.length_map,NGO_ChunkSchedule.window_count] at h;omega)).val =
 (bytes.val.drop (32*i)).take 32 := by
 have len : ce.chunks.length=bytes.val.length/32 := by
   have h:=congrArg List.length values
   simpa only [List.length_map,NGO_ChunkSchedule.window_count] using h
 have h:=congrArg (fun xs : List (List U8)=>xs[i]?) values
 simpa only [List.getElem?_map,List.getElem?_eq_getElem (by omega : i<ce.chunks.length),
   List.getElem?_eq_getElem (by rw [NGO_ChunkSchedule.window_count];exact live),Option.map_some,
   NGO_ChunkSchedule.window_at,Option.some.injEq] using h
theorem result (row : U8) (bytes : Slice U8) (ce : CE)
 (values : ce.chunks.map (fun c=>c.val)=NGO_ChunkSchedule.windows bytes.val (bytes.val.length/32))
 (bound : bytes.val.length≤3712)
 (i : Nat) (out : Option Nat)
 (trace : NFU_Retarget.LPl.Scan.Trace (NFU_Retarget.LPl.Validate.predicate bytes.val) (bytes.val.length/32) i out)
 (count : Usize) (same : count.val=i) :
 r1_wire.validate_record_fields_loop (state ce count) row=reply row out := by
 have len : ce.chunks.length=bytes.val.length/32 := by
   have h:=congrArg List.length values
   simpa only [List.length_map,NGO_ChunkSchedule.window_count] using h
 induction trace generalizing count with
 | done i ended =>
   unfold r1_wire.validate_record_fields_loop
   apply NCO_LoopSteps.loop_done
   simp [r1_wire.validate_record_fields_loop.body,NGO_ScheduleState.stop ce count (by omega),reply]
 | reject i live bad =>
   let finish : Usize:=UScalar.ofNat (bytes.val.length/32) (by scalar_tac)
   obtain ⟨next,addition,advance⟩:=WP.spec_imp_exists (UScalar.add_spec (x:=count) (y:=1#usize) (by scalar_tac))
   obtain ⟨chunk,native,selected⟩:=NGO_ScheduleState.step ce count finish next len (by simpa [finish,same] using live) (by simpa using advance)
   have original : chunk.val=(bytes.val.drop (32*i)).take 32 := by
     rw [←selected];simpa only [same] using window bytes ce values count.val (by simpa [same] using live)
   have size : chunk.val.length=32 := by rw [original];simp only [List.length_take,List.length_drop];omega
   have rejects : NFU_Retarget.LPl_Kit_Bytes.validChunk 8 true chunk.val=false := by
     simpa only [NFU_Retarget.LPl.Validate.predicate,NFU_Retarget.LPl.Echeck.chunk_eq,original] using bad
   unfold r1_wire.validate_record_fields_loop
   apply NCO_LoopSteps.loop_done
   have step:=NGV_ValidatorStep.step row (state ce count) (state ce next) count chunk native size
   have port : UScalar.ofNat i (by scalar_tac)=count := UScalar.eq_of_val_eq same.symm
   simpa [rejects,reply,show i≤UScalar.cMax .Usize by scalar_tac,port] using step
 | next i live good out rest ih =>
   let finish : Usize:=UScalar.ofNat (bytes.val.length/32) (by scalar_tac)
   obtain ⟨next,addition,advance⟩:=WP.spec_imp_exists (UScalar.add_spec (x:=count) (y:=1#usize) (by scalar_tac))
   obtain ⟨chunk,native,selected⟩:=NGO_ScheduleState.step ce count finish next len (by simpa [finish,same] using live) (by simpa using advance)
   have original : chunk.val=(bytes.val.drop (32*i)).take 32 := by
     rw [←selected];simpa only [same] using window bytes ce values count.val (by simpa [same] using live)
   have size : chunk.val.length=32 := by rw [original];simp only [List.length_take,List.length_drop];omega
   have accepts : NFU_Retarget.LPl_Kit_Bytes.validChunk 8 true chunk.val=true := by
     simpa only [NFU_Retarget.LPl.Validate.predicate,NFU_Retarget.LPl.Echeck.chunk_eq,original] using good
   unfold r1_wire.validate_record_fields_loop at ih ⊢
   rw [NCO_LoopSteps.loop_continue _ (state ce count) (state ce next) (by
     simpa only [accepts,if_true] using NGV_ValidatorStep.step row (state ce count) (state ce next) count chunk native size)]
   exact ih next (by simpa [same] using advance)
#print axioms window
#print axioms result
end NGV_ValidatorLoop
