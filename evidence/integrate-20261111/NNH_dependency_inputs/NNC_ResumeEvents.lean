import NNC_WriteFree
import RPz8_ARW_LocalBudget
set_option autoImplicit false
noncomputable section
namespace NNC_ResumeEvents
open Aeneas Aeneas.Std Result AspisR1
/-- Exact byte parts, without collapsing their syscall partition. -/
def parts (chunks : Slice (Slice U8)) : List RSL.Bytes :=
 chunks.val.map (fun s => NNC_ByteCarriers.host s.val)

def digest (out : Array U8 32#usize) : RSL.B32 :=
 ⟨NNC_ByteCarriers.host out.val,by
   have h := out.property
   change out.val.length = 32 at h
   simpa only [NNC_ByteCarriers.host,List.length_map] using h⟩

/-- Every attempted native digest is retained, including fail/div. It is not
safe to recover this complete trace from its answered-query projection alone. -/
def query (event : NJU_ResumeObserved.Event) : List SdkC_Source.Query :=
 match event with
 | .digest chunks reply => [⟨chunks,reply⟩]
 | _ => []

def queries (events : List NJU_ResumeObserved.Event) : SdkC_Source.Log := events.flatMap query

/-- RSL has a completed-digest event only when there is a returned digest.
The complete failed/pending native query is still retained by `queries`. -/
def returning (event : NJU_ResumeObserved.Event) : List NNC_WriteFree.ReadEvent :=
 match event with
 | .digest chunks (.ok out) => [⟨RSL.Event.digest (parts chunks) (digest out),by
     intro c b equal
     cases equal⟩]
 | _ => []

def render (events : List NJU_ResumeObserved.Event) : List RSL.Event :=
 (events.flatMap returning).map Subtype.val

theorem attempted (chunks : Slice (Slice U8)) (reply : Result (Array U8 32#usize)) :
 queries [.digest chunks reply] = [⟨chunks,reply⟩] := rfl

theorem returned (chunks : Slice (Slice U8)) (out : Array U8 32#usize) :
 render [.digest chunks (.ok out)] = [RSL.Event.digest (parts chunks) (digest out)] := rfl

theorem queries_append (a b : List NJU_ResumeObserved.Event) :
 queries (a++b) = queries a ++ queries b := List.flatMap_append

theorem render_append (a b : List NJU_ResumeObserved.Event) :
 render (a++b) = render a ++ render b := by
 simp only [render,List.flatMap_append,List.map_append]

theorem no_write (events : List NJU_ResumeObserved.Event) (c : Nat) (b : RSL.Bytes) :
 RSL.Event.write c b ∉ render events := by
 intro member
 obtain ⟨e,_,equal⟩ := List.mem_map.mp member
 exact e.property c b equal

/-- The source/native resume equality preserves the COMPLETE attempted-query
trace at these SAME records, on ALL results. No Root0 or digest totality. -/
theorem native_source {X : Type} (d : VTop_Stages.aspis_core.digest.Digest32 X)
 (ck proof pub : Slice U8) (hash : X) (reservation : NP6_StdModel.Reservation) :
 queries (NLT_NativeWindows.resumeRun d ck proof pub hash reservation).events =
 queries (NJU_ResumeObserved.run reservation (NJC_ResumeCalls.digest d)
   ck proof pub .S2 hash).events := by
 unfold NLT_NativeWindows.resumeRun
 rw [NKU_ParentFold.source]
 rfl

#print axioms attempted
#print axioms returned
#print axioms queries_append
#print axioms render_append
#print axioms no_write
#print axioms native_source
end NNC_ResumeEvents
