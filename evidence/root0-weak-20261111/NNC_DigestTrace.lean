import NNC_ResumeEvents
set_option autoImplicit false
noncomputable section
namespace NNC_DigestTrace
open Aeneas Aeneas.Std Result AspisR1
/-- Attempted syscalls retain their full partial reply. A separately stopped
syscall has no reply at all. Neither is replaced by a successful H answer. -/
inductive Step where
 | attempted (query : SdkC_Source.Query)
 | pending (parts : SdkC_Source.Parts)

abbrev Trace := List Step

def returning : Step → List NNC_WriteFree.ReadEvent
 | .attempted ⟨parts,.ok digest⟩ =>
   [⟨.digest (NNC_ResumeEvents.parts parts) (NNC_ResumeEvents.digest digest),by
      intro c b equal
      cases equal⟩]
 | _ => []

def render (trace : Trace) : List RSL.Event :=
 (trace.flatMap returning).map Subtype.val

def log (trace : Trace) : SdkC_Source.Log :=
 trace.filterMap (fun s => match s with | .attempted q => some q | .pending _ => none)

def pending (trace : Trace) : List SdkC_Source.Parts :=
 trace.filterMap (fun s => match s with | .attempted _ => none | .pending p => some p)

theorem render_append (a b : Trace) : render (a++b) = render a ++ render b := by
 simp only [render,List.flatMap_append,List.map_append]

theorem log_attempted (queries : SdkC_Source.Log) :
 log (queries.map Step.attempted) = queries := by
 induction queries with
 | nil => rfl
 | cons q rest ih => simpa only [List.map_cons,log,List.filterMap_cons] using congrArg (List.cons q) ih

theorem no_pending (queries : SdkC_Source.Log) : pending (queries.map Step.attempted) = [] := by
 induction queries with
 | nil => rfl
 | cons q rest ih => simpa only [List.map_cons,pending,List.filterMap_cons] using ih

theorem no_write (trace : Trace) (c : Nat) (bytes : RSL.Bytes) :
 RSL.Event.write c bytes ∉ render trace := by
 intro member
 obtain ⟨e,_,equal⟩ := List.mem_map.mp member
 exact e.property c bytes equal

/-- A pending native request survives in the trace with NO invented digest,
no result event and no source suffix. -/
theorem stopped (queries : SdkC_Source.Log) (parts : SdkC_Source.Parts) :
 log (queries.map Step.attempted ++ [.pending parts]) = queries ∧
 pending (queries.map Step.attempted ++ [.pending parts]) = [parts] ∧
 render (queries.map Step.attempted ++ [.pending parts]) = render (queries.map Step.attempted) := by
 constructor
 · simp only [log,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,List.append_nil]
   exact log_attempted queries
 constructor
 · simp only [pending,List.filterMap_append,List.filterMap_cons,List.filterMap_nil]
   rw [show List.filterMap (fun s => match s with | .attempted _ => none | .pending p => some p)
     (queries.map Step.attempted) = [] from no_pending queries]
   rfl
 · rw [render_append]
   exact List.append_nil _

#print axioms render_append
#print axioms log_attempted
#print axioms no_pending
#print axioms no_write
#print axioms stopped
end NNC_DigestTrace
