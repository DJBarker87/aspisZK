import PV_L1_QueryProducer
set_option autoImplicit false
noncomputable section
namespace PV_L1_QueryRecord
open Aeneas Aeneas.Std Result ProverRwFull
open PV_L1_QueryProducer
variable [ExternalTypes] [ExternalFuns]
variable {H : Type}

/-- The source return itself determines the complete instrumented record:
ordered digest entries, exact success/error and the entire returned state. -/
theorem of_source (hash : aspis_core.digest.Digest32 H)
    (s : host_transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : core.result.Result (Array U32 22#usize) verifier.Error × host_transcript.Transcript H)
    (executed : host_transcript.Transcript.queries hash s row payload = ok out) :
    produce hash s row payload = ⟨readOrder,ok out⟩ := by
  have hr : (produce hash s row payload).result = ok out :=
    (complete_result hash s row payload).trans executed
  have he := completed_order hash s row payload out hr
  cases hp : produce hash s row payload with
  | mk events result =>
    rw [hp] at hr he
    cases hr
    cases he
    rfl
#print axioms of_source

theorem abort_record (hash : aspis_core.digest.Digest32 H)
    (s after : host_transcript.Transcript H) (row : U8) (payload : Slice U8)
    (executed : host_transcript.Transcript.queries hash s row payload =
      ok (.Err .Transcript,after)) :
    produce hash s row payload = ⟨readOrder,ok (.Err .Transcript,after)⟩ :=
  of_source hash s row payload _ executed
#print axioms abort_record

theorem digest_count (hash : aspis_core.digest.Digest32 H)
    (s : host_transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : core.result.Result (Array U32 22#usize) verifier.Error × host_transcript.Transcript H)
    (executed : host_transcript.Transcript.queries hash s row payload = ok out) :
    (produce hash s row payload).events.length = 17 := by
  rw [of_source hash s row payload out executed]
  simp only [readOrder,List.length_cons,List.length_map,List.length_range]
#print axioms digest_count
end PV_L1_QueryRecord
