import NGQ_TraceErase
set_option autoImplicit false
namespace AspisR1.NGQ_Embed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Blocks := Array (Array U8 32#usize) 8#usize
abbrev Decode := Blocks → Blocks → Result (core.result.Result
  (Array U32 22#usize × Array U8 32#usize) aspis_core.transcript.QuerySampleError)

def boundaries (decode : Decode) : QueriesModel.Boundaries :=
  ⟨decode,AspisS1M31Embedding.Total.embed⟩

/-- The selected emitted constructor is total even before the sampler's
18-bit output bound is used. No accepted-run premise is required. -/
theorem total (decode : Decode) (m : aspis_core.field.M31) :
    ∃ e, (boundaries decode).embed m=ok e := by
  exact ⟨_,AspisS1M31Embedding.Total.embed_total m⟩

theorem finish {H : Type} (D : aspis_core.Digest32 H)
    (before : transcript.Transcript H) (decode : Decode)
    (blocks advances : Blocks) (q : Array U32 22#usize)
    (selected : Array U8 32#usize)
    (call : decode blocks advances=ok (.Ok (q,selected))) :
    NGQ_QueryFactor.finishQuery (boundaries decode) D before blocks advances=
      ok (.Ok q,{before with state:=selected}) :=
  NGQ_TraceErase.finish_success _ D before blocks advances q selected call (total decode)
#print axioms total
#print axioms finish
end AspisR1.NGQ_Embed
