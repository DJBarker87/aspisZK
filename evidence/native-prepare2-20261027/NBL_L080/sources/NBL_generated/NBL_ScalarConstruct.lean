import NBL_BlockTrace
import NBA_SamplerValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_ScalarConstruct
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Once ONE native block trace is linked, the installed scalar output is
constructed. A chosen successful sampler result is not a hypothesis. -/
theorem source {H : Type} (D : aspis_core.Digest32 H)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (nonzero : Bool) (b : NBL_BlockTrace.Block D before row payload) :
    ∃ s : NBL_BlockTrace.Scalar D before row payload nonzero,
      s.block=b := by
  cases nonzero with
  | true =>
    obtain ⟨out,call,canonical,rank⟩ := NBA_SamplerValues.gamma b.value
    exact ⟨⟨b,out,call⟩,rfl⟩
  | false =>
    obtain ⟨raw,call,mapped,canonical⟩ := NBA_SamplerValues.ordinary b.value
    exact ⟨⟨b,_,mapped⟩,rfl⟩

#print axioms source
end AspisR1.NBL_ScalarConstruct
end
