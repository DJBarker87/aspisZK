import R1Z.PV_Canon_Semantic
import R1Z.PV_Join_PublicCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem current_sampler_law (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base)) :
    @SamplerLaw (PV_Join_PublicCaller.native base) (PV_Join_PublicCaller.selected base ops) := by
  intro bytes
  change Safe Q (ProverRwFullSampler.selected bytes)
  exact safe_of_total (sampler_total bytes)
 theorem current_semantic (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    {H : Type} (digest : aspis_core.digest.Digest32 H)
    (s after : host_wire.SemanticTranscript H) (row : U8) (framed : Slice U8)
    (q : aspis_core.field.QM31)
    (h : @host_wire.SemanticTranscript.semantic (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) H digest s row framed = .ok (.Ok q,after)) : Q q := by
  have hs := @semantic_safe (PV_Join_PublicCaller.native base)
    (PV_Join_PublicCaller.selected base ops) (current_sampler_law base ops) H digest s row framed
  exact hs (.Ok q,after) h q rfl
#print axioms current_sampler_law
#print axioms current_semantic
end R1Z.PV_Canon
