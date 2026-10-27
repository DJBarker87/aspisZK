import R1Z.PV_Canon_D234Boundary
import R1Z.PV_Canon_CurrentSemantic
import R1Z.PV_Canon_ParseQ
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 def d234 : aspis_core.field.QM31 := ⟨⟨0#u32,2147483648#u32⟩,⟨0#u32,0#u32⟩⟩
 theorem d234_not_quartic : ¬ Q d234 := by
  intro h
  exact d234_outside_domain h.1.2
 theorem sampler_ne_d234 (bytes : Array U8 32#usize) :
    ProverRwFullSampler.selected bytes ≠ .ok d234 := by
  intro h
  obtain ⟨q,hq,hc⟩ := sampler_total bytes
  rw [h] at hq
  cases hq
  exact d234_not_quartic hc
 theorem parser_ne_d234 (bytes : Slice U8) :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes ≠ .ok (some d234) := by
  intro h
  exact d234_not_quartic (parse_qm31 bytes d234 h)
 theorem semantic_ne_d234 (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    {H : Type} (digest : aspis_core.digest.Digest32 H)
    (s after : host_wire.SemanticTranscript H) (tag : U8) (framed : Slice U8) :
    @host_wire.SemanticTranscript.semantic (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) H digest s tag framed ≠ .ok (.Ok d234,after) := by
  intro h
  exact d234_not_quartic (current_semantic base ops digest s after tag framed d234 h)
#print axioms d234_not_quartic
#print axioms sampler_ne_d234
#print axioms parser_ne_d234
#print axioms semantic_ne_d234
end R1Z.PV_Canon
