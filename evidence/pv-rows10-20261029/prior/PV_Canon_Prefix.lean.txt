import R1Z.PV_Canon_Polynomial
import R1Z.PV_Canon_CurrentSemantic
import R1Z.PV_Canon_UpdateRead
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
/-- Exact successful prefix equations at the op121 call in the extracted
host_sumcheck.prove_sumcheck_round. Native installation/reachability is a
separate P obligation; no oracle canonicality hypothesis is needed here. -/
theorem op121_arguments (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    {H : Type} (digest : aspis_core.digest.Digest32 H)
    (s after : host_wire.SemanticTranscript H) (tag : U8) (framed : Slice U8)
    (values coefficients : Array aspis_core.field.QM31 28#usize)
    (point updated : Array aspis_core.field.QM31 10#usize)
    (round : Usize) (sampled read : aspis_core.field.QM31)
    (hr : round.val < 10)
    (hp : @host_sumcheck.interpolate (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) values = .ok coefficients)
    (hs : @host_wire.SemanticTranscript.semantic (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) H digest s tag framed = .ok (.Ok sampled,after))
    (hu : Array.update point round sampled = .ok updated)
    (hi : Array.index_usize updated round = .ok read) :
    Coeffs coefficients ∧ Q read := by
  exact ⟨polynomial base ops values coefficients hp,
    update_read_canonical point updated round sampled read hr
      (current_semantic base ops digest s after tag framed sampled hs) hu hi⟩
#print axioms op121_arguments
end R1Z.PV_Canon
