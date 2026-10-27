import R1Z.PV_Canon_Sampler
import R1Z.PV_Canon_Result
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- A sampler-only interface. This is instantiated by sampler_total, not T. -/
def SamplerLaw (dict : ExternalFuns) : Prop :=
  ∀ bytes, Safe Q (dict.op248 bytes)
def SemanticValue {H : Type}
    (r : (core.result.Result aspis_core.field.QM31 r1_wire.Error) × host_wire.SemanticTranscript H) : Prop :=
  ∀ q, r.1 = .Ok q → Q q
 theorem semantic_safe (dict : ExternalFuns) (law : SamplerLaw dict)
    {H : Type} (digest : aspis_core.digest.Digest32 H)
    (s : host_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    Safe SemanticValue (@host_wire.SemanticTranscript.semantic _ dict H digest s row framed) := by
  unfold host_wire.SemanticTranscript.semantic
  split
  · apply safe_ok
    intro q h; cases h
  · apply safe_bind_any; rintro ⟨r,s1⟩
    cases r with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      apply safe_ok
      intro q h; cases h
    | Ok bytes =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply safe_bind Q SemanticValue _ _ (law bytes)
      intro q hq
      apply safe_ok
      intro z hz; cases hz; exact hq
#print axioms semantic_safe
end R1Z.PV_Canon
