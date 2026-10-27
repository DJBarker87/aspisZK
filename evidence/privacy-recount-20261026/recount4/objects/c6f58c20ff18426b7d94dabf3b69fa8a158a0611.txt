import R1Z.PhaseSamplerParserBin
import R1Z.PhaseLeafEncodingBin
import R1Z.RomGrammarBin

/-! Composed logical protocol instance. The ROM backend and residual prover
coins/opening data remain parameters; messages, block decoding, query scan,
leaves, grammar and order are constructed. This is not a restatement of
PrivacyR1Final over its arbitrary base, and no source execution identity is
silently inferred. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseProtocolInstanceBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.Batched R1Z.GamesR1
  R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.PhaseLocalityBin R1Z.PremisesR1PBin
local notation "K" => AspisWideTower.WideExact

variable {CommitHandle Aux : Type} {F : Subfield K}

def wire (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) : R1PhaseWire h B outputs x :=
  PhaseMessageEncodingBin.phaseWire PhaseMessageEncodingBin.wideBytes
    (PhaseSamplerParserBin.wireData (RomFiniteBin.wire base (RomGrammarBin.bound publicWidth)))
    PhaseSamplerParserBin.decode_local h B outputs x

/-- The concrete message/sampler model passed as base to the final endpoint. -/
def baseWire (base : R1Wire K CommitHandle Aux) : R1Wire K CommitHandle Aux :=
  PhaseMessageEncodingBin.wireData PhaseMessageEncodingBin.wideBytes
    (PhaseSamplerParserBin.wireData base)

section Instance
variable (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "W" => wire base publicWidth h B outputs x
abbrev prover (seed : R1ProverP K CommitHandle Aux F (W).toWire) :
    R1PhaseProver h B outputs x W :=
  PhaseLeafConstructionBin.prover PhaseLeafEncodingBin.encoding W seed

/-- Causality is unconditional for the composed model, including inconsistent
answer vectors. No execution-order premise is needed for this model fact. -/
theorem causal_premise (seed : R1ProverP K CommitHandle Aux F (W).toWire) : ∀ (w : h.Instance) sec d p v v',
    Earlier (W).toWire (prover base publicWidth h B outputs x seed).toProver p v v' →
      attAddr (W).toWire (prover base publicWidth h B outputs x seed).toProver h B outputs x w sec d v p =
        attAddr (W).toWire (prover base publicWidth h B outputs x seed).toProver h B outputs x w sec d v' p := by
  intro w sec d p v v' he
  exact PhaseCausalityBin.R_causal_D80 (wire base publicWidth h B outputs x)
    (prover base publicWidth h B outputs x seed) w sec d p v v' he

def rows01 : Sem1UniformR1.SemRows01 (W).toWire where
  s1 := PhaseSamplerParserBin.scalar
  sem1 := fun _ _ _ _ => rfl
  sem0 := fun _ _ _ _ _ he => congrArg PhaseSamplerParserBin.scalar (he 0 (by decide))

theorem sampler_source : (rows01 base publicWidth h B outputs x).s1 =
    R1J.SamplerLawSpend.s1Spend (algebraMap R1J.SamplerLawSpend.QF K) := rfl

/-- This model can be used at exactly the endpoint's ROM wrapper by choosing
its base explicitly; the generic final theorem does not make this choice. -/
theorem endpoint_wire : (W).toWire =
    RomFiniteBin.wire (baseWire base) (RomGrammarBin.bound publicWidth) := rfl

#print axioms endpoint_wire
/-- The selected model does not inherit the base wire's message functions. -/
theorem frame_selected : (W).toWire.frame =
    PhaseMessageEncodingBin.frame PhaseMessageEncodingBin.wideBytes := rfl

theorem decoder_selected : (W).toWire.dec = PhaseSamplerParserBin.decode := rfl

#print axioms causal_premise
#print axioms rows01
#print axioms sampler_source
#print axioms frame_selected
#print axioms decoder_selected
end Instance
#print axioms wire
end R1Z.PhaseProtocolInstanceBin
