import NNG_LegacySuffix136
import NNG_ConcreteCalls136
import NNG_LIBClaims
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LegacyConfig136
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Concrete deterministic model boundaries, used only as the explicit witness
for CLOSED179's semantic provenance. This is not a VLib field instance. -/
def boundaries (env : RSL.Env) : FinishModel.Boundaries where
 fromFn := OraclePortStdBuilder.fromFn
 mask := FIp_SemanticArithmetic.mask
 add := FIp_SemanticArithmetic.add
 mul := FIp_SemanticArithmetic.mul
 terminal := FIq_Terminal.terminal
 circle := F3M_CircleSource.source
 unwrapRoot := core.result.Result.unwrap core.fmt.DebugTryFromSliceError
 claims := ClaimsUnrolledFinish.claims (NP6_StdModel.calls (NNG_LIBClaims.reservation env))

def parent {H W : Type} (s : NNG_Emitted.Parent H W) : NNG_LegacySuffix136.Parent H W :=
 ⟨NNG_Install.digest s.digest,NNG_Transport.toT9 s.publicValue,NNG_Transport.toT12 s.prefixValue,
  NNG_Transport.toT10 s.transcript,NNG_Transport.toT3 s.challenges,none⟩

theorem rounds : NJM_RoundJoin.R=AspisS1ExtractedRoundChildren.children := rfl
#print axioms rounds
end AspisR1.NNG_LegacyConfig136
