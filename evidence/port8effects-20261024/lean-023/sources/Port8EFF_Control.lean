import VTop_OracleCode
import VTop_Flow
import Port8EFF_PowersTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port8EFF_Control
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
def afterSplit {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (hash : Hash) (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator) (i : Usize) :
    Code (core.result.Result Unit verifier.Error) :=
  if a.next != i then .done (.Err .Checkpoint)
  else .call (.op17 29#usize p.gamma) (afterPowers D proof hash obs p a i)


def commonTail {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (_pub proof : Slice U8) (hash : Hash)
    (obs : Option (verifier.Phase → Result Unit))
    (r : core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) :
    Code (core.result.Result Unit verifier.Error) := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue pair =>
    let (p,a) := pair
    let i ← VTop_Flow.traceEffects.op16
    afterSplit D proof hash obs p a i
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual

theorem common_ok (impl : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub proof : Slice U8) (hash : Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (H : Bytes → State) :
    eval H (interpret impl (commonTail D pub proof hash none (.Ok (p,a))))=
      eval H (interpret impl (.call .op16 (afterSplit D proof hash none p a))) := rfl

#print axioms common_ok

theorem common_source {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub proof ck : Slice U8) (hash : Hash) :
    VTop_Flow.tx2_common VTop_Flow.traceEffects D pub proof ck hash none=
      .call (.op18 D ck proof pub .S2 hash) (commonTail D pub proof hash none) := rfl

theorem rejected (impl : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub proof : Slice U8) (hash : Hash) (e : verifier.Error) (H : Bytes → State) :
    eval H (interpret impl (commonTail D pub proof hash none (.Err e)))=([],ok (.Err e)) := rfl

#print axioms common_source
#print axioms rejected
end AspisR1.Port8EFF_Control
end
