import S1CurrentPrepareCodeExactV1
import S1TopPrepareSourceV1
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPrepareCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1ClaimPreparedBridge AspisS1TopPrepareCarrier AspisS1TopPrepareSource
open AspisS1ValuesOwnedInstallation

def sourceOps (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : AspisR1CurrentCaller.Ops :=
  AspisR1CurrentCaller.S1SemanticInstallation.install
    {(withValues base) with op10:=AspisS1NativeCompact.compact.expand_semantic nativeValues} R B

/-- Complete op7 effect tree at the lead's physical stage ABI. No field of
Prepared, gamma scratch, public/proof/hash argument or error is projected away. -/
def code (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (input : Array Top.E 29#usize) :
    Code (core.result.Result Top.Prepared VTop_Stages.verifier.Error × Array Top.E 29#usize) := do
  let (result,scratch) ← AspisR1CurrentCaller.S1PrepareCode.prepare base R B (currentDigest D)
    (AspisS6CurrentVerifierCarrier.toPublic pub) proof hash (mapArray fromE input)
  pure ((match result with
    | .Ok prepared => .Ok (toPrepared prepared)
    | .Err error => .Err (AspisS6CurrentVerifierCarrier.fromError error)),mapArray toE scratch)

/-- ALL outcomes at the exact installed top op7, including both source
hash-bearing phases and rejection prefixes in the same Code tree. -/
theorem source (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (input : Array Top.E 29#usize) :
    erase (code base R B D pub proof hash input)=
      AspisS1TopPrepareSource.prepare (sourceOps base R B) D pub proof hash none input := by
  unfold code AspisS1TopPrepareSource.prepare
  rw [erase_bind,AspisR1CurrentCaller.S1PrepareCode.source]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro result _
  rcases result with ⟨result,scratch⟩
  cases result <;> rfl

#print axioms source
end AspisS1TopPrepareCode
