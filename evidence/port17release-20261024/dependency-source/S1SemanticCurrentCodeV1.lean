import S1SemanticCodeVerifyExactV1
import S1SemanticInstallationV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.S1SemanticCodeInstallation
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open InstalledPreparation

/-- Complete current semantic verifier, with the exact installed root-copy
operation and all full return/error carriers. The source body is reified. -/
def code (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) : Code (core.result.Result (r1_semantic.Verified H) r1_wire.Error) := do
  let result ← AspisR1PublicPreparation.S1SemanticCode.verify
    (AspisR1PublicPreparation.S1SemanticCode.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B))
    (retainedDigest D) (FirstComposition.toRetainedPublic pub) bytes hash none
  pure (match result with
    | .Ok sem => .Ok (S1SemanticCarrier.currentSem sem)
    | .Err error => .Err (S1SemanticCarrier.currentWireError error))

theorem source (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) :
    erase (code R B D pub bytes hash)=S1SemanticInstallation.verify R B D pub bytes hash := by
  unfold code S1SemanticInstallation.verify
  rw [erase_bind,AspisR1PublicPreparation.S1SemanticCode.verify_erasure]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro result _
  cases result <;> rfl

#print axioms source
end AspisR1CurrentCaller.S1SemanticCodeInstallation
