import RPz7_S1SemanticCodeVerifyExactV1
import PIN2_S1SemanticCodeVerifyExactV1
import RPz7_S1SemanticInstallationV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.S1SemanticCodeInstallation
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open InstalledPreparation

/-! PIN2 W7 (2026-11-11): `code` now runs the PIN2 lifted verifier `S1SemanticCode.verifyPIN2`
(option L2: the release lift with the single public-transcript call replaced by the PIN2 lift on
the copies); `source` (statement unchanged) now equates it with the restated
`S1SemanticInstallation.verify` (the PIN2 VerifyPrefix on the copies) via `verifyPIN2_erasure`. -/

/-- Complete current semantic verifier, with the exact installed root-copy
operation and all full return/error carriers. The source body is reified. -/
def code (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) : Code (core.result.Result (r1_semantic.Verified H) r1_wire.Error) := do
  let result ← AspisR1PublicPreparation.S1SemanticCode.verifyPIN2
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
  rw [erase_bind, AspisR1PublicPreparation.S1SemanticCode.verifyPIN2_erasure,
    AspisR1PublicPreparation.PIN2W7_PrefixGlue.bind_rmap]
  have same : ∀ {H' : Type} (D' : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H') p pre t ch,
      AspisR1PublicPreparation.S1SemanticCode.finishObs
        (AspisR1PublicPreparation.FinishModel.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B))
        D' p pre t ch none =
      AspisR1PublicPreparation.PIN2W7_PrefixGlue.finish
        (AspisR1PublicPreparation.FinishModel.finish R (AspisR1PublicPreparation.S1SemanticRootCopy.install B))
        D' p pre t ch none := by
    intro H' D' p pre t ch
    unfold AspisR1PublicPreparation.S1SemanticCode.finishObs AspisR1PublicPreparation.PIN2W7_PrefixGlue.finish
    apply AspisR1PublicPreparation.PIN2W7_PrefixGlue.bind_congr'
    intro r
    cases r <;> rfl
  unfold AspisR1PublicPreparationPIN2.VerifyPrefix.verify
  simp only [same]
  apply AspisR1PublicPreparation.PIN2W7_PrefixGlue.bind_congr'
  intro result
  cases result <;> rfl

#print axioms source
end AspisR1CurrentCaller.S1SemanticCodeInstallation
