import NJG_ObservedInstall
import NJG_ConfiguredFinish
import NJG_PublicBack
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJG_CurrentEquation
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge OriginalPreparedSource S1SemanticCarrier
open NJG_InputCarriers NJG_Carriers NJG_Results

def verify (R : RoundModel.Boundaries) (F : FinishModel.Boundaries)
 {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
 (pubdata : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) :
 Result (core.result.Result (AspisR1CurrentCaller.r1_semantic.Verified H) AspisR1CurrentCaller.r1_wire.Error) := do
 let result←upResult (NIX_ObservedBody.emitted
  (NJG_ObservedInstall.install R (S1SemanticRootCopy.install F))
  (downDigest (retainedDigest D)) (downPublic (FirstComposition.toRetainedPublic pubdata)) bytes hash none)
 ok (match result with | .Ok value=>.Ok (currentSem value) | .Err error=>.Err (currentWireError error))

theorem claims_model (seed : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
 NJG_FinishInstall.model (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std (FIp_Install.boundaries seed)))=
 S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std (FIp_Install.boundaries seed)) := by
 unfold NJG_FinishInstall.model S1SemanticRootCopy.install ClaimsUnrolledFinish.install FIp_Install.boundaries
 rw [NJG_ConfiguredFinish.unwrap]

/-- The complete current op9 carrier, not acceptance equivalence or a selected
projection. Every value is copied from the SAME emitted root result. Protocol
leaf functions and native interpretation remain explicit unresolved obligations. -/
theorem source (R : RoundModel.Boundaries) (seed : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
 {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
 (pubdata : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) :
 verify R (ClaimsUnrolledFinish.install std (FIp_Install.boundaries seed)) D pubdata bytes hash=
 S1SemanticInstallation.verify R (ClaimsUnrolledFinish.install std (FIp_Install.boundaries seed)) D pubdata bytes hash := by
 unfold verify S1SemanticInstallation.verify
 rw [NJG_ObservedInstall.source,NJG_CarrierBack.digest,NJG_PublicBack.full,claims_model]
 rfl

/-- Explicit source-model packet interpretation only. This definition is NEVER
asserted equal to the frozen native op9 merely because its equation compiles. -/
def ops (base : Ops) (seed : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) : Ops :=
 {base with op9:=fun {H} D pubdata bytes hash obs=>match obs with
   | none=>verify AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std (FIp_Install.boundaries seed)) D pubdata bytes hash
   | some observe=>base.op9 D pubdata bytes hash (some observe)}

theorem slot (base : Ops) (seed : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
 {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
 (pubdata : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) :
 (ops base seed std).op9 D pubdata bytes hash none=
 (RowShape_InstalledSlots.verifierOps (ops base seed std) (FIp_Install.boundaries seed) std).op9 D pubdata bytes hash none := by
 change verify AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std (FIp_Install.boundaries seed)) D pubdata bytes hash=_
 rw [source]
 rfl

#print axioms claims_model
#print axioms source
#print axioms slot
end AspisR1.NJG_CurrentEquation
end
