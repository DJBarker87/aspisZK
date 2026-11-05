import NHE_Round
import NHE_DotDeployed
import NHE_PolynomialDomain
set_option autoImplicit false
noncomputable section
namespace NHQ_PacketPorts
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- The actual round packet interface used by the stage, including full errors. -/
def round (bytes : Slice U8) (alpha claim : NE) :=
 FIo_FieldBridge.map NHE_Round.reply (NHE_Round.source bytes alpha claim)

theorem round_packet (r : NP6_StdModel.Reservation) (bytes : Slice U8)
 (alpha claim : NE) (i : Usize) (canonicalAlpha : canonE alpha) (index : i.val<2) :
 round bytes alpha claim =
 AspisR1Stage2.Stage2Finish.verifier.finishRelationRoundWithOps
  (IDa_Deployed.finish r) bytes (FIo_Install.fromE alpha) (FIo_Install.fromE claim) i :=
 NHE_Round.cohort r bytes alpha claim i canonicalAlpha index

/-- Parser failure and run-time nonreturn remain inside the packet. -/
def dot (bytes : Slice U8) (weights : Slice NHE_DotBody.NQ) :=
 FIo_FieldBridge.map NHE_DotDeployed.stageResult (NHE_Dot.source bytes weights)

theorem dot_packet (bytes : Slice U8) (weights : Slice NHE_DotBody.NQ)
 (width : weights.val.length≤64) :
 dot bytes weights = SAG_DotClosed.source bytes
  (SAG_DotAdapter.mapSlice NHE_DotRead.stageQ weights) :=
 NHE_DotDeployed.cohort bytes weights width

/-- Canonical last-round claims are produced, rather than assumed equal to pair. -/
theorem polynomial_canonical (bytes : Slice U8) (alpha claim : NE)
 (canonicalAlpha : canonE alpha) (returned : NHE_Polynomial.source bytes alpha=ok claim) :
 canonE claim := NHE_PolynomialDomain.source bytes alpha claim canonicalAlpha returned

#print axioms round_packet
#print axioms dot_packet
#print axioms polynomial_canonical
end NHQ_PacketPorts
