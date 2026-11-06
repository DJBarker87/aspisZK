import NIW_AlignComposedRoot
import NIW_AlignRegularPostBoundary
import NIW_AlignFinishPort
import NIW_AlignRegularNativeView
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignNativeObligations
open Aeneas Aeneas.Std Result NIT_Cuts NIT_PairControl

/-- DATA ONLY. The native parent interpretation must produce this actual
complete observed regular Result. No result equation is a carrier field. -/
structure RegularObservation where
 outcome : Result NHM_RegularKinds.Reply

/-- Exact still-unproved native projection conclusion. This is deliberately
NOT a hypothesis of any accepted positive native root. -/
def RegularProjection [FIo_Native.Allocation] (c : Context) (before : Scratch)
 (native : RegularObservation) : Prop :=
 native.outcome=(NIW_AlignRegularPhase.run c before).2.outcome

/-- Complete allocator witness at the actual native parent Result, including
all error/abort arms. This is an obligation, not an asserted theorem. -/
def PairWitness (r : NP6_StdModel.Reservation) (c : Context) (native : Result NR) : Prop :=
 NIT_AllocatorChain.Trace c r native

/-- The SAME native child-event projections must be associated by the parent
body and cuts. Equality here is a target conclusion, never a root premise or
an additional physical exporter requirement. -/
def FinishProjection (r : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 (v : AspisR1Stage2.verifier.View) (p : AspisR1Stage2.verifier.Prepared)
 (a : AspisR1Stage2.verifier.Accumulator) (nativeEvents : List NIW_AlignFinishExecution.Event) : Prop :=
 nativeEvents=(NIW_AlignFinishComposed.run r loc v p a).2.1

#print RegularObservation
#print RegularProjection
#print PairWitness
#print FinishProjection
#check NIW_AlignComposedRoot.source
#check NIW_AlignPairInstalled.source
#check NIW_AlignFinishPort.source
#print NIW_AlignFinishPort.Cut
#print NIW_AlignFinishPort.Bound
#print NIW_AlignPairPhase.Certificate
#print NIG_FinishInput.Domain
#print NIW_AlignNativeObligations.RegularObservation
#print NIW_AlignNativeObligations.RegularProjection
#print NIW_AlignNativeObligations.PairWitness
#print NIW_AlignNativeObligations.FinishProjection
#print NIW_AlignRegularNativeView.project
end AspisR1.NIW_AlignNativeObligations
