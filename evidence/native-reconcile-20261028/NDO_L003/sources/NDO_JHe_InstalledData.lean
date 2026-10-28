import RPu_FIq_Install
import RPz7_S1SemanticRootCopyV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_InstalledData
open Aeneas Aeneas.Std Result
/-- Definition-only fission of the adopted IDa installation; equality to IDa
is checked separately without importing the security headline into the fixture. -/
structure Uninstalled (CoreError : Type) where
  adapter : AdapterRw.Ops
  currentBase : AspisR1CurrentCaller.Ops
  stageBase : VTop_Stages.Ops
  reserved : Bool
  query : Port3_NativeQueryBody.Ops
  geometry : Port3_NativeGeometryBody.Ops CoreError

/-- Complete finish interpretation: FIo/FIn value bodies and Port3 release leaves.
No success, acceptance or semantic law is stored in this record. -/
def finish (reservation : NP6_StdModel.Reservation) :
    AspisR1Stage2.Stage2Finish.FinishOps FIo_Install.W where
  field := FIn_Primitives.field
  quarter := ok 536870912#u32
  add := FIn_Primitives.add
  mulM := SAG_StageScale.mulM
  ne := Port3_FinishStage.ne
  polynomial := FIn_ExtractInstall.polynomial
  trace := fun _ _ _ => ok ()
  folds := Port3_FinishStage.folds
  newWeights := FIn_WeightsInstall.newWeights
  pair := FIo_Install.pair reservation
  mark := Port3_QueryStage.mark
  dot := SAG_DotClosed.source

/-- Source interpretations of every semantic finish boundary. Root-copy has
its existing accepted-value/panic interpretation; std effects remain a P6 gate. -/
def boundaries (reservation : NP6_StdModel.Reservation) :
    AspisR1PublicPreparation.FinishModel.Boundaries where
  fromFn := OraclePortStdBuilder.fromFn
  mask := FIp_SemanticArithmetic.mask
  add := FIp_SemanticArithmetic.add
  mul := FIp_SemanticArithmetic.mul
  terminal := FIq_Terminal.terminal
  circle := F3M_CircleSource.source
  unwrapRoot := AspisR1PublicPreparation.S1SemanticRootCopy.unwrapRoot
  claims := ClaimsUnrolledFinish.claims (NP6_StdModel.calls reservation)

def seed {CoreError : Type} (missing : Uninstalled CoreError)
    (reservation : NP6_StdModel.Reservation) :
    DrvC_Installation.Configuration FIo_Install.W CoreError where
  adapter := missing.adapter
  currentBase := missing.currentBase
  stageBase := missing.stageBase
  finish := finish reservation
  reserved := missing.reserved
  query := missing.query
  geometry := missing.geometry
  boundaries := boundaries reservation
  std := NP6_StdModel.calls reservation

/-- Explicit partial source installation, not a source-to-ELF certificate.
All unresolved outer components are exposed in `missing`. -/
def deployedConfiguration {CoreError : Type} (missing : Uninstalled CoreError)
    (indexError : CoreError) (reservation : NP6_StdModel.Reservation) :
    DrvC_Installation.Configuration FIo_Install.W CoreError :=
  FIq_Install.configuration indexError (seed missing reservation) reservation


end AspisR1.JHe_InstalledData
end
