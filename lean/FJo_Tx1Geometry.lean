import FJo_Tx1AtPowers
import FIp_Install
import F3Y_InstalledLaws
import Port5Q1_GeometryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_Tx1Geometry
open Aeneas Aeneas.Std Result
open DrvC_Installation F3V_RunEvidence Tx1Q_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The SAME TX1 geometry is bound to its actual query array by installed source laws. -/
theorem value {C : Type} (err : C) (seed : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : F3T_ByteCarrier.Submission)
    (H : Bytes → State) (e : Evidence (FIp_Install.configuration err seed r) B s H) :
    Port5Q1_GeometryBinding.Binding (prepared e.run.p).queries 0#usize 10#usize (geometry e.run.geometry) := by
  let base := FIo_Install.select r seed
  let c := FIp_Install.configuration err seed r
  exact Port5Q1_GeometryReads.accepted c.geometry
    (F3Y_InstalledLaws.canonical err base r) (F3Y_InstalledLaws.domain err base r)
    (F3Y_InstalledLaws.multiply err base r) (F3Y_InstalledLaws.one err base r)
    (F3Y_InstalledLaws.inverse err base r) e.run.p.queries 0#usize 10#usize
    (geometry e.run.geometry) (by decide) e.run.geometry_call
#print axioms value
end AspisR1.FJo_Tx1Geometry
end
