import NHW_QueryDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_DeployedStabilize
open Aeneas Aeneas.Std Result Port3_NativeQueryBody
/-- Split the large configuration comparison into only the overwritten fields. -/
theorem fixed (base : Ops)
 (h2 : base.op2=SAQ_Arithmetic.add) (h3 : base.op3=SAQ_MixedSource.mulE)
 (h4 : base.op4=ok 0#u32) (h5 : base.op5=ok 1#u32)
 (h6 : base.op6=AspisR1Qm31ArithmeticProbe.field.M31.sub)
 (h7 : base.op7=AspisR1Qm31ArithmeticProbe.field.M31.mul)
 (h8 : base.op8=S7Kani3BasisOuter.double)
 (h9 : base.op9=SAQ_Arithmetic.mulK) (h16 : base.op16=SAQ_LineQuery.line)
 (h20 : base.op20=FIp_DotsAdapter.dots) (h21 : base.op21=SAQ_Decoder.read) :
 NHW_QueryDictionary.model base=Tx1Q_QueryBridge.leaves base := by
 unfold NHW_QueryDictionary.model SAQ_Decoder.install SAQ_LineQuery.install
   SAQ_QuerySource.install SAQ_Arithmetic.install SAQ_Query.install
 rw [←h2,←h3,←h4,←h5,←h6,←h7,←h8,←h9,←h16,←h20,←h21]

theorem deployed {C : Type} (missing : IDa_Deployed.Uninstalled C) (err : C)
 (r : NP6_StdModel.Reservation) :
 NHW_QueryDictionary.model (NHW_DeployedQuery.configuration missing err r).query=
 Tx1Q_QueryBridge.leaves (NHW_DeployedQuery.configuration missing err r).query := by
 apply fixed
 all_goals rfl
#print axioms fixed
#print axioms deployed
end AspisR1.NHW_DeployedStabilize
