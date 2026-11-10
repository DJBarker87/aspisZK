-- PCVN_ composition: the deployed VTop Ops (PRVEq_Tx2Deployed_n0 / m1 shape) at the closure's concrete slot values
-- inact := NJC_ClosedCalls.inactive, mk := NHV_ReleaseOps.mark, with the proved frozen relations for op2, op13, op17 and the receipted op3 wrapper.
-- This file does NOT discharge h18 (op18) and does not relate op5/6/9/10/11/19 to frozen emissions.
import Aeneas
import PRVEq_Tx2Deployed_n0
import PRVEq_Op2_p5
import PRVEq_Op13_p1
import PRVEq_Op17_p2
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVN_Tx2Deployed_n1
open AspisR1 PCVN_Tx2Deployed

section
variable {F CE : Type} (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
  (geo : Port3_NativeGeometryBody.Ops CE) (base : VTop_Stages.Ops)
  (finish : AspisR1Stage2.Stage2Finish.FinishOps F)

/-- op2 of the deployed dictionary = the fresh 4bb3b3f WideExact.from_le_bytes behind the structural port. -/
theorem op2_deployed_frozen (bytes : Slice Std.U8) :
    (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish).op2 bytes = (do
      let o ← AspisR1CandidateParser.PRVFresh_R1CandidateWideParserSource_j1.field.wide_exact.WideExact.from_le_bytes bytes
      ok (Option.map PCVN_Op2.port o)) := by
  rw [slot_op2]; exact PCVN_Op2.op2_frozen bytes

theorem op13_deployed_frozen (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) (p : VTop_Stages.verifier.Phase) :
    (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish).op13 obs p =
      AspisR1CurrentCaller.PCVN_FreshMark.verifier.mark (Option.map (fun f q => f (PCVN_Op13.fromC q)) obs) (PCVN_Op13.toC p) := by
  rw [slot_op13]; exact PCVN_Op13.op13_frozen obs p

theorem op17_deployed_frozen (N : Std.Usize) (x : AspisR1.Tx2N_Powers.E) :
    (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish).op17 N x = (do
      let out ← AspisR1LoopPowers.PCVN_FreshPowers.powers N (AspisR1.Tx2N_Powers.toPowers x)
      ok (AspisR1.Tx2N_Powers.mapArray out)) := by
  rw [slot_op17]; exact AspisR1LoopPowers.PCVN_Op17.op17_frozen N x

/-- op3: the deployed shape slot is the receipted Op3I_Source parse_shape at the std instance Op3I_Std.ops behind nominal ports. -/
theorem op3_deployed_shape (proof : Slice Std.U8) :
    (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish).op3 proof =
      Tx2I_Install.shape proof := by
  rw [slot_op3]
end

#print axioms op2_deployed_frozen
#print axioms op13_deployed_frozen
#print axioms op17_deployed_frozen
#print axioms op3_deployed_shape
end PCVN_Tx2Deployed_n1
