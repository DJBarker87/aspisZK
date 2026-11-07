import NNH_QueryCapture
import LIBB_EnvCommon
import NKO_C07Domain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064SourceInputs
open Aeneas Aeneas.Std VTop_Stages NJU_CommonObserved

def input (env : RSL.Env) (pub proof ck : Slice U8) (e : Event)
 (entered : e∈(LIBB_Tx2EnvCode.observed env pub proof ck).events) :
 NLT_NativeWindows.Input e := by
 cases e with
 | resume .. => exact LIBB_Tx2Reservation.reservation env
 | pending .. => exact LIBB_Tx2Reservation.reservation env
 | finish .. => exact (LIBB_Tx2Reservation.reservation env,NLT_FrameFromCuts.unusedLocations)
 | query pr p a g geo pending reply =>
   have widths := NKO_C07.at_actual
    (LIBB_Tx2Reservation.reservation env) (LIBB_Tx2Reservation.reservation env)
    (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
    (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env))
    (LIBB_PartitionEnv.digest env) pub proof ck () pr p a g geo pending reply entered
   exact NNH_QueryCapture.input ⟨pr,p,a,g,geo,pending⟩
    ⟨widths.2.2.2.2.2.1,widths.2.2.2.2.2.2.2.1,
     widths.2.2.2.2.2.2.2.2.1,widths.2.2.2.2.2.2.1⟩
 | powers .. => exact PUnit.unit
 | inactive .. => exact PUnit.unit
 | merkle .. => exact PUnit.unit
 | geometry .. => exact PUnit.unit
 | flush .. => exact PUnit.unit

theorem bound (env : RSL.Env) (pub proof ck : Slice U8) (e : Event)
 (entered : e∈(LIBB_Tx2EnvCode.observed env pub proof ck).events) :
 LIBB_RecordReservation.Bound (LIBB_Tx2Reservation.reservation env) e
  (input env pub proof ck e entered) := by
 cases e <;> first | rfl | exact True.intro

theorem actual (env : RSL.Env) (pub proof ck : Slice U8) (len : proof.val.length=57607)
 (e : Event) (entered : e∈(LIBB_Tx2EnvCode.observed env pub proof ck).events) :
 NLT_NativeWindows.window (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () e
  (input env pub proof ck e entered)=e :=
 LIBB_RecordReservation.step (LIBB_Tx2Reservation.reservation env)
  (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) pub proof ck () len
  e entered e (input env pub proof ck e entered) rfl (bound env pub proof ck e entered)
#print axioms input
#print axioms bound
#print axioms actual
end AspisR1.NNH_064SourceInputs
