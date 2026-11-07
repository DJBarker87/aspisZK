import NNH_064Reservation
import LIBB_RecordRender
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064ResumeRecord
open Aeneas Aeneas.Std VTop_Stages NJU_CommonObserved
/-- Concrete first native record at the actual runtime reservation binder.
The erased seed reply is not read by the native window. -/
def record (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8) :
 LIBB_RecordRender.Record env :=
 ⟨.resume ck proof pub .div,r,
  .ordinary _ (by intro pr p folded reply same; cases same)⟩

def trace (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8) :
 NNC_DigestTrace.Trace :=
 (NNC_ResumeEvents.queries (NLT_NativeWindows.resumeRun
  (LIBB_PartitionEnv.digest env) ck proof pub () r).events).map NNC_DigestTrace.Step.attempted

theorem from_record (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8) :
 NNC_RecordTrace.FromRecord (record env r pub proof ck) (trace env r pub proof ck) := rfl

theorem bound (sha : List RSL.Bytes → RSL.B32) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (env : RSL.Env) (rep : NNH_HostEnv.EnvRep sha pda clock r env) (pub proof ck : Slice U8) :
 LIBB_RecordReservation.Bound (LIBB_Tx2Reservation.reservation env)
  (record env r pub proof ck).entered (record env r pub proof ck).input :=
 NNH_064Reservation.canonical_tag sha pda clock r env rep

/-- Exact attempted/replied digest events of the SAME resume record. -/
theorem rendered (sha : List RSL.Bytes → RSL.B32) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (env : RSL.Env) (rep : NNH_HostEnv.EnvRep sha pda clock r env) (pub proof ck : Slice U8) :
 NNC_DigestTrace.render (trace env r pub proof ck)=
 LIBB_Tx2EnvTrace.event env (.resume ck proof pub .div) :=
 LIBB_ResumeTrace.native env r (NNH_064Reservation.tag sha pda clock r env rep)
  (LIBB_PartitionEnv.digest env) ck proof pub ()
#print axioms from_record
#print axioms bound
#print axioms rendered
end AspisR1.NNH_064ResumeRecord
