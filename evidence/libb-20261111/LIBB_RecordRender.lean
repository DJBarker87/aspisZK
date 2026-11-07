import LIBB_EnvCommon
import LIBB_C04DetailGraph
import NNC_RecordTrace
set_option autoImplicit false
noncomputable section
namespace LIBB_RecordRender
open Aeneas Aeneas.Std AspisR1 VTop_Stages
open NLT_NativeInvocation
abbrev Record (env : RSL.Env) := Occurrence (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
/-- Each source record has either the complete resume observation or the
closed C04 detail law, including its independent pending-prefix branch. -/
def Law (env : RSL.Env) (record : Record env) (trace : NNC_DigestTrace.Trace) : Prop :=
 match record with
 | ⟨.resume ck proof pub _,_,_⟩ =>
   NNC_DigestTrace.render trace=LIBB_Tx2EnvTrace.event env (.resume ck proof pub .div)
 | ⟨_,_,detail⟩ => LIBB_C04DetailGraph.RenderLaw (LIBB_PartitionEnv.H env) detail trace

theorem one (env : RSL.Env) (record : Record env) (trace : NNC_DigestTrace.Trace)
 (source : NNC_RecordTrace.FromRecord record trace)
 (bound : LIBB_RecordReservation.Bound (LIBB_Tx2Reservation.reservation env) record.entered record.input)
 (law : NLT_C04Installed.Law (LIBB_PartitionEnv.H env) record.detail) : Law env record trace := by
 rcases record with ⟨e,input,detail⟩
 cases e <;> first
 | exact LIBB_C04DetailGraph.transport detail law trace source
 | (change trace=_ at source
    subst trace
    exact LIBB_ResumeTrace.native env input
     (bound.trans (LIBB_Tx2Reservation.reserved env)) (LIBB_PartitionEnv.digest env) _ _ _ ())

/-- Exact chronological frame decomposition. No independent execution or
log is chosen: the pieces come from this SAME Records derivation. -/
theorem records (env : RSL.Env) (rs : List (Record env)) (trace : NNC_DigestTrace.Trace)
 (source : NNC_RecordTrace.Records rs trace) (bound : LIBB_EnvCommon.Bound env rs)
 (laws : ∀ record∈rs,NLT_C04Installed.Law (LIBB_PartitionEnv.H env) record.detail) :
 ∃ pieces : List NNC_DigestTrace.Trace, trace=pieces.flatten ∧ List.Forall₂ (Law env) rs pieces := by
 induction source with
 | nil => exact ⟨[],rfl,.nil⟩
 | cons record rest head tail headSource next ih =>
   obtain ⟨pieces,rfl,rel⟩:=ih
    (fun r h=>bound r (List.mem_cons_of_mem _ h))
    (fun r h=>laws r (List.mem_cons_of_mem _ h))
   exact ⟨head::pieces,rfl,.cons (one env record head headSource
    (bound record List.mem_cons_self) (laws record List.mem_cons_self)) rel⟩
#print axioms one
#print axioms records
end LIBB_RecordRender
end
