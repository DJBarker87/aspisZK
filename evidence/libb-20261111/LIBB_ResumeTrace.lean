import LIBB_ResumeReservation
import NNC_DigestTrace
set_option autoImplicit false
noncomputable section
namespace LIBB_ResumeTrace
open Aeneas Aeneas.Std AspisR1

theorem one (e : NJU_ResumeObserved.Event) :
 NNC_DigestTrace.render ((NNC_ResumeEvents.queries [e]).map NNC_DigestTrace.Step.attempted) =
 NNC_ResumeEvents.render [e] := by
 cases e <;> try rfl
 rename_i chunks reply
 cases reply <;> rfl

theorem render (events : List NJU_ResumeObserved.Event) :
 NNC_DigestTrace.render ((NNC_ResumeEvents.queries events).map NNC_DigestTrace.Step.attempted) =
 NNC_ResumeEvents.render events := by
 induction events with
 | nil => rfl
 | cons e rest ih =>
   change NNC_DigestTrace.render ((NNC_ResumeEvents.queries ([e] ++ rest)).map _) =
     NNC_ResumeEvents.render ([e] ++ rest)
   rw [NNC_ResumeEvents.queries_append,List.map_append,NNC_DigestTrace.render_append,
     NNC_ResumeEvents.render_append,one,ih]

/-- SAME entered resume arguments, all Result arms, and the actual Env
reservation tag. The headline error payload is not silently replaced. -/
theorem native {X : Type} (env : RSL.Env) (r : NP6_StdModel.Reservation)
 (bound : NJC_FilledClause.reserved r = env.reservation)
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (ck proof pub : Slice U8) (hash : X) :
 NNC_DigestTrace.render ((NNC_ResumeEvents.queries
  (NLT_NativeWindows.resumeRun d ck proof pub hash r).events).map NNC_DigestTrace.Step.attempted) =
 NNC_ResumeEvents.render (NJU_ResumeObserved.run (LIBB_Tx2Reservation.reservation env)
  (NJC_ResumeCalls.digest d) ck proof pub .S2 hash).events := by
 rw [NNC_ResumeEvents.native_source]
 rw [LIBB_ResumeReservation.run r (LIBB_Tx2Reservation.reservation env)
   (bound.trans (LIBB_Tx2Reservation.reserved env).symm)]
 exact render _
#print axioms one
#print axioms render
#print axioms native
end LIBB_ResumeTrace
end
