import LIB_Env
import LIB_VCarriers
import RPz7_S1ClosedPreparationHashCodeV1
import LIBC_PreparedErrors
set_option autoImplicit false
noncomputable section
namespace LIBC_PreparedLog
open Aeneas Aeneas.Std Result AspisR1 AspisR1PublicPreparation
open NFW_PreparedControl NHL_PreparedScalars
/-- SAME fixed cohort installation used by the CLOSED179 packet. -/
theorem installation : AspisR1CurrentCaller.BorrowedClaimPrepared.closedHashBoundaries = actual := rfl
def code (D : aspis_core.Digest32 Unit) (sem : r1_semantic.Verified Unit)
 (v : verifier.View) (_ : Unit) (old : Scratch) :=
 PreparedSourceEffects.prepare
  (PreparedHashCode.preparationEffects actual AspisR1CurrentCaller.BorrowedClaimPrepared.closedHashQueries)
  D sem v () old
theorem dictionary : PreparedHashCode.withQueries actual
 AspisR1CurrentCaller.BorrowedClaimPrepared.closedHashQueries = actual := by
 rw [← installation]
 exact AspisR1CurrentCaller.BorrowedClaimPrepared.closedHashBoundaries_queries
/-- Ordered effects and full Result share one typed source computation.
There is no free child dictionary and no supplied successful call. -/
theorem full_result (D : aspis_core.Digest32 Unit) (sem : r1_semantic.Verified Unit)
 (v : verifier.View) (old : Scratch) :
 (PreparedHashCode.run (code D sem v () old)).2 =
 NGN_Emitted.prepared actual D sem v () old := by
 rw [PreparedHashCode.run_value,code,PreparedHashCode.preparation_erasure,dictionary,OriginalPreparedNative.eq_prepare]
 exact (LIBC_PreparedErrors.complete D sem v old).symm
/-- Failed attempts have no invented returned digest. Env.sha256 is total at
this library instance; a stop retains only the preceding successful prefix. -/
def event : PreparedHashCode.Event → List RSL.Event
 | .digest _ _ parts (.ok reply) => [.digest (NNC_ResumeEvents.parts parts) (LIB_Carriers.b32 reply)]
 | .digest _ _ _ (.fail _) => []
 | .digest _ _ _ .div => []
def events (log : PreparedHashCode.Log) : List RSL.Event := log.flatMap event
theorem digest_event {H : Type} (D : aspis_core.Digest32 H) (h : H)
 (parts : Slice (Slice U8)) (reply : Array U8 32#usize) :
 event (.digest D h parts (.ok reply)) =
 [.digest (NNC_ResumeEvents.parts parts) (LIB_Carriers.b32 reply)] := rfl
theorem events_append (a b : PreparedHashCode.Log) :
 events (a++b) = events a ++ events b := List.flatMap_append
/-- Full source value with the same fixed environment backend. No SHA value
is proved here: it remains the headline-bound runtime realization. -/
def digest (env : RSL.Env) : aspis_core.Digest32 Unit :=
 NGQ_Effects.dictionary (LIB_Env.hashv env)
theorem source_at_env (env : RSL.Env) (sem : r1_semantic.Verified Unit)
 (v : verifier.View) (old : Scratch) :
 (PreparedHashCode.run (code (digest env) sem v () old)).2 =
 NGN_Emitted.prepared actual (digest env) sem v () old := full_result _ sem v old
#print axioms installation
#print axioms dictionary
#print axioms full_result
#print axioms digest_event
#print axioms events_append
#print axioms source_at_env
end LIBC_PreparedLog
