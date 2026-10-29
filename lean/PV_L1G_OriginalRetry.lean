import PV_L1G_WorldReached
import PV_L1E_OriginalCountSkeleton
set_option autoImplicit false
namespace PV_L1G_OriginalRetry
open PV_L1G_WorldRetry
open R1Z.SideChannelL1AttemptRecord (Owner Run events)
/-- A sufficient reached-leaf and client-adapter criterion for the FROZEN
OriginalRetry link. This is conditional; no deployed leaf is installed here. -/
theorem original_retry {I A W S P : Type}
 (a : I → Attempt W S P) (owner : I → Owner (W × S) P)
 (initial : I → W × S) (fuel index : I → Nat)
 (body : I → PV_RJ4IDB.Trace A)
 (decode : I → PV_L1D_Logged.Logged
   (R1Z.ProverCommitRetry34.Step (R1Z.ProverCommitRetry34.Published P) × (W × S)) → PV_RJ4IDB.Trace A)
 (adapt : I → Run P × (W × S) → PV_RJ4IDB.Trace A)
 (leaf : ∀ i, PV_L1F_ReachedJoin.ReachedOwner (stateAttempt (a i)) (owner i) (index i) (initial i))
 (bodyLaw : ∀ i, body i = decode i (stateLog
   (PV_L1G_WorldRetry.run (a i) (fuel i) (index i) (initial i).2 (initial i).1)))
 (client : ∀ i r, decode i ⟨events r.1,.ok (r.1.result,r.2)⟩ = adapt i r) :
 PV_L1E_OriginalCountSkeleton.PV_L1E_Link_OriginalRetry body owner initial fuel index adapt := by
 intro i
 rw [bodyLaw i]
 have join := original_logged (a i) (owner i) (index i) (initial i) (leaf i)
   (fuel i) (index i) (initial i).2 (initial i).1 .initial
 rw [join,client i]
#print axioms original_retry
end PV_L1G_OriginalRetry
