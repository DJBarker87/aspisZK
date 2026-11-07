import NNG_PrepareErrors087
import NMP_Install131
import NMP_ResultTransport
import LIBC_PreparedLog
import LIBC_PreparedLaw
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PreparedCall087
open Aeneas Aeneas.Std Result NMP_prepare
open NNG_PrepareCarriers087 NNG_PrepareErrors087
open NMT_Transport (arr arr_inverse)

/-- Source effects and the complete scratch reply share the SAME CLOSED179
computation. No query, constructor or allocator success is assumed. -/
def code {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (h : H) (g : NMP_Emitted.Scratch) :=
 AspisR1PublicPreparation.PreparedSourceEffects.prepare
  (AspisR1PublicPreparation.PreparedHashCode.preparationEffects NHL_PreparedScalars.actual
   AspisR1CurrentCaller.BorrowedClaimPrepared.closedHashQueries)
  (NMP_Install131.digest D) (NMP_Transport.toT11 sem) (view v) h (arr wide g)

def replyBack (r : NFW_PreparedControl.Out) : NMP_Emitted.PreparedOut :=
 ((match r.1 with | .Ok p=>.Ok (preparedBack p)
   | .Err e=>.Err (errorBack (LIBC_PreparedLaw.error e))),arr wideBack r.2)
def port (r : NMP_Emitted.PreparedOut) : LIBC_PreparedLaw.Output :=
 ((match r.1 with | .Ok p=>.ok (prepared p) | .Err e=>.error (error e)),arr wide r.2)
def call {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (h : H) (g : NMP_Emitted.Scratch) : Result NMP_Emitted.PreparedOut :=
 NMP_ResultTransport.outer replyBack (AspisR1PublicPreparation.PreparedHashCode.run (code D sem v h g)).2

theorem reply_inverse (r : NFW_PreparedControl.Out) : port (replyBack r)=LIBC_PreparedLaw.port r := by
 rcases r with ⟨r,g⟩
 cases r with
 | Ok p=>
   simp only [port,replyBack,LIBC_PreparedLaw.port,preparedBack_inverse]
   rw [arr_inverse wideBack wide wideBack_inverse]
 | Err e=>
   simp only [port,replyBack,LIBC_PreparedLaw.port,errorBack_inverse]
   rw [arr_inverse wideBack wide wideBack_inverse]

theorem projection (r : Result NFW_PreparedControl.Out) :
 NNG_EmittedCallGraph.resultMap port (NMP_ResultTransport.outer replyBack r) =
 NNG_EmittedCallGraph.resultMap LIBC_PreparedLaw.port r := by
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok r=>exact congrArg Result.ok (reply_inverse r)

/-- At the actual Unit instantiation, this is exactly LIBC's receipted CLOSED
model code at the raw semantic, View and incoming scratch arguments. -/
theorem source (D : aspis_core.digest.Digest32 Unit) (sem : r1_semantic.Verified Unit)
 (v : verifier.View) (g : NMP_Emitted.Scratch) :
 (AspisR1PublicPreparation.PreparedHashCode.run (code D sem v () g)).2 =
 NGN_Emitted.prepared NHL_PreparedScalars.actual (NMP_Install131.digest D)
   (NMP_Transport.toT11 sem) (view v) () (arr wide g) :=
 LIBC_PreparedLog.full_result _ _ _ _
#print axioms reply_inverse
#print axioms projection
#print axioms source
end AspisR1.NNG_PreparedCall087
