import NNG_PrepareErrors087
import NMP_ResultTransport
import LIBC_WideView
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_WideView087
open Aeneas Aeneas.Std Result NMP_prepare
open NNG_PrepareCarriers087 NNG_PrepareErrors087
open NMP_ResultTransport (inner outer)

def call (proof semantic y1 : Slice U8) : Result (core.result.Result verifier.View verifier.Error) :=
 outer (inner (fun v=>viewBack (AspisR1SelectedWideViewV1.preparedView v))
   (fun e=>errorBack (LIBC_WideView.error e)))
  (AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1)
def port (r : core.result.Result verifier.View verifier.Error) : Except LIB_VCarriers.VErr LIB_VCarriers.View :=
 match r with | .Ok v=>.ok (view v) | .Err e=>.error (error e)

theorem projection (r : Result (core.result.Result AspisR1SelectedWideViewV1.verifier.View AspisR1SelectedWideViewV1.verifier.Error)) :
 NNG_EmittedCallGraph.resultMap port
   (outer (inner (fun v=>viewBack (AspisR1SelectedWideViewV1.preparedView v)) (fun e=>errorBack (LIBC_WideView.error e))) r) =
 NNG_EmittedCallGraph.resultMap LIBC_WideView.port r := by
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok r=>cases r <;> simp only [outer,NMP_ResultTransport.inner,NNG_EmittedCallGraph.resultMap,port,LIBC_WideView.port,viewBack_inverse,errorBack_inverse]

theorem projected (proof semantic y1 : Slice U8) (env : RSL.Env)
 (domain : LIBC_WideView.Domain (LIB_Carriers.bytes proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1)) :
 NNG_EmittedCallGraph.resultMap port (call proof semantic y1) =
 .ok (LIBC_WideView.value (LIB_Carriers.bytes proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1) env) := by
 rw [call,projection]
 have law := LIBC_WideView.model_port (LIB_Carriers.bytes proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1) env domain
 rw [LIBC_Bytes.from_native,LIBC_Bytes.from_native,LIBC_Bytes.from_native] at law
 exact law
#print axioms projection
#print axioms projected
end AspisR1.NNG_WideView087
