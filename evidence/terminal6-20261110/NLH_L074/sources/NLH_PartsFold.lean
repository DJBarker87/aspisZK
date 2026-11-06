import NLH_PartsStep0
import NLH_PartsStep1
import NLH_PartsStep2
import NLH_PartsStep3
import NLH_PartsStep4
import NLH_PartsStep5
import NLH_PartsStep6
import NLH_PartsStep7
import NLH_PartsStep8
import NLH_RustCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_PartsFold
open Aeneas Aeneas.Std Result FIq_Native NLH_PartsValues
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
open NKR_TermTail (Calls Carrier)
theorem call (zc point : Array NQ 10#usize) (mu : NQ) (child : Carrier)
 (p : Calls zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2) (i : Fin 9) :
 NLH_PartsState.arithmetic zc point mu (stage child p i.val) i=ok (values p i) := by
 fin_cases i
 · exact NLH_PartsStep0.call zc point mu child p
 · exact NLH_PartsStep1.call zc point mu child p
 · exact NLH_PartsStep2.call zc point mu child p
 · exact NLH_PartsStep3.call zc point mu child p
 · exact NLH_PartsStep4.call zc point mu child p
 · exact NLH_PartsStep5.call zc point mu child p
 · exact NLH_PartsStep6.call zc point mu child p
 · exact NLH_PartsStep7.call zc point mu child p
 · exact NLH_PartsStep8.call zc point mu child p
theorem step (pub : Public) (claims : Array NQ 84#usize) (point zc : Array NQ 10#usize)
 (lambda chi theta mu : NQ) (child : Carrier)
 (p : Calls zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2) (i : Fin 9) :
 NLH_PartsState.step pub claims point zc lambda chi theta mu (.arithmetic i) (stage child p i.val)=
 ok (.Ok (stage child p (i.val+1))) := by
 change (do let reply ← NLH_PartsState.arithmetic zc point mu (stage child p i.val) i
            ok (core.result.Result.Ok (NLH_PartsState.State.mk child
              (fun j => if j=i then reply else snapshot p i.val j)) : core.result.Result NLH_PartsState.State NKR_TermTail.Error))=_
 rw [call,bind_tc_ok,NLH_PartsValues.update]
 rfl
theorem arithmetic (pub : Public) (claims : Array NQ 84#usize) (point zc : Array NQ 10#usize)
 (lambda chi theta mu : NQ) (child : Carrier)
 (p : Calls zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2) :
 NLH_RustCuts.Cuts (NLH_PartsState.step pub claims point zc lambda chi theta mu)
 ((List.finRange 9).map NLH_PartsState.Event.arithmetic) (stage child p 0) (ok (.Ok (stage child p 9)))
 ((List.finRange 9).map NLH_PartsState.Event.arithmetic) := by
 change NLH_RustCuts.Cuts _ [NLH_PartsState.Event.arithmetic 0,NLH_PartsState.Event.arithmetic 1,NLH_PartsState.Event.arithmetic 2,NLH_PartsState.Event.arithmetic 3,NLH_PartsState.Event.arithmetic 4,NLH_PartsState.Event.arithmetic 5,NLH_PartsState.Event.arithmetic 6,NLH_PartsState.Event.arithmetic 7,NLH_PartsState.Event.arithmetic 8] _ _ _
 exact .next (step pub claims point zc lambda chi theta mu child p 0)
  (.next (step pub claims point zc lambda chi theta mu child p 1)
   (.next (step pub claims point zc lambda chi theta mu child p 2)
    (.next (step pub claims point zc lambda chi theta mu child p 3)
     (.next (step pub claims point zc lambda chi theta mu child p 4)
      (.next (step pub claims point zc lambda chi theta mu child p 5)
       (.next (step pub claims point zc lambda chi theta mu child p 6)
        (.next (step pub claims point zc lambda chi theta mu child p 7)
         (.next (step pub claims point zc lambda chi theta mu child p 8) (.nil (stage child p 9))))))))))
#print axioms call
#print axioms step
#print axioms arithmetic
end AspisR1.NLH_PartsFold
end
