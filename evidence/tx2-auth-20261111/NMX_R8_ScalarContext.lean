import NMX_R8_Stops
set_option autoImplicit false
namespace NMX_R8_ScalarContext
open Aeneas Aeneas.Std Result RSL NMS_R2N_Interpreted

theorem context {A B C : Type} (r : Result A) (f : A → Result B) (k : B → Spec C) :
 Spec.bind (liftResult r) (fun a => Spec.bind (liftResult (f a)) k) =
 Spec.bind (liftResult (r >>= f)) k := by
 cases r with
 | ok a => simp only [bind_tc_ok,liftResult,Spec.bind_pure]
 | fail error => simp only [bind_tc_fail,liftResult,NMX_R8_Stops.panic_bind]
 | div =>
   simp only [bind_tc_div,liftResult]
   change Spec.bind NMX_R8_Stops.diverge _ = Spec.bind NMX_R8_Stops.diverge _
   simp only [NMX_R8_Stops.diverge_bind]
#print axioms context
end NMX_R8_ScalarContext
