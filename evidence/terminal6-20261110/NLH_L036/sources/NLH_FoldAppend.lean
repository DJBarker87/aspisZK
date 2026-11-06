import NLH_FoldCore
import NLH_RustCuts
set_option autoImplicit false
namespace AspisR1.NLH_FoldAppend
open Aeneas Aeneas.Std Result
theorem plain {S E : Type} {step : E → S → Result S}
 {first rest leftLog rightLog : List E} {before middle : S} {out : Result S}
 (left : NLH_FoldCore.Cuts step first before (ok middle) leftLog)
 (right : NLH_FoldCore.Cuts step rest middle out rightLog) :
 NLH_FoldCore.Cuts step (first++rest) before out (leftLog++rightLog) := by
 induction first generalizing before leftLog with
 | nil => cases left;exact right
 | cons e es ih =>
   cases left with
   | next h tail => exact .next h (ih tail)
theorem rust {S E R : Type} {step : E → S → Result (core.result.Result S R)}
 {first rest leftLog rightLog : List E} {before middle : S} {out : Result (core.result.Result S R)}
 (left : NLH_RustCuts.Cuts step first before (ok (.Ok middle)) leftLog)
 (right : NLH_RustCuts.Cuts step rest middle out rightLog) :
 NLH_RustCuts.Cuts step (first++rest) before out (leftLog++rightLog) := by
 induction first generalizing before leftLog with
 | nil => cases left;exact right
 | cons e es ih =>
   cases left with
   | next h tail => exact .next h (ih tail)
#print axioms plain
#print axioms rust
end AspisR1.NLH_FoldAppend
