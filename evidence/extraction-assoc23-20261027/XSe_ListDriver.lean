import XRx_StageRules
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XSe_ListDriver
/-- First-stop fold, parametric in items, state and error. -/
def fold {I E S : Type} (stage : I → S → Result (core.result.Result S E)) :
 List I → core.result.Result S E → Result (core.result.Result S E)
 | [],s => ok s
 | i::is,.Err e => ok (.Err e)
 | i::is,.Ok s => do
   let next ← stage i s
   fold stage is next

def body {I E S : Type} (stage : I → S → Result (core.result.Result S E))
 (s : List I × core.result.Result S E) :
 Result (ControlFlow (List I × core.result.Result S E) (core.result.Result S E)) :=
 match s with
 | ([],s) => ok (.done s)
 | (_::_,.Err e) => ok (.done (.Err e))
 | (i::is,.Ok s) => do
   let next ← stage i s
   ok (.cont (is,next))
/-- Emitted short-circuit loop and fold agree on the WHOLE state/error Result. -/
theorem source {I E S : Type} (stage : I → S → Result (core.result.Result S E))
 (items : List I) (s : core.result.Result S E) :
 loop (body stage) (items,s)=fold stage items s := by
 induction items generalizing s with
 | nil => rw [loop]; rfl
 | cons i is ih =>
   cases s with
   | Err e => rw [loop]; rfl
   | Ok s =>
     rw [loop]
     simp only [body]
     cases h : stage i s with
     | fail e => simp only [fold,h]; rfl
     | div => simp only [fold,h]; rfl
     | ok next =>
       simp only [h,bind_tc_ok]
       rw [ih]
       simp only [fold,h,bind_tc_ok]
/-- Any finishing continuation receives exactly the same surviving state. -/
theorem finish {I E S O : Type} (stage : I → S → Result (core.result.Result S E))
 (last : S → Result (core.result.Result O E)) (items : List I)
 (s : core.result.Result S E) :
 XRx_StageRules.chain (loop (body stage) (items,s)) last=
 XRx_StageRules.chain (fold stage items s) last := by rw [source]
#print axioms source
#print axioms finish
end XSe_ListDriver
