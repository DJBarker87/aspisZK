import NLH_TermHornerCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_HornerTrace
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NLH_TermHornerCut (Trace)
theorem append {p xs ys before middle out} (left : Trace p xs before middle) (right : Trace p ys middle out) :
 Trace p (xs++ys) before out := by
 induction left with
 | nil => exact right
 | cons pm ma cut _ ih => exact .cons pm ma cut (ih right)
theorem unique {p xs before out out'} (first : Trace p xs before out) (second : Trace p xs before out') : out=out' := by
 induction first generalizing out' with
 | nil => cases second;rfl
 | cons pm ma cut tail ih =>
   cases second with
   | cons pm' ma' _ tail' =>
     have products := Result.ok.inj (pm.symm.trans pm')
     cases products
     have middle := Result.ok.inj (ma.symm.trans ma')
     cases middle
     exact ih tail'
#print axioms append
#print axioms unique
end AspisR1.NLH_HornerTrace
end
