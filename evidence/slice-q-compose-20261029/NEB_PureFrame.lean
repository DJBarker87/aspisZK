import Aeneas
set_option autoImplicit false
namespace NEB_PureFrame
open Aeneas Aeneas.Std Result

def run {A S Event : Type} (s : S) (r : Result A) : Result (A × S × List Event) := do
  let z ← r
  ok (z,s,[])

theorem successful {A S Event : Type} (s : S) (r : Result A) (z : A) (h : r=ok z) :
    run (Event:=Event) s r=ok (z,s,[]) := by
  simp only [run,h,bind_tc_ok]

theorem equality {A S Event : Type} (s : S) (r t : Result A) (h : r=t) :
    run (Event:=Event) s r=run s t := by rw [h]

#print axioms successful
#print axioms equality
end NEB_PureFrame
