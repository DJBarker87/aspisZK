import PV_STX_PrefixLaws
set_option autoImplicit false
namespace PV_STX_Composition
open Aeneas Aeneas.Std PV_STX_Code PV_STX_Machine
variable {Op : Type → Type 1} {W E A B : Type}

/-- The second reached primitive is interpreted at the FIRST reply's world,
not at the entry world or a reselected fixed dictionary. All second outcomes,
including source fail and div, preserve both event segments and its post-world. -/
theorem two_calls (handler : Handler Op W E) (first : Op A) (next : A → Op B)
    (w : W) (a : A) (r : Result B)
    (hfirst : (handler first w).answer = .returned (.ok a))
    (hnext : (handler (next a) (handler first w).world).answer = .returned r) :
    run handler 3 (.seq (.call first) (fun a => .call (next a))) w =
      ⟨.returned r,(handler (next a) (handler first w).world).world,
        (handler first w).events ++ (handler (next a) (handler first w).world).events⟩ := by
  cases r <;>
    simp only [run,advance,start,step,resumed,continueWith,hfirst,hnext,List.nil_append,List.append_nil]

/-- A first-call fault cannot execute the second request, even if that second
request would have succeeded. The first-call post-world is retained. -/
theorem first_fault (handler : Handler Op W E) (first : Op A) (next : A → Op B)
    (w : W) (fault : Fault)
    (hfirst : (handler first w).answer = .fault fault) :
    run handler 3 (.seq (.call first) (fun a => .call (next a))) w =
      ⟨.fault fault,(handler first w).world,(handler first w).events⟩ := by
  simp only [run,advance,start,step,hfirst,List.nil_append]

#print axioms two_calls
#print axioms first_fault
end PV_STX_Composition
