import PV_L2B_SamplerLaw
import PV_L2B_Rejection
set_option autoImplicit false
namespace PV_L2B_EntropyTrace
-- Per successful 64-byte fill: 0=first zero (second check skipped),
-- 1=second zero, 2=both nonzero. OS error schedule is a separate input.
def kind {A B : Type} : Option A × Option B → Nat
 | (none, _) => 0
 | (some _, none) => 1
 | (some _, some _) => 2
def checks (kind : Nat) : Nat := if kind=0 then 1 else 2
def branches {A B : Type} : Nat → List (Option A × Option B) → List Nat
 | 0, _ => []
 | _+1, [] => []
 | n+1, x::xs => if kind x=2 then [2] else kind x :: branches n xs
theorem first_zero {A B : Type} (b : Option B) : kind ((none : Option A), b)=0 := rfl
#print axioms first_zero
end PV_L2B_EntropyTrace
