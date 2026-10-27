import RPu_FIo_ArrayBack
import RPt_FIo_Constants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_ArrayValue
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE wide)
abbrev decode (x : NE) := AspisR1CurrentWide.Proof.decodeWide (wide x)
abbrev E := AspisWideTower.WideExact

def value {N : Usize} (a : Array NE N) (i : Nat) : E :=
  ((a.val[i]?).map decode).getD 0

theorem read {N : Usize} (a : Array NE N) (i : Usize) (x : NE)
    (run : Array.index_usize a i=ok x) : decode x=value a i.val := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i z hz
    have same : z=x := Result.ok.inj run
    subst z
    change a.val[i.val]?=some x at hz
    simp only [value,hz,Option.map_some,Option.getD_some]

#print axioms read
end AspisR1.FGm_ArrayValue
end
