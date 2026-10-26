import FIo_ArrayCanon
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_ArrayValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)

def value {N : Usize} (a : Array NE N) (n : Nat) : AspisWideTower.WideExact :=
  match a.val[n]? with | some x => decodeWide (wide x) | none => 0

theorem read {N : Usize} (a : Array NE N) (i : Usize) (z : NE)
    (run : Array.index_usize a i=ok z) : value a i.val=decodeWide (wide z) := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i x hx
    have same : x=z := Result.ok.inj run
    subst x
    change a.val[i.val]?=some z at hx
    simp only [value,hx]

#print axioms read
end AspisR1.FIp_ArrayValue
end
