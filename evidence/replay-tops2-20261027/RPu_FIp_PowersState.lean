import RPu_FIp_ArraySetValue
import RPu_FIo_PowersCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_PowersState
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
abbrev FE := AspisWideTower.WideExact
abbrev State (N : Usize) := FIo_PowersCanonical.State N

def Inv {N : Usize} (x : NE) (s : State N) : Prop :=
  FIo_PowersCanonical.Inv s ∧ s.2.2.val≤N.val ∧
  decodeWide (wide s.2.1)=decodeWide (wide x)^s.2.2.val ∧
  ∀ j, j<s.2.2.val → FIp_ArrayValue.value s.1 j=decodeWide (wide x)^j

def Post {N : Usize} (x : NE) (a : Array NE N) : Prop :=
  FIo_ArrayCanon.Holds a ∧ ∀ j,j<N.val → FIp_ArrayValue.value a j=decodeWide (wide x)^j

#print Inv
#print Post
end AspisR1.FIp_PowersState
end
