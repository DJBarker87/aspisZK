module
public import Lean
noncomputable section
namespace NEP_MutateMatch
public axiom privateAx : Nat
public axiom proofAx : True
public axiom auxAx : Nat
public def matcher (n : Nat) : Nat :=
  match n, n with
  | 0, _ => 0
  | _, 0 => 0
  | _+1, _+1 => 0
private def secret : Nat := privateAx
public def viaPrivate : Nat := secret
public theorem proof : True := proofAx
def hiddenAux : Nat := auxAx
public def viaAux : Nat := hiddenAux
end NEP_MutateMatch
