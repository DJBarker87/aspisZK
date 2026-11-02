module
public import Lean
noncomputable section
namespace NEP_MutateAux
public axiom matchAx : Nat
public axiom privateAx : Nat
public axiom proofAx : True
public def matcher (n : Nat) : Nat :=
  match n, n with
  | 0, _ => matchAx
  | _, 0 => 0
  | _+1, _+1 => matchAx
private def secret : Nat := privateAx
public def viaPrivate : Nat := secret
public theorem proof : True := proofAx
def hiddenAux : Nat := 0
public def viaAux : Nat := hiddenAux
end NEP_MutateAux
