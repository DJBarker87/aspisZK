import NKU_Chronology
import NKU_Array22
set_option autoImplicit false
noncomputable section
namespace NKU_Tail
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
/-- Complete decoded value passed to the retained Prepared/Accumulator
constructor cuts. The SAME owned weights move into the returned accumulator. -/
def build (s : NKU.State) : Result (core.result.Result NKU.Pair verifier.Error) :=
 match s.decoded.next,s.decoded.endAt,s.decoded.roots,s.decoded.gammaAlpha,
   s.decoded.rho,s.decoded.semantic,s.decoded.z,s.decoded.claim,s.decoded.rhs,s.decoded.power,s.owned with
 | some next,some «end»,[state,a3,a4],[g,k,a0,a1],some rho,some semantic,
   [x0,y0,x1,y1],some claim,some rhs,some power,some weights => do
   if s.reader.at != «end» then ok (.Err .Checkpoint) else do
   let queries ← NKU_Validator.values s.decoded.queries
   let n ← lift (UScalar.cast .Usize next)
   ok (.Ok ({variant := .S2,roots := Array.make 2#usize [a3,a4],gamma := g,kappa := k, alpha := Array.make 2#usize [a0,a1],rho,queries,semantic_alpha := semantic, z := Array.make 2#usize [{x := x0,y := y0},{x := x1,y := y1}],claim,state},
    {weights,rhs,power,next := n}))
 | _,_,_,_,_,_,_,_,_,_,_ => fail .panic
/-- The returned terminal state retains the complete value on the same carrier.
An abort has no following event; rejected weights cleanup stays a native cut. -/
def run (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := liftM (build s)
theorem guard_reject (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (semantic : Array NKU.K 10#usize) (x0 y0 x1 y1 : NKU.K) (claim rhs : NKU.E)
 (power : NKU.K) (weights : alloc.vec.Vec NKU.K)
 (different : s.reader.at != «end») :
 build {s with decoded := {s.decoded with next := some next,endAt := some «end», roots := [state,a3,a4],gammaAlpha := [g,k,a0,a1],rho := some rho,semantic := some semantic, z := [x0,y0,x1,y1],claim := some claim,rhs := some rhs,power := some power},owned := some weights}=
 ok (.Err .Checkpoint) := by
 unfold build
 simp only [different,ite_true]
#print axioms guard_reject
end NKU_Tail
