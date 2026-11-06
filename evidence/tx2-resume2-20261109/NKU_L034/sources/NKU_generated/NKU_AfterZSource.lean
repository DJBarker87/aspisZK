import NKU_Pack
import NKK_AllocationStage
set_option autoImplicit false
noncomputable section
namespace NKU_AfterZSource
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
/-- Exact source continuation after power43, before SAME reservation44. -/
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (semantic : Array NKU.K 10#usize)
 (x0 y0 x1 y1 : NKU.K) (claim rhs : NKU.E) (power : NKU.K) (r : verifier.Reader) :
 Run (core.result.Result NKU.Pair verifier.Error) := do
 let allocated ← NKK_AllocationStage.source s.frame.reservation d
 NKK_Try.emitted allocated fun owner=>do
 let reply ← recordWeights s.frame.checkpoint r.at owner
 NKK_Try.emitted reply fun (weights,cursor)=>do
 if cursor != «end» then pure (.Err .Checkpoint) else do
 let n ← lift (UScalar.cast .Usize next)
 pure (.Ok ({variant := .S2,roots := Array.make 2#usize [a3,a4],gamma := g,kappa := k,alpha := Array.make 2#usize [a0,a1],rho,queries,semantic_alpha := semantic,z := Array.make 2#usize [{x := x0,y := y0},{x := x1,y := y1}],claim,state},{weights,rhs,power,next := n}))
end NKU_AfterZSource
