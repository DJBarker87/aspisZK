import NHI_KindDomain
set_option autoImplicit false
noncomputable section
namespace NHM_RegularKinds
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
variable [FIo_Native.Allocation]
abbrev Scratch := alloc.vec.Vec NQ
abbrev Parts := Array NE 7#usize
abbrev Reply := core.result.Result Unit FIo_Native.verifier.Error × Scratch × Parts

def kinds (shared : Bool) : List Usize := if shared then [2#usize,5#usize,6#usize]
 else [1#usize,2#usize,3#usize,5#usize,6#usize]

def go (child : Usize→Scratch→Parts→Result Reply) : List Usize→Scratch→Parts→Result Reply
 | [],scratch,parts=>ok (.Ok (),scratch,parts)
 | kind::rest,scratch,parts=>do
  let (r,scratch1,parts1) ← child kind scratch parts
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _=>go child rest scratch1 parts1
  | core.ops.control_flow.ControlFlow.Break residual=>do
   let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    Unit (core.convert.FromSame FIo_Native.verifier.Error) residual
   ok (r1,scratch1,parts1)

def reference (w : FIo_Native.weights.Weights) (shared : Bool) (alpha : Slice NE) (f : Slice U8)
 (folds n : Usize) (ap0 ap1 : Array NE 4#usize) (scratch : Scratch) (parts : Parts) :=
 go (fun k s p=>FIo_Native.weights.process_kind w k alpha f folds n ap0 ap1 s p)
  (kinds shared) scratch parts

/-- Exact SAME-state source order on both guard arms, including every child error.
This is model composition only; the process_kind/native driver packets remain OPEN. -/
theorem cohort (w : FIo_Native.weights.Weights) (shared : Bool) (alpha : Slice NE) (f : Slice U8)
 (folds n : Usize) (ap0 ap1 : Array NE 4#usize) (scratch : Scratch) (parts : Parts) :
 FIo_Native.weights.process_regular_kinds w shared alpha f folds n ap0 ap1 scratch parts=
 reference w shared alpha f folds n ap0 ap1 scratch parts := by
 cases shared <;> rfl

theorem first_error (child : Usize→Scratch→Parts→Result Reply) (k : Usize) (rest : List Usize)
 (scratch scratch1 : Scratch) (parts parts1 : Parts) (e : FIo_Native.verifier.Error)
 (run : child k scratch parts=ok (.Err e,scratch1,parts1)) :
 go child (k::rest) scratch parts=ok (.Err e,scratch1,parts1) := by
 rw [go,run]
 rfl

theorem after_ok (child : Usize→Scratch→Parts→Result Reply) (k : Usize) (rest : List Usize)
 (scratch scratch1 : Scratch) (parts parts1 : Parts)
 (run : child k scratch parts=ok (.Ok (),scratch1,parts1)) :
 go child (k::rest) scratch parts=go child rest scratch1 parts1 := by
 rw [go,run]
 rfl

#print axioms cohort
#print axioms first_error
#print axioms after_ok
end NHM_RegularKinds
end
