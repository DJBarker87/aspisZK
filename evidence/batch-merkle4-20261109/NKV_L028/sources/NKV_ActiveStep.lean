import NKV_ConcreteChildren
import Port4B_NativeLeaf
set_option autoImplicit false
noncomputable section
namespace NKV_ActiveStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open NKV_StepErasure NKV_LoopTransport

def restore : ControlFlow State CohortOut → ControlFlow State Out
 | .cont s => .cont s
 | .done (i,v,some r) => .done (i,v,r,false)
 | .done (i,v,none) => .done (i,v,.Err .Parse,true)

/-- The in-loop Rust Err is preserved in the adopted emission. Only tail
exits need the rejection observation. This equality covers fail/div too. -/
theorem source (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (root : Array U8 32#usize) (tree : Usize) (hash : H)
 (lo n slot : Usize) (keys : Array U64 16#usize) (idx : Indices) (val : Values)
 (d pos : Usize) (more : pos<n) :
 mapResult restore (AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
   ops D proof root tree hash lo n slot keys idx val d pos)=
 NKV_FRef.verifier.candidate.batch_tree_loop.body
   ops D proof root tree hash lo n slot keys idx val d pos := by
 unfold AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
   NKV_FRef.verifier.candidate.batch_tree_loop.body
 simp only [if_pos more,map_bind,map_ite,map_pair,map_cf,map_ok,restore]
 rfl

set_option pp.proofs false
#print source
#print axioms source
end NKV_ActiveStep
end
