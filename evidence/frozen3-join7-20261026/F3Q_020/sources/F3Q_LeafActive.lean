import F3Q_LeafPost
import F3Q_LeafEval
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_LeafActive
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values Next Out)
open Port4B_NativeLeaf MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem active {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Digest) (tree lo n slot d pos : Usize)
    (keys : Array U64 16#usize) (idx : Indices) (val : Values) (more : pos<n) :
    Port9OR_BatchStep.body Port4B_Install.leaves D proof root tree hash lo n slot keys idx val d pos=
      (do let key ← liftResult (Array.index_usize keys pos)
          let view ← liftResult (Port4B_Install.leaves.op2 proof (openingIndex lo key))
          let leaf ← Port4B_LeafCode.code tree view
          F3Q_LeafPost.code idx val d (decodedIndex key) leaf (Usize.wrapping_add pos 1#usize)) := by
  unfold Port9OR_BatchStep.body
  rw [if_pos more]
  rfl

theorem step_eval {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (proof : Slice U8) (root : Digest) (tree lo n slot pos : Usize)
    (keys : Array U64 16#usize) (s : reference.Scratch) (key : U64) (view : Slice U8)
    (more : pos<n) (keyRead : Array.index_usize keys pos=ok key)
    (viewRead : Port4B_Install.leaves.op2 proof (openingIndex lo key)=ok view)
    (size : view.val.length=832) :
    eval H (SdkC_Oracle.program (Port9OR_BatchStep.body Port4B_Install.leaves D proof root tree hash
      lo n slot keys s.idx s.val s.n pos))=
      ([(flatten (Port4B_LeafCode.input tree view),H (flatten (Port4B_LeafCode.input tree view)))],
       Port4B_LeafStep.post s.idx s.val s.n (decodedIndex key)
        (encodeState (H (flatten (Port4B_LeafCode.input tree view)))) (Usize.wrapping_add pos 1#usize)) := by
  rw [active D hash proof root tree lo n slot s.n pos keys s.idx s.val more]
  simp only [Bind.bind,F3Q_CodeEval.lift_bind_eval,keyRead,viewRead,F3Q_CodeEval.bind_eval,
    F3Q_LeafEval.leaf H tree view size,F3Q_LeafPost.eval_post,List.append_nil]

#print axioms active
#print axioms step_eval
end AspisR1.F3Q_LeafActive
end
