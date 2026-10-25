import Port10AUTH_Trace
import Port9OR_BatchStep
import Port4B_LeafCut

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Leaf
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port4B_NativeLeaf Port4B_LeafStep MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical

/-- Literal emitted active iteration, factored only at its hash boundary.
The post-hash duplicate comparison and checked writes are still executed. -/
theorem active (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Digest) (kind lo n slot d pos : Usize)
    (keys : Array U64 16#usize) (idx : Port9OR_BatchStep.Indices) (val : Port9OR_BatchStep.Values)
    (more : pos<n) :
    Port9OR_BatchStep.body base D proof root kind hash lo n slot keys idx val d pos =
      (do let key ← liftResult (Array.index_usize keys pos)
          let view ← liftResult (base.op2 proof (openingIndex lo key))
          let leaf ← Port4B_LeafCode.code kind view
          liftResult (post idx val d (decodedIndex key) leaf (Usize.wrapping_add pos 1#usize))) := by
  simp only [Port9OR_BatchStep.body,if_pos more,Port9OR_BatchStep.ops,Port3_BatchStd.install,
    Port4B_VerifyInstall.install,liftResult,CheckpointBytes5Effect.bind,lift,openingIndex,decodedIndex,post]
  rfl

/-- Exact one-read trace at the reached physical opening. Native hash failure
is retained; no all-input totality/Oracle law is assumed. -/
theorem leaf_trace {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (kind : Usize) (view : Slice U8) (size : view.val.length=832) :
    Port9OR_Code.trace D hash (Port4B_LeafCode.code kind view)=
      match D.digest hash (Port4B_LeafCode.input kind view) with
      | .ok d => ([(Port4B_LeafCode.input kind view,d)],.ok d)
      | .fail e => ([],.fail e)
      | .div => ([],.div) := by
  have range (s e : Usize) (order : s.val≤e.val) (fit : e.val≤832) :
      Port4B_LeafCode.readRange view s e=ok (MultiproofConeSlices.sub view s e) :=
    MultiproofConeSlices.range_total view s e order (by omega)
  unfold Port4B_LeafCode.code Port4B_LeafCode.input
  split
  · simp only [Port4B_LeafCode.codeFor,Port9OR_Code.trace,
      range 608#usize 640#usize (by decide) (by decide),
      range 0#usize 480#usize (by decide) (by decide)]
    cases D.digest hash _ <;> rfl
  · split
    · simp only [Port4B_LeafCode.codeFor,Port9OR_Code.trace,
        range 640#usize 672#usize (by decide) (by decide),
        range 480#usize 608#usize (by decide) (by decide)]
      cases D.digest hash _ <;> rfl
    · simp only [Port4B_LeafCode.codeFor,Port9OR_Code.trace,
        range 800#usize 832#usize (by decide) (by decide),
        range 672#usize 800#usize (by decide) (by decide)]
      cases D.digest hash _ <;> rfl

#print axioms active
#print axioms leaf_trace
end AspisR1.Port10AUTH_Leaf
end
