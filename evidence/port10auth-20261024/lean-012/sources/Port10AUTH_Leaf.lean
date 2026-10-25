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

theorem lift_bind {A B X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (hash : X) (r : Result A) (k : A → Code B) :
    Port9OR_Code.trace D hash (liftResult r >>= k)=match r with
      | .ok a => Port9OR_Code.trace D hash (k a)
      | .fail e => ([],.fail e)
      | .div => ([],.div) := by cases r <;> rfl

theorem pure_trace {A X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (hash : X) (a : A) : Port9OR_Code.trace D hash (pure a)=([],ok a) := rfl

/-- Literal emitted active iteration at its actual key and opening reads.
The hash remains before the duplicate check, including duplicate rejection. -/
theorem active (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Digest) (kind lo n slot d pos : Usize)
    (keys : Array U64 16#usize) (idx : Port9OR_BatchStep.Indices) (val : Port9OR_BatchStep.Values)
    (key : U64) (view : Slice U8) (more : pos<n)
    (keyRead : Array.index_usize keys pos=ok key)
    (viewRead : (Port9OR_BatchStep.ops base).op2 proof (openingIndex lo key)=ok view) :
    Port9OR_Code.trace D hash (Port9OR_BatchStep.body base D proof root kind hash lo n slot keys idx val d pos) =
      Port9OR_Code.trace D hash (do
        let leaf ← Port4B_LeafCode.code kind view
        liftResult (post idx val d (decodedIndex key) leaf (Usize.wrapping_add pos 1#usize))) := by
  unfold Port9OR_BatchStep.body
  rw [if_pos more]
  have kr : (Port9OR_BatchStep.ops base).op9 keys pos=ok key := keyRead
  simp only [openingIndex] at viewRead
  simp only [lift_bind,kr,lift,viewRead,openingIndex,decodedIndex]
  simp only [Port10AUTH_Trace.trace_bind]
  cases h : Port9OR_Code.trace D hash (Port4B_LeafCode.code kind view) with
  | mk log result =>
    cases result with
    | fail e => rfl
    | div => rfl
    | ok leaf =>
      simp only [Port10AUTH_Trace.trace_lift,post]
      simp only [Port9OR_BatchStep.ops,Port3_BatchStd.install]
      repeat'
        first
        | rfl
        | exact True.intro
        | apply And.intro
        | (fail_if_no_progress dsimp only)
        | (fail_if_no_progress simp only [lift_bind,pure_trace,lift,bind_tc_ok,
            List.append_nil,List.nil_append])
        | (split <;> (try simp_all only [Prod.mk.injEq,Result.ok.injEq,if_true,if_false]))
      all_goals (try constructor) <;> first | rfl | exact List.append_nil _

/-- Exact one-read trace at the reached physical opening. Native hash failure
is retained; no all-input totality/Oracle law is assumed. -/
theorem leaf_trace {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
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

/-- Actual successful emitted iteration forces its one physical hash to
succeed. The entire log is retained even when its inner result rejects a
conflicting duplicate; no suffix, deduplication or caching is applied here. -/
theorem accepted_trace (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Digest) (kind lo n slot d pos : Usize)
    (keys : Array U64 16#usize) (idx : Port9OR_BatchStep.Indices) (val : Port9OR_BatchStep.Values)
    (key : U64) (view : Slice U8) (more : pos<n)
    (keyRead : Array.index_usize keys pos=ok key)
    (viewRead : (Port9OR_BatchStep.ops base).op2 proof (openingIndex lo key)=ok view)
    (size : view.val.length=832) (out : ControlFlow Port9OR_BatchStep.Next Port9OR_BatchStep.Out)
    (accepted : erase D hash (Port9OR_BatchStep.body base D proof root kind hash lo n slot keys idx val d pos)=ok out) :
    ∃ digest, D.digest hash (Port4B_LeafCode.input kind view)=ok digest ∧
      post idx val d (decodedIndex key) digest (Usize.wrapping_add pos 1#usize)=ok out ∧
      Port9OR_Code.trace D hash (Port9OR_BatchStep.body base D proof root kind hash lo n slot keys idx val d pos)=
        ([(Port4B_LeafCode.input kind view,digest)],ok out) := by
  have factor := active base D hash proof root kind lo n slot d pos keys idx val key view more keyRead viewRead
  rw [Port10AUTH_Trace.trace_bind,leaf_trace D hash kind view size] at factor
  have success := (Port9OR_Code.trace_value D hash _).trans accepted
  rw [factor] at success
  cases call : D.digest hash (Port4B_LeafCode.input kind view) with
  | fail e => simp only [call] at success;cases success
  | div => simp only [call] at success;cases success
  | ok digest =>
    simp only [call,Port10AUTH_Trace.trace_lift] at success factor
    exact ⟨digest,rfl,success,by simpa only [List.append_nil,success] using factor⟩

#print axioms lift_bind
#print axioms pure_trace
#print axioms accepted_trace
#print axioms active
#print axioms leaf_trace
end AspisR1.Port10AUTH_Leaf
end
