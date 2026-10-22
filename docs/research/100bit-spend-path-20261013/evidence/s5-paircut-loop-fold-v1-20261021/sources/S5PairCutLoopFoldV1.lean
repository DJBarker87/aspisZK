import S5PairCutFieldCallbackV1
import EbyKPushStateInvariantStepV1
import EbyKPushPairWrapperStepV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5PairCutLoopFoldV1

open AspisR1S5PairCutFieldCallbackV1
open AspisR1S5EbyKConcreteOpsInstanceV1
open AspisR1WeightsPairCutEbyKDotOpsV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps :=
  sourceOps

abbrev PairQM := AspisR1WeightsPairCut.field.QM31
abbrev PushState := AspisR1EbyKPushDotBackend.PushState
abbrev PushWide := AspisR1EbyKPushDotBackend.PushWide
abbrev PushQm := AspisR1EbyKPushDotBackend.PushQm
abbrev PairWide := AspisR1WeightsPairCut.field.WideExact
abbrev LoopState := (core.ops.range.Range Usize) ×
  AspisR1WeightsPairCut.fast_pairing.EbyKDot
abbrev LoopOutput := (core.result.Result Unit AspisR1WeightsPairCut.verifier.Error) ×
  AspisR1WeightsPairCut.fast_pairing.EbyKDot
abbrev BodyCF := core.ops.control_flow.ControlFlow LoopOutput LoopState

/-- Exact post-push branch of the emitted body.  The closure maps an inner
push error to `Parse`; the Try branch then returns that error with the updated
pair, while success continues with the already advanced iterator. -/
def pushByteProductsPostPush (iter1 : core.ops.range.Range Usize)
    (r : core.result.Result Unit Unit) (pair1 :
      AspisR1WeightsPairCut.fast_pairing.EbyKDot) :
    Result BodyCF :=
  match r with
  | .Ok () => .ok (core.ops.control_flow.ControlFlow.Continue (iter1, pair1))
  | .Err _ => .ok (core.ops.control_flow.ControlFlow.Break
      (core.result.Result.Err AspisR1WeightsPairCut.verifier.Error.Parse, pair1))

/-- For the concrete callback trace we keep the byte slice explicit.  This
specialized form avoids manufacturing a slice inside the source-shaped body. -/
def pushByteProductsAfterNextAt
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM)
    (iter1 : core.ops.range.Range Usize) (j : Usize)
    (pair : AspisR1WeightsPairCut.fast_pairing.EbyKDot) :
    Result BodyCF := do
  let value ← read bytes j
  let scalar ← Slice.index_usize scratch j
  let (r, pair1) ← AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
    pair value scalar
  pushByteProductsPostPush iter1 r pair1

/-- Full one-iteration body adapter.  The iterator implementation is a
parameter so the theorem does not import PairCut's generated external
declarations; the emitted operation order and both Continue/Break branches are
represented directly. -/
def pushByteProductsBodyWith
    (next : core.ops.range.Range Usize →
      Result (Option Usize × core.ops.range.Range Usize))
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM)
    (iter : core.ops.range.Range Usize)
    (pair : AspisR1WeightsPairCut.fast_pairing.EbyKDot) :
    Result BodyCF := do
  let (o, iter1) ← next iter
  match o with
  | none => .ok (core.ops.control_flow.ControlFlow.Break
      (core.result.Result.Ok (), pair))
  | some j => pushByteProductsAfterNextAt read bytes scratch iter1 j pair

theorem callback_body_success_continue
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM)
    (iter iter1 : core.ops.range.Range Usize) (j : Usize)
    (pair pair1 : AspisR1WeightsPairCut.fast_pairing.EbyKDot)
    (value : PairWide) (scalar : PairQM)
    (hread : read bytes j = .ok value)
    (hscalar : Slice.index_usize scratch j = .ok scalar)
    (hpush : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
      pair value scalar = .ok (.Ok (), pair1)) :
    pushByteProductsAfterNextAt read bytes scratch iter1 j pair =
      .ok (core.ops.control_flow.ControlFlow.Continue (iter1, pair1)) := by
  simp [pushByteProductsAfterNextAt, hread, hscalar, hpush,
    pushByteProductsPostPush]

theorem emitted_body_success_continue
    (next : core.ops.range.Range Usize →
      Result (Option Usize × core.ops.range.Range Usize))
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM)
    (iter iter1 : core.ops.range.Range Usize) (j : Usize)
    (pair pair1 : AspisR1WeightsPairCut.fast_pairing.EbyKDot)
    (value : PairWide) (scalar : PairQM)
    (hnext : next iter = .ok (some j, iter1))
    (hread : read bytes j = .ok value)
    (hscalar : Slice.index_usize scratch j = .ok scalar)
    (hpush : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
      pair value scalar = .ok (.Ok (), pair1)) :
    pushByteProductsBodyWith next read bytes scratch iter pair =
      .ok (core.ops.control_flow.ControlFlow.Continue (iter1, pair1)) := by
  simp [pushByteProductsBodyWith, hnext, callback_body_success_continue,
    hread, hscalar, hpush, pushByteProductsAfterNextAt,
    pushByteProductsPostPush]

theorem callback_body_success_continue_preserves_kernel
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM)
    (iter iter1 : core.ops.range.Range Usize) (j : Usize)
    (pair pair1 : AspisR1WeightsPairCut.fast_pairing.EbyKDot)
    (value : PairWide) (scalar : PairQM)
    (hread : read bytes j = .ok value)
    (hscalar : Slice.index_usize scratch j = .ok scalar)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
      (AspisR1WeightsPairCutEbyKDotOpsV1.wideToSource value))
    (hscalarCanonical : ∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ
      (AspisR1WeightsPairCutEbyKDotOpsV1.qToSource scalar)).val,
      x.val < 2147483647)
    (hinv0 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource pair).count.val
      (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource pair).c0.sums)
    (hinv1 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource pair).count.val
      (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource pair).c1.sums)
    (hcount : (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource pair).count <
      AspisR1EbyKPushExplicitOpsV1.maxTerms)
    (hpush : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
      pair value scalar = .ok (.Ok (), pair1)) :
    pushByteProductsAfterNextAt read bytes scratch iter1 j pair =
      .ok (core.ops.control_flow.ControlFlow.Continue (iter1, pair1)) ∧
    AspisR1FinishDotCountBoundV2.sumsBelowCount
      (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource pair1).count.val
      (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource pair1).c0.sums ∧
    AspisR1FinishDotCountBoundV2.sumsBelowCount
      (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource pair1).count.val
      (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource pair1).c1.sums ∧
    (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource pair1).count.val =
      (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource pair).count.val + 1 := by
  have hcontinue := callback_body_success_continue read bytes scratch iter iter1 j
    pair pair1 value scalar hread hscalar hpush
  obtain ⟨_sourceOut, _hsource, _hmap, h0, h1, hinc, _hp0, _hp1⟩ :=
    AspisR1S5EbyKPushPairWrapperStepV1.installed_push_state_step
      pair value scalar pair1 hcanonical hcount hscalarCanonical hinv0 hinv1 hpush
  exact ⟨hcontinue, h0, h1, hinc⟩

/-- Per-index premises for the source-shaped callback fold.  The field reader
is parameterized so the exact helper/decoder can be plugged in without
importing PairCut's external `weights.field` axiom. -/
def CallbackEntryValid
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM) (j : Usize) : Prop :=
  ∃ value scalar, read bytes j = .ok value ∧
    Slice.index_usize scratch j = .ok scalar ∧
    AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
      (AspisR1WeightsPairCutEbyKDotOpsV1.wideToSource value) ∧
    (∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ
      (AspisR1WeightsPairCutEbyKDotOpsV1.qToSource scalar)).val,
      x.val < 2147483647)

/-- A finite source-order trace for the successful branch of
`weights.push_byte_products_loop.body`.  Each entry records the field callback,
scratch lookup, and installed EbyK transition in their emitted order. -/
inductive CallbackPushTrace
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM) :
    PushState → List Usize → PushState → Prop where
  | nil (s : PushState) : CallbackPushTrace read bytes scratch s [] s
  | cons {s mid out : PushState} {j : Usize} {js : List Usize}
      {v : PairWide} {q : PairQM}
      (hread : read bytes j = .ok v)
      (hscalar : Slice.index_usize scratch j = .ok q)
      (hpush : AspisR1EbyKPushDotBackend.pushWithDotBackend
        AspisR1EbyKPushDecodedProductUpdate.QRaw s
        (AspisR1WeightsPairCutEbyKDotOpsV1.wideToSource v)
        (AspisR1WeightsPairCutEbyKDotOpsV1.qToSource q) = .ok (.Ok (), mid))
      (htail : CallbackPushTrace read bytes scratch mid js out) :
      CallbackPushTrace read bytes scratch s (j :: js) out

/-- Callback-parameterized fold bridge: for an index schedule whose concrete
field and scratch reads succeed, canonical field values and canonical scalar
coordinates produce a successful ordered EbyK push trace.  This is the local
successful-Continue fold; IteratorRange advancement and PairCut's
external-symbol refinement remain separate source boundaries. -/
theorem callback_push_trace_total
    (read : Slice U8 → Usize → Result PairWide)
    (bytes : Slice U8) (scratch : Slice PairQM)
    (s : PushState) (js : List Usize)
    (hroom : s.count.val + js.length ≤ 4096)
    (hinv0 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      s.count.val s.c0.sums)
    (hinv1 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      s.count.val s.c1.sums)
    (hentries : ∀ j, j ∈ js → CallbackEntryValid read bytes scratch j) :
    ∃ out, CallbackPushTrace read bytes scratch s js out ∧
      AspisR1FinishDotCountBoundV2.sumsBelowCount out.count.val out.c0.sums ∧
      AspisR1FinishDotCountBoundV2.sumsBelowCount out.count.val out.c1.sums ∧
      out.count.val = s.count.val + js.length := by
  induction js generalizing s with
  | nil =>
      refine ⟨s, CallbackPushTrace.nil s, hinv0, hinv1, ?_⟩
      simp
  | cons j js ih =>
      have hjmem : j ∈ j :: js := by simp
      have hroom'' : s.count.val + (js.length + 1) ≤ 4096 := by
        simpa only [List.length_cons] using hroom
      have hcountVal : s.count.val < 4096 := by omega
      have hcount : s.count < AspisR1EbyKPushExplicitOpsV1.maxTerms := by
        simpa [AspisR1EbyKPushExplicitOpsV1.maxTerms] using hcountVal
      obtain ⟨value, scalar, hread, hscalar, hcanonical, hscalarCanonical⟩ :=
        hentries j hjmem
      obtain ⟨mid, hpush, hinv0', hinv1', hinc, _hprod0, _hprod1⟩ :=
        AspisR1S5EbyKPushStateInvariantStepV1.push_success_state_step
          s (AspisR1WeightsPairCutEbyKDotOpsV1.wideToSource value)
          (AspisR1WeightsPairCutEbyKDotOpsV1.qToSource scalar)
          hcanonical hcount hscalarCanonical hinv0 hinv1
      have hroom' : mid.count.val + js.length ≤ 4096 := by
        rw [hinc]
        omega
      have hentries' : ∀ k, k ∈ js → CallbackEntryValid read bytes scratch k := by
        intro k hk
        exact hentries k (by simp [hk])
      obtain ⟨out, htail, hout0, hout1, hfinal⟩ :=
        ih mid hroom' hinv0' hinv1' hentries'
      refine ⟨out, CallbackPushTrace.cons hread hscalar hpush htail,
        hout0, hout1, ?_⟩
      rw [hinc] at hfinal
      calc
        out.count.val = (s.count.val + 1) + js.length := hfinal
        _ = s.count.val + (j :: js).length := by simp only [List.length_cons]; omega

/-- The checked concrete field helper supplies the canonical-output component
of `CallbackEntryValid` directly.  Scratch lookup and scalar-coordinate bounds
are intentionally explicit caller premises. -/
theorem checked_callback_entry_valid
    (bytes : Slice U8) (scratch : Slice PairQM) (j : Usize)
    (value : PairWide) (scalar : PairQM)
    (hread : checkedFieldCallback bytes j = .ok value)
    (hscalar : Slice.index_usize scratch j = .ok scalar)
    (hscalarCanonical : ∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ
      (AspisR1WeightsPairCutEbyKDotOpsV1.qToSource scalar)).val,
      x.val < 2147483647) :
    CallbackEntryValid checkedFieldCallback bytes scratch j := by
  exact ⟨value, scalar, hread, hscalar,
    checkedFieldCallback_success_push_canonical bytes j value hread,
    hscalarCanonical⟩

#print axioms callback_push_trace_total
#print axioms checked_callback_entry_valid
#print axioms emitted_body_success_continue
#print axioms callback_body_success_continue_preserves_kernel
end AspisR1S5PairCutLoopFoldV1
