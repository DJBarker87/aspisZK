import AspisV8R19.R144BeforeOodBytesBridge
import AspisV8R19.R141BeforeOodPrimitiveBridge
import AspisV8R19.R140BeforeOodSampleBridge

/-! Exact selected before_ood result and state. The raw chronology retains
arbitrary hash errors and divergence. The modeled chronology uses an explicit
byte oracle and preserves both callback sampler failures and short claim input.
Shared-oracle traces and probability laws are separate obligations. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace AspisV8R19.R146BeforeOodBridge
open Aeneas Aeneas.Std Result
open AspisR136BeforeOod
open AspisV8R19 R144BeforeOodBytesBridge

abbrev Values := alloc.vec.Vec aspis_core.field.QM31
abbrev Transcript := aspis_core.transcript.Transcript
abbrev Outcome := core.result.Result Transcript AspisR136BeforeOod.Error

def claimsSlice (v : Values) : Slice U8 :=
  ⟨packed (v.val.take 358), by
    rw [packed_length, List.length_take]
    have := Usize.cMax_bound
    scalar_tac⟩

def claimsBytes (v : Values) : Result (Slice U8) :=
  if 358 ≤ v.val.length then .ok (claimsSlice v) else .fail .panic

theorem claims_exact (v : Values) :
    (do
      let s ← alloc.vec.Vec.index
        (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.QM31)
        v { «end» := 358#usize }
      let b ← bytes s
      ok (alloc.vec.Vec.deref b)) = claimsBytes v := by
  by_cases h : 358 ≤ v.val.length
  · simp only [alloc.vec.Vec.index, alloc.vec.Vec.deref,
      core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice,
      core.slice.index.SliceIndexRangeToUsizeSlice.index, Slice.length,
      show (358#usize : Usize).val = 358 from rfl, h, if_true, bind_tc_ok]
    have hlen : (v.val.slice 0 358).length = 358 := by
      simp [List.slice, List.length_take, Nat.min_eq_left h]
    rw [bytes_execution _ (by
      change 16 * (v.val.slice 0 358).length ≤ Usize.max
      rw [hlen]; have := Usize.cMax_bound; scalar_tac)]
    simp only [bind_tc_ok, claimsBytes, h, if_true, claimsSlice,
      encoded, alloc.vec.Vec.deref, List.slice, List.drop_zero]
  · simp [alloc.vec.Vec.index, alloc.vec.Vec.deref,
      core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice,
      core.slice.index.SliceIndexRangeToUsizeSlice.index, Slice.length,
      h, claimsBytes]

def profileData : Slice U8 := Array.to_slice (Array.make 24#usize [
  65#u8, 86#u8, 56#u8, 47#u8, 114#u8, 101#u8, 108#u8, 97#u8,
  116#u8, 105#u8, 111#u8, 110#u8, 45#u8, 99#u8, 97#u8, 108#u8,
  108#u8, 98#u8, 97#u8, 99#u8, 107#u8, 47#u8, 118#u8, 49#u8])

def sourceChronology (w : Wire) (statement : Array U8 32#usize)
    (hashfn : Slice (Slice U8) → Result (Array U8 32#usize)) : Result Outcome := do
  let t ← aspis_core.transcript.Transcript.new hashfn
  let t1 ← aspis_core.transcript.Transcript.absorb t
    AspisR137Transcript.transcript.label.PROFILE profileData
  let t2 ← aspis_core.transcript.Transcript.absorb t1
    AspisR137Transcript.transcript.label.STATEMENT (Array.to_slice statement)
  let t3 ← aspis_core.transcript.Transcript.absorb t2
    AspisR137Transcript.transcript.label.ROOT (Array.to_slice w.roots.1)
  let (lambda, t4) ← sample t3 false
  match lambda with
  | .Err e => ok (.Err e)
  | .Ok _ =>
    let (chi, t5) ← sample t4 false
    match chi with
    | .Err e => ok (.Err e)
    | .Ok _ =>
      let t6 ← aspis_core.transcript.Transcript.absorb t5
        AspisR137Transcript.transcript.label.SECOND_PHASE_ROOT (Array.to_slice w.roots.2)
      let claims ← claimsBytes w.v
      let t7 ← aspis_core.transcript.Transcript.absorb t6
        AspisR137Transcript.transcript.label.V6_POINT_CLAIMS claims
      ok (.Ok t7)

theorem claims_continuation (v : Values) (next : Slice U8 → Result Outcome) :
    (do
      let s ← alloc.vec.Vec.index
        (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.QM31)
        v { «end» := 358#usize }
      let b ← bytes s
      next (alloc.vec.Vec.deref b)) = (do
      let s ← claimsBytes v
      next s) := by
  rw [← claims_exact]
  simp only [bind_assoc_eq, bind_tc_ok]

theorem source_chronology_exact (w : Wire) (statement : Array U8 32#usize)
    (hashfn : Slice (Slice U8) → Result (Array U8 32#usize)) :
    before_ood w statement hashfn = sourceChronology w statement hashfn := by
  simp only [before_ood, sourceChronology, profileData, lift, bind_tc_ok,
    aspis_core.transcript.label.PROFILE, aspis_core.transcript.label.STATEMENT,
    aspis_core.transcript.label.ROOT, aspis_core.transcript.label.SECOND_PHASE_ROOT,
    aspis_core.transcript.label.V6_POINT_CLAIMS]
  simp only [bind_eq_iff]
  intro t ht t1 ht1 t2 ht2 t3 ht3 r hr
  rcases r with ⟨lambda, t4⟩
  dsimp only
  cases lambda with
  | Err e => rfl
  | Ok q =>
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    intro chi t5 hchi
    cases chi with
    | Err e => rfl
    | Ok q1 =>
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      intro t6 ht6
      exact claims_continuation w.v (fun claims => do
        let t7 ← aspis_core.transcript.Transcript.absorb t6
          AspisR137Transcript.transcript.label.V6_POINT_CLAIMS claims
        ok (.Ok t7))

open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.R137TranscriptPrimitiveBridge
open AspisV8R19.R140BeforeOodSampleBridge

def absorbState (H : Bytes → State) (s : State) (label : U8)
    (data : Slice U8) : State :=
  H (DuplexFrames.absorb (SourceDuplexStep.bytes s)
    (SqueezeOracleBridge.decodeByte label) (decodedSlice data))

def ordinaryResult (H : Bytes → State) (s : State) :=
  mapInner (R137SamplerChallengeBridge.encodeResult
    (QM31SamplerProgram.challengeRun H s).2.1)

def modelChronology (H : Bytes → State) (w : Wire)
    (statement : Array U8 32#usize) : Result Outcome :=
  let s1 := absorbState H zeroState AspisR137Transcript.transcript.label.PROFILE profileData
  let s2 := absorbState H s1 AspisR137Transcript.transcript.label.STATEMENT statement.to_slice
  let s3 := absorbState H s2 AspisR137Transcript.transcript.label.ROOT w.roots.1.to_slice
  let s4 := (QM31SamplerProgram.challengeRun H s3).2.2
  match ordinaryResult H s3 with
  | .Err e => .ok (.Err e)
  | .Ok _ =>
    let s5 := (QM31SamplerProgram.challengeRun H s4).2.2
    match ordinaryResult H s4 with
    | .Err e => .ok (.Err e)
    | .Ok _ => do
      let claims ← claimsBytes w.v
      let s6 := absorbState H s5 AspisR137Transcript.transcript.label.SECOND_PHASE_ROOT
        w.roots.2.to_slice
      let s7 := absorbState H s6 AspisR137Transcript.transcript.label.V6_POINT_CLAIMS claims
      .ok (.Ok (transcriptFor H s7))

theorem model_chronology_exact (H : Bytes → State) (w : Wire)
    (statement : Array U8 32#usize) :
    sourceChronology w statement (SqueezeOracleBridge.hashAdapter H) =
      modelChronology H w statement := by
  simp [sourceChronology, R141BeforeOodPrimitiveBridge.new_exact,
    R141BeforeOodPrimitiveBridge.absorb_exact, sample_false_exact,
    sampleModelFalse, modelChronology, absorbState, ordinaryResult]

theorem before_ood_model_exact (H : Bytes → State) (w : Wire)
    (statement : Array U8 32#usize) :
    before_ood w statement (SqueezeOracleBridge.hashAdapter H) =
      modelChronology H w statement := by
  rw [source_chronology_exact, model_chronology_exact]

#print axioms claims_exact
#print axioms source_chronology_exact
#print axioms model_chronology_exact
#print axioms before_ood_model_exact
end AspisV8R19.R146BeforeOodBridge
