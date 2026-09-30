import AspisV8R19.R153ScheduleBytesBridge
import AspisV8R19.R146BeforeOodBridge
import AspisV8R19.R150QueryPublicBridge

set_option autoImplicit false
/-! Exact selected query_schedule chronology and outcome/state, with the
actual q22 and three-attempt nonzero sampler adapters. Raw outer failure and
divergence and callback error-state updates are retained. This is not yet an
observed shared-oracle trace or a complete security theorem. -/
namespace AspisV8R19.R154QueryScheduleBridge
open Aeneas Aeneas.Std Result
open AspisV8R19 AspisR151QuerySchedule
abbrev Outcome := core.result.Result (alloc.vec.Vec U32 × aspis_core.field.QM31) AspisR136BeforeOod.Error

def profileData : Slice U8 := Array.to_slice (Array.make 18#usize [
  65#u8,86#u8,56#u8,47#u8,113#u8,117#u8,101#u8,114#u8,121#u8,
  45#u8,98#u8,97#u8,116#u8,99#u8,104#u8,47#u8,118#u8,49#u8])

def nonceRange (nonces : Slice U8) : Result (Slice U8) :=
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    nonces {start:=16#usize,«end»:=24#usize}

def mapQueryResult (r : core.result.Result (alloc.vec.Vec U32) aspis_core.transcript.QuerySampleError) :
    core.result.Result (alloc.vec.Vec U32) AspisR136BeforeOod.Error :=
  match r with
  | .Ok q => .Ok q
  | .Err _ => .Err .Sampler

theorem map_query_exact (r : core.result.Result (alloc.vec.Vec U32) aspis_core.transcript.QuerySampleError) :
    AspisR151QuerySchedule.core.result.Result.map_err
      query_schedule.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError r () =
      .ok (mapQueryResult r) := by
  cases r <;> rfl

theorem sample_same (t : aspis_core.transcript.Transcript) (nz : Bool) :
    AspisR151QuerySchedule.sample t nz = AspisR136BeforeOod.sample t nz := by rfl

def sourceChronology (p : Prefix) (finals : Slice aspis_core.field.QM31) (nonces : Slice U8) :
    Result (Outcome × Prefix) := do
  let v ← AspisR151QuerySchedule.bytes finals
  let t1 ← aspis_core.transcript.Transcript.absorb p.t 53#u8 (alloc.vec.Vec.deref v)
  let nonce ← nonceRange nonces
  let t2 ← aspis_core.transcript.Transcript.absorb t1 5#u8 nonce
  let (r,t3) ← aspis_core.transcript.Transcript.challenge_queries_without_replacement t2
    22#usize 262144#u32 64#usize
  match mapQueryResult r with
  | .Err e => .ok (.Err e,{p with t:=t3})
  | .Ok q =>
    let t4 ← aspis_core.transcript.Transcript.absorb t3
      AspisR137Transcript.transcript.label.PROFILE profileData
    let (r1,t5) ← AspisR136BeforeOod.sample t4 true
    match r1 with
    | .Err e => .ok (.Err e,{p with t:=t5})
    | .Ok rho => .ok (.Ok (q,rho),{p with t:=t5})

theorem source_chronology_exact (p : Prefix) (finals : Slice aspis_core.field.QM31)
    (nonces : Slice U8) : query_schedule p finals nonces = sourceChronology p finals nonces := by
  simp only [query_schedule,sourceChronology,nonceRange,profileData,
    aspis_core.transcript.label.V6_FINAL256,aspis_core.transcript.label.GRIND_NONCE,
    aspis_core.transcript.label.PROFILE,lift,bind_tc_ok,R143QueryEntryBridge.wrapping_bound,
    map_query_exact,sample_same]
  simp only [bind_eq_iff]
  intro v hv t1 ht1 nonce hn t2 ht2 r hr
  rcases r with ⟨qr,t3⟩
  cases qr with
  | Err e => rfl
  | Ok q =>
    simp [mapQueryResult,core.result.Result.Insts.CoreOpsTry.branch]
    intro t4 ht4 r1 t5 hs
    cases r1 <;> rfl

open DuplexFrames SourceDuplexStep R137TranscriptPrimitiveBridge

def queryModel (H : Bytes → State) (s : State) := do
  let r ← R150QueryPublicBridge.encodeModelResult (Q22SamplerProgram.challengeRun H s).2.1
  .ok (r,transcriptFor H (Q22SamplerProgram.challengeRun H s).2.2)

theorem query_model_exact (H : Bytes → State) (s : State) :
    aspis_core.transcript.Transcript.challenge_queries_without_replacement
      (transcriptFor H s) 22#usize 262144#u32 64#usize = queryModel H s := by
  unfold aspis_core.transcript.Transcript.challenge_queries_without_replacement
  change (do
    let (r,next) ← AspisR137Q22.r137_query_probe (R149QueryLoopBridge.queryTranscript H s)
    .ok (r,fromQueryTranscript next)) = _
  rw [R150QueryPublicBridge.public_exact]
  simp only [queryModel,bind_assoc_eq,bind_tc_ok]
  rfl

def finalBytes (finals : Slice aspis_core.field.QM31)
    (hsize : 16 * finals.val.length ≤ Usize.max) : Slice U8 :=
  alloc.vec.Vec.deref (R144BeforeOodBytesBridge.encoded finals hsize)

def modelChronology (H : Bytes → State) (p : Prefix) (s : State)
    (finals : Slice aspis_core.field.QM31) (hsize : 16 * finals.val.length ≤ Usize.max)
    (nonces : Slice U8) : Result (Outcome × Prefix) := do
  let s1 := R146BeforeOodBridge.absorbState H s 53#u8 (finalBytes finals hsize)
  let nonce ← nonceRange nonces
  let s2 := R146BeforeOodBridge.absorbState H s1 5#u8 nonce
  let qrun := Q22SamplerProgram.challengeRun H s2
  let r ← R150QueryPublicBridge.encodeModelResult qrun.2.1
  let t3 := transcriptFor H qrun.2.2
  match mapQueryResult r with
  | .Err e => .ok (.Err e,{p with t:=t3})
  | .Ok q =>
    let s4 := R146BeforeOodBridge.absorbState H qrun.2.2
      AspisR137Transcript.transcript.label.PROFILE profileData
    let (r1,t5) ← R140BeforeOodSampleBridge.sampleModelTrue H s4
    match r1 with
    | .Err e => .ok (.Err e,{p with t:=t5})
    | .Ok rho => .ok (.Ok (q,rho),{p with t:=t5})

theorem schedule_model_exact (H : Bytes → State) (p : Prefix) (s : State)
    (finals : Slice aspis_core.field.QM31) (hsize : 16 * finals.val.length ≤ Usize.max)
    (nonces : Slice U8) :
    query_schedule {p with t:=transcriptFor H s} finals nonces =
      modelChronology H p s finals hsize nonces := by
  rw [source_chronology_exact]
  simp [sourceChronology,modelChronology,R153ScheduleBytesBridge.bytes_execution _ hsize,
    finalBytes,R141BeforeOodPrimitiveBridge.absorb_exact,R146BeforeOodBridge.absorbState,
    query_model_exact,queryModel,R140BeforeOodSampleBridge.sample_true_exact]


#print axioms map_query_exact
#print axioms sample_same
#print axioms source_chronology_exact
#print axioms query_model_exact
#print axioms schedule_model_exact
#print axioms AspisR151QuerySchedule.query_schedule
#print axioms AspisR151QuerySchedule.bytes
#print axioms AspisR151QuerySchedule.sample
end AspisV8R19.R154QueryScheduleBridge
