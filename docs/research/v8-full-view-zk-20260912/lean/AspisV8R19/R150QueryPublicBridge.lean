import AspisV8R19.R143QueryEntryBridge
import AspisV8R19.R149QueryLoopBridge
import AspisV8R19.R137SamplerLimbBridge

set_option autoImplicit false
/-! Exact actual R137 q22 result and returned transcript under an explicit total
byte oracle. The model is encoded back into the source result without dropping
error tags or counters. Arbitrary argument guard errors are proved separately;
shared-oracle trace equality and challenge probabilities remain separate. -/
namespace AspisV8R19.R150QueryPublicBridge
open Aeneas Aeneas.Std Result
open AspisV8R19
open DuplexFrames SourceDuplexStep SqueezeOracleBridge
open QueryChunkModel
open R143QueryEntryBridge
abbrev Values := R143QueryEntryBridge.Values
abbrev queryTranscript := R149QueryLoopBridge.queryTranscript

def encodeValues (xs : List Nat) : Result Values :=
  if h : xs.length ≤ Usize.max then
    .ok ⟨xs.map R137SamplerLimbBridge.encodeWord, by simpa using h⟩
  else .fail .panic

def encodeModelResult : Except Nat (List Nat) →
    Result (core.result.Result Values AspisR137Q22.transcript.QuerySampleError)
  | .ok xs => do let out ← encodeValues xs; .ok (.Ok out)
  | .error n =>
    if h : n ≤ Usize.max then
      .ok (.Err (.DrawLimitExhausted
        (UScalar.ofNatCore n (by scalar_tac)) 64#usize))
    else .fail .panic

theorem word_roundtrip (x : U32) : R137SamplerLimbBridge.encodeWord x.val = x := by
  apply UScalar.eq_of_val_eq
  change x.val % 4294967296 = x.val
  apply Nat.mod_eq_of_lt
  exact x.hBounds

theorem values_roundtrip (out : Values) :
    encodeValues (out.val.map UScalar.val) = .ok out := by
  have h : (out.val.map UScalar.val).length ≤ Usize.max := by
    simpa using out.property
  simp only [encodeValues, dif_pos h, List.map_map]
  apply congrArg Result.ok
  apply Subtype.ext
  simp only [Function.comp_def,word_roundtrip]
  exact congrFun List.map_id_fun out.val

theorem encode_finish (out : Values) :
    encodeModelResult (Q22WordScan.finish (view out 0#usize)) = .ok (finishSource out) := by
  by_cases h : alloc.vec.Vec.len out = 22#usize
  · have hv : out.val.length = 22 := congrArg UScalar.val h
    simp only [Q22WordScan.finish,view,List.length_map,hv,↓reduceIte,
      encodeModelResult,values_roundtrip,bind_tc_ok,finishSource,if_pos h]
  · have hv : out.val.length ≠ 22 := by
      intro he;apply h;apply UScalar.eq_of_val_eq;exact he
    simp only [Q22WordScan.finish,view,List.length_map,if_neg hv,
      encodeModelResult,finishSource,if_neg h]
    rw [dif_pos out.property]
    congr 3

theorem public_result (H : Bytes → State) (s : State) :
    ∃ out : Values,
      AspisR137Q22.r137_query_probe (queryTranscript H s) =
        .ok (finishSource out,queryTranscript H (Q22SamplerProgram.challengeRun H s).2.2) ∧
      Q22WordScan.finish (view out 0#usize) = (Q22SamplerProgram.challengeRun H s).2.1 ∧
      out.val.length ≤ 22 := by
  obtain ⟨out,he,hf,hc⟩ := R149QueryLoopBridge.source_loop H 8 s
    (alloc.vec.Vec.with_capacity U32 22#usize) 0#usize (by decide) (by decide) (by decide)
  refine ⟨out,?_,hf,hc⟩
  rw [selected_entry,he]
  rfl

theorem public_exact (H : Bytes → State) (s : State) :
    AspisR137Q22.r137_query_probe (queryTranscript H s) = (do
      let r ← encodeModelResult (Q22SamplerProgram.challengeRun H s).2.1
      .ok (r,queryTranscript H (Q22SamplerProgram.challengeRun H s).2.2)) := by
  obtain ⟨out,he,hf,hc⟩ := public_result H s
  rw [← hf,encode_finish,bind_tc_ok]
  exact he

theorem zero_bound (self : AspisR137Q22.transcript.Transcript)
    (count maxDraws : Usize) :
    self.challenge_queries_without_replacement count 0#u32 maxDraws =
      .ok (.Err (.BoundNotPowerOfTwo 0#u32),self) := by
  simp [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement]

theorem nonpower_bound (self : AspisR137Q22.transcript.Transcript)
    (count maxDraws : Usize) (bound : U32) (hn : bound ≠ 0#u32)
    (hb : (bound &&& Std.U32.wrapping_sub bound 1#u32) ≠ 0#u32) :
    self.challenge_queries_without_replacement count bound maxDraws =
      .ok (.Err (.BoundNotPowerOfTwo bound),self) := by
  simp only [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement,
    if_neg hn,lift,bind_tc_ok]
  simp only [bne_iff_ne]
  rw [if_pos hb]

theorem count_exceeds (self : AspisR137Q22.transcript.Transcript)
    (count maxDraws : Usize) (bound : U32) (hn : bound ≠ 0#u32)
    (hb : (bound &&& Std.U32.wrapping_sub bound 1#u32) = 0#u32)
    (hc : count > UScalar.cast .Usize bound) :
    self.challenge_queries_without_replacement count bound maxDraws =
      .ok (.Err (.CountExceedsBound count bound),self) := by
  simp only [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement,
    if_neg hn,lift,bind_tc_ok,hb,
    show (0#u32 != 0#u32) = false from rfl, Bool.false_eq_true,if_false,if_pos hc]


#print axioms word_roundtrip
#print axioms values_roundtrip
#print axioms encode_finish
#print axioms public_result
#print axioms public_exact
#print axioms zero_bound
#print axioms nonpower_bound
#print axioms count_exceeds
end AspisV8R19.R150QueryPublicBridge
