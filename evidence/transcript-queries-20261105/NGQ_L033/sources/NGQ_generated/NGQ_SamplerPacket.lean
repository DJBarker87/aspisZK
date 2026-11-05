import NGQ_SamplerNative
import NGQ_Embed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGQ_SamplerPacket
open Aeneas Aeneas.Std Result
open Query31ExplicitListLoop Query31ExplicitScanBody
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks := Array Bytes32 8#usize
abbrev State := AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan
abbrev Scan := Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
abbrev initial := Query31ConcreteDriverTraceFacts.sourceDefaultState
abbrev NativeOut := NGQ_SamplerDriver.Out

def errorPort : AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError →
    AspisR1PublicPreparation.aspis_core.transcript.QuerySampleError
 | .BoundNotPowerOfTwo bound => .BoundNotPowerOfTwo bound
 | .CountExceedsBound count bound => .CountExceedsBound count bound
 | .DrawLimitExhausted accepted maxDraws => .DrawLimitExhausted accepted maxDraws

def decode (blocks advances : Blocks) : Result (core.result.Result
    (Array U32 22#usize × Bytes32) AspisR1PublicPreparation.aspis_core.transcript.QuerySampleError) := do
 let out ← AspisR1Query31Transcript.queries_from_pairs_with_scan Scan initial blocks advances
 match out with
 | .Ok value => ok (.Ok value)
 | .Err error => ok (.Err (errorPort error))

theorem initial_valid : validState initial :=
 Query31ConcreteDriverTraceFacts.sourceDefaultState_valid

/-- Full finish value/error, not a success premise. -/
theorem finish_total (s : State) (advances : Blocks) (i : Usize) (hi : i.val<8) :
    ∃ out, AspisR1Query31Transcript.finishAdvance advances i s=ok out := by
  have read := NGQ_SamplerArray8.read advances i hi
  by_cases full : s.accepted_len=22#usize
  · refine ⟨.Ok (s.accepted, _),?_⟩
    simp only [AspisR1Query31Transcript.finishAdvance,
      AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish,
      AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT,full,if_true,
      core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,read]
  · refine ⟨.Err (.DrawLimitExhausted s.accepted_len 64#usize),?_⟩
    simp only [AspisR1Query31Transcript.finishAdvance,
      AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish,
      AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT,
      AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_MAX_DRAWS,full,if_false,
      core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
    rfl

theorem walk_total (advances : Blocks) (fallback : Usize) (hf : fallback.val<8) :
    ∀ (inputs : List (Bytes32 × Usize)), (∀ p∈inputs,p.2.val<8) →
      ∀ (s : State), validState s →
        ∃ out, NGQ_SamplerDriver.walk Scan advances fallback inputs s=ok out := by
  intro inputs
  induction inputs with
  | nil =>
    intro _ s good
    exact finish_total s advances fallback hf
  | cons head tail ih =>
    intro indices s good
    obtain ⟨words,sf,pending,decoded,trace,validFinal,call⟩ := NGQ_SamplerNative.construct head.1 s good
    have headBound : head.2.val<8 := indices head (List.mem_cons_self ..)
    have tailBound : ∀ p∈tail,p.2.val<8 := fun p hp => indices p (List.mem_cons_of_mem head hp)
    cases flag : optionStop pending with
    | false =>
      obtain ⟨out,next⟩ := ih tailBound sf validFinal
      refine ⟨out,?_⟩
      simpa only [NGQ_SamplerDriver.walk,Scan,call,flag,bind_tc_ok,Bool.false_eq_true,if_false] using next
    | true =>
      obtain ⟨out,next⟩ := finish_total sf advances head.2 headBound
      refine ⟨out,?_⟩
      simpa only [NGQ_SamplerDriver.walk,Scan,call,flag,bind_tc_ok,if_true] using next

theorem zip_bound (xs : List Bytes32) :
    ∀ (indices : List Usize), (∀ i∈indices,i.val<8) →
      ∀ p∈xs.zip indices,p.2.val<8 := by
  induction xs with
  | nil => intro indices good p hp; cases hp
  | cons x xs ih =>
    intro indices good p hp
    cases indices with
    | nil => cases hp
    | cons i is =>
      simp only [List.zip_cons_cons,List.mem_cons] at hp
      rcases hp with eq | rest
      · subst p; exact good i (List.mem_cons_self ..)
      · exact ih is (fun j hj => good j (List.mem_cons_of_mem i hj)) p rest

theorem total (blocks advances : Blocks) : ∃ out, decode blocks advances=ok out := by
  have indices : ∀ i ∈ [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize], i.val<8 := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h <;> subst i <;> decide
  obtain ⟨out,call⟩ := walk_total advances 7#usize (by decide) _
    (zip_bound blocks.val _ indices) initial initial_valid
  have source := NGQ_SamplerDriver.source Scan initial blocks advances
  rw [← source] at call
  cases out with
  | Ok value => exact ⟨.Ok value,by simp only [decode,call,bind_tc_ok]⟩
  | Err error => exact ⟨.Err (errorPort error),by simp only [decode,call,bind_tc_ok]⟩

#print axioms initial_valid
#print axioms finish_total
#print axioms walk_total
#print axioms zip_bound
#print axioms total
end AspisR1.NGQ_SamplerPacket
end
