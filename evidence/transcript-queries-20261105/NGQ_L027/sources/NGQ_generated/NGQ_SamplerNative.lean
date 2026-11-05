import NGQ_SamplerWords
import NGQ_SamplerConstruct
import NGQ_SamplerDriver
set_option autoImplicit false
namespace AspisR1.NGQ_SamplerNative
open Aeneas Aeneas.Std Result
open Query31ExplicitListLoop Query31ExplicitScanBody
abbrev State := NGQ_SamplerTrace.State
abbrev Bytes32 := NGQ_SamplerDriver.Bytes32

/-- The byte callback and locally framed scanner transitions use the same
block, word array and mutable state. -/
theorem source (block : Bytes32) (words : Array U32 8#usize)
    (s final : State) (pending : Option Bool)
    (decode : Query31ConcreteWordsDriverChain.actualQueryWords block=ok words)
    (trace : NGQ_SamplerTrace.Trace words.val s final pending) :
    Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s block=
      ok (optionStop pending,final) := by
  unfold Query31ModelScanCall.modelScanFn
  rw [decode,bind_tc_ok,NGQ_SamplerTrace.source trace,bind_tc_ok]
  rfl

/-- The local native relation is inhabited for every bounded input state.
No successful scanner Result is supplied as a premise. -/
theorem construct (block : Bytes32) (s : State) (valid : validState s) :
    ∃ words final pending,
      Query31ConcreteWordsDriverChain.actualQueryWords block=ok words ∧
      NGQ_SamplerTrace.Trace words.val s final pending ∧ validState final ∧
      Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s block=
        ok (optionStop pending,final) := by
  obtain ⟨words,decode,meaning⟩ := NGQ_SamplerWords.source block
  obtain ⟨final,pending,trace,good⟩ := NGQ_SamplerConstruct.construct words.val s valid
  exact ⟨words,final,pending,decode,trace,good,source block words s final pending decode trace⟩

#print axioms source
#print axioms construct
end AspisR1.NGQ_SamplerNative
