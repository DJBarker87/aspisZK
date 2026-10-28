import NBA_QueryWords
import NBA_QueryConstruct
import NBA_QueryDriver
set_option autoImplicit false
namespace AspisR1.NBA_QueryNative
open Aeneas Aeneas.Std Result
open Query31ExplicitListLoop Query31ExplicitScanBody
abbrev State := NBA_QueryTrace.State
abbrev Bytes32 := NBA_QueryDriver.Bytes32

/-- The byte callback and locally framed scanner transitions use the same
block, word array and mutable state. -/
theorem source (block : Bytes32) (words : Array U32 8#usize)
    (s final : State) (pending : Option Bool)
    (decode : Query31ConcreteWordsDriverChain.actualQueryWords block=ok words)
    (trace : NBA_QueryTrace.Trace words.val s final pending) :
    Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s block=
      ok (optionStop pending,final) := by
  unfold Query31ModelScanCall.modelScanFn
  rw [decode,bind_tc_ok,NBA_QueryTrace.source trace,bind_tc_ok]

/-- The local native relation is inhabited for every bounded input state.
No successful scanner Result is supplied as a premise. -/
theorem construct (block : Bytes32) (s : State) (valid : validState s) :
    ∃ words final pending,
      Query31ConcreteWordsDriverChain.actualQueryWords block=ok words ∧
      NBA_QueryTrace.Trace words.val s final pending ∧ validState final ∧
      Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s block=
        ok (optionStop pending,final) := by
  obtain ⟨words,decode,meaning⟩ := NBA_QueryWords.source block
  obtain ⟨final,pending,trace,good⟩ := NBA_QueryConstruct.construct words.val s valid
  exact ⟨words,final,pending,decode,trace,good,source block words s final pending decode trace⟩

#print axioms source
#print axioms construct
end AspisR1.NBA_QueryNative
