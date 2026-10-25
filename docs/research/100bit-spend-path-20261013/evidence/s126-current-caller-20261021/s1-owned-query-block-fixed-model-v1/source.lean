import S1OwnedQueryBlockModelV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Meaning
open Aeneas Aeneas.Std Result
open Query31ExplicitScanBody
open AspisV8R19.SqueezeOracleBridge

/-- Literal same-byte LE/mask word order, reusing the existing checked decoder
arithmetic. No source word value or independent successful decode is assumed. -/
theorem wordValuesFrom_zero_math (block : Array U8 32#usize) :
    wordValuesFrom block 0=AspisV8R19.SamplerWords.words 18 (decodeState block) := by
  unfold wordValuesFrom AspisV8R19.SamplerWords.words
  rw [List.drop_zero]
  apply congrArg (fun f : Fin 8 → Nat => List.ofFn f)
  funext j
  exact AspisS1QueryWordModel.masked_word_value block j

/-- TOTAL full extracted owned block to the fixed mathematical sampler,
including early stop and the entire same returned state. -/
theorem block_fixed_model (s : CurrentScan) (block : Array U8 32#usize)
    (hlen : s.accepted_len.val≤22) (hd : s.draws.val≤64) :
    ∃ (sf : CurrentScan) (stop : Bool),
      owned_block s.accepted s.accepted_len s.draws block=ok (pack sf stop) ∧
      AspisV8R19.Q22WordScan.scan (q22StateOf s)
        (AspisV8R19.SamplerWords.words 18 (decodeState block))=(q22StateOf sf,stop) ∧
      Query31ExplicitListLoop.validState sf := by
  obtain ⟨sf,stop,call,model,valid⟩ := block_model s block hlen hd
  rw [wordValuesFrom_zero_math] at model
  exact ⟨sf,stop,call,model,valid⟩

#print axioms wordValuesFrom_zero_math
#print axioms block_fixed_model
end AspisS1OwnedQueryBlock.Meaning
