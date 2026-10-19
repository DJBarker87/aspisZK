import GSFixedInputDecoderFamily
import FiniteOptionSamplerComposition
import GSDecoderTapeReindex

set_option autoImplicit false
namespace AspisR1.GSRejectingSamplerDecoderBank
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.GSDecoderTapeReindex
open AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound

abbrev Positions := Fin ((1025*112 + 256*112)*149)
abbrev FlatTape (K : Type) := Positions → K × K

variable {X K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

/-- The byte sampler is a total rejecting function. A successful sample is
reindexed without further randomness, then runs the actual 29+5 decoder bank. -/
def sampleAndRun (sample : X → Option (FlatTape K)) (q : Nat)
    (inputs : Inputs K 5) (x : X) : Option (Results K 5) :=
  (sample x).map (fun H => run q 149 inputs (flatBank K (1025*112) (256*112) 149 H))

/-- Failure includes byte-sampler rejection and any actual bank call returning
none. This predicate is exactly the observed failure of sampleAndRun. -/
def failed (sample : X → Option (FlatTape K)) (q : Nat)
    (inputs : Inputs K 5) (x : X) : Prop :=
  AspisR1.FiniteOptionSamplerComposition.fails sample
    (fun H => GSFixedInputDecoderFamily.failed
      (run q 149 inputs (flatBank K (1025*112) (256*112) 149 H))) x

/-- The event used in the probability theorem is the actual output failure,
including rejection before the decoder bank is entered. -/
theorem failed_iff_output (sample : X → Option (FlatTape K)) (q : Nat)
    (inputs : Inputs K 5) (x : X) :
    failed sample q inputs x ↔ sampleAndRun sample q inputs x = none ∨
      ∃ out, sampleAndRun sample q inputs x = some out ∧
        GSFixedInputDecoderFamily.failed out := by
  cases hs : sample x <;>
    simp [failed, AspisR1.FiniteOptionSamplerComposition.fails, sampleAndRun, hs]

noncomputable section
variable [Fintype K] [Fintype X] [Nonempty X]

/-- A conditional adapter: the actual finite-byte sampler still must supply
its output-mass and rejection bounds. The decoder and reindexing are concrete. -/
theorem failure_small (sample : X → Option (FlatTape K)) (q : Nat)
    (inputs : Inputs K 5) (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2)
    (hmass : ∀ H, mean (fun x => indicator (sample x = some H)) ≤
      1 / (Fintype.card (FlatTape K) : ℚ))
    (hreject : mean (fun x => indicator (sample x = none)) ≤ (1/2 : ℚ)^467) :
    mean (fun x => indicator (failed sample q inputs x)) < (1/2 : ℚ)^126 := by
  have hb := abort_small_five q inputs hq hodd
  have hf : mean (fun H : FlatTape K => indicator
      (GSFixedInputDecoderFamily.failed
        (run q 149 inputs (flatBank K (1025*112) (256*112) 149 H)))) <
      (1/2 : ℚ)^127 := by
    have he := mean_flatBank (K := K) (1025*112) (256*112) 149
      (fun H => indicator (GSFixedInputDecoderFamily.failed (run q 149 inputs H)))
    exact he.trans_lt hb
  have hc := AspisR1.FiniteOptionSamplerComposition.failure_le_rejection_add_uniform
    sample (fun H => GSFixedInputDecoderFamily.failed
      (run q 149 inputs (flatBank K (1025*112) (256*112) 149 H))) hmass
  change mean (fun x => indicator (failed sample q inputs x)) ≤ _ at hc
  calc
    _ ≤ _ := hc
    _ ≤ (1/2 : ℚ)^467 + (1/2 : ℚ)^127 := add_le_add hreject (le_of_lt hf)
    _ < (1/2 : ℚ)^126 := by
      have hp : (1/2 : ℚ)^467 ≤ (1/2 : ℚ)^128 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
      calc
        _ ≤ (1/2 : ℚ)^128 + (1/2 : ℚ)^127 := add_le_add hp le_rfl
        _ < _ := by norm_num

#print axioms sampleAndRun
#print axioms failed_iff_output
#print axioms failure_small
end
end AspisR1.GSRejectingSamplerDecoderBank
