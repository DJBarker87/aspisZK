import GSRejectingSamplerDecoderBank
import M31PairedSamplerMass
import M31PairedSamplerRejectBound

set_option autoImplicit false
namespace AspisR1.GSConcreteByteDecoderBank
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.GSRejectingSamplerDecoderBank
open AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open M31RetryOutputFiber M31AcceptFiber

abbrev K := WideExactOutput
abbrev RawCoins := ActualWidePairInputTape 21377328

variable [BEq K] [LawfulBEq K] [DecidableEq K]

/-- Actual finite-word sampler, exact tape reindexing and maintained 29+5
GS interpolation/root decoders. No abstract random-field oracle is supplied. -/
def run (inputs : Inputs K 5) (xs : RawCoins) : Option (Results K 5) :=
  sampleAndRun (actualWidePairSamplerTape 21377328) (P31^8) inputs xs

def failed (inputs : Inputs K 5) (xs : RawCoins) : Prop :=
  GSRejectingSamplerDecoderBank.failed
    (actualWidePairSamplerTape 21377328) (P31^8) inputs xs

noncomputable section

theorem field_card : P31^8 = Fintype.card K := by
  rw [AspisWideTower.wideExact_card]
  norm_num [P31, AspisV8R15.ExactTowerBase.P]

theorem field_odd : ringChar K ≠ 2 := by
  intro h
  have hz : (ringChar K : K) = 0 := CharP.cast_eq_zero K (ringChar K)
  rw [h] at hz
  exact AspisWideTower.wideExact_two_ne_zero hz

/-- All input arrays are fixed before the uniform finite-word coins. The
complete coin-sampler plus bank failure is below2^-126, including rejection. -/
theorem failure_small (inputs : Inputs K 5) :
    mean (fun xs : RawCoins => indicator (failed inputs xs)) < (1/2 : ℚ)^126 := by
  apply GSRejectingSamplerDecoderBank.failure_small
    (actualWidePairSamplerTape 21377328) (P31^8) inputs field_card field_odd
  · simpa only [actualPairedTapeSampler] using
      actualPairedTape_output_mass_le_uniform 21377328
  · exact actualWidePairSamplerTape_reject_concrete

#print axioms run
#print axioms field_card
#print axioms field_odd
#print axioms failure_small
end
end AspisR1.GSConcreteByteDecoderBank
