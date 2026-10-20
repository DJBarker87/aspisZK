import GSActualBankJobsM10
import GSByteSamplerWorkM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.GSActualByteJobsM10
open CompPoly AspisWideTower GSFixedInputDecoderFamily GSDecoderTapeReindex
open GSScalarCallScheduleM10 GSScalarOperandEnvelopeM10 RawExtractorCostLedger
open M31AcceptFiber M31RetryOutputFiber
attribute [local irreducible] RRRecoveryJobsM10.select GSActualBankJobsM10.calls
  GSActualBankJobsM10.count GSByteSamplerWorkM10.sample

def calls (inputs : Inputs WideExact 5) (coins : GSConcreteByteDecoderBank.RawCoins) : List (Call WideExact) :=
  RRRecoveryJobsM10.select (GSByteSamplerWorkM10.sample 21377328 coins).1
    (fun H _ => GSActualBankJobsM10.calls (P31^8) 149 inputs
      (flatBank WideExact (1025*112) (256*112) 149 H))

theorem length (inputs : Inputs WideExact 5) (coins : GSConcreteByteDecoderBank.RawCoins) :
    (calls inputs coins).length ≤ GSActualBankJobsM10.count 149 := by
  unfold calls
  apply RRRecoveryJobsM10.select_property _ _ (fun cs => cs.length ≤ GSActualBankJobsM10.count 149)
  · exact Nat.zero_le _
  · intro H _
    exact GSActualBankJobsM10.calls_length (P31^8) 149 inputs GSConcreteByteDecoderBank.field_card _

theorem bounded (inputs : Inputs WideExact 5) (coins : GSConcreteByteDecoderBank.RawCoins) :
    ∀ c ∈ calls inputs coins, Bounded 112 (P31^8) c := by
  unfold calls
  apply RRRecoveryJobsM10.select_property _ _ (fun cs => ∀ c ∈ cs, Bounded 112 (P31^8) c)
  · simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  · intro H _
    exact GSActualBankJobsM10.calls_bounded (P31^8) 149 inputs _

def jobs (inputs : Inputs WideExact 5) (coins : GSConcreteByteDecoderBank.RawCoins) : Jobs WideExact :=
  GSScalarJobsM10.ofCalls 112 (P31^8) (calls inputs coins) (bounded inputs coins)

theorem jobs_bounded (inputs : Inputs WideExact 5) (coins : GSConcreteByteDecoderBank.RawCoins) :
    (jobs inputs coins).Bounded 113 (P31^8+1) (GSActualBankJobsM10.count 149) := by
  have hj := GSScalarJobsM10.bounded 112 (P31^8) _ (bounded inputs coins)
  have hc := length inputs coins
  exact ⟨hj.gcd_count.trans hc,hj.division_count.trans hc,hj.power_count.trans hc,
    hj.gcd_sizes,hj.division_sizes,hj.power_bits⟩

#print axioms length
#print axioms bounded
#print axioms jobs_bounded
end AspisR1.GSActualByteJobsM10
end
