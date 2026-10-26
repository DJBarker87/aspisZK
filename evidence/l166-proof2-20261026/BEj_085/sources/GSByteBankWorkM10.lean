import GSBankOutputEnvelopeM10
import GSByteSamplerWorkM10
import PublicParserWork
import OptionWorkInvariantM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.GSByteBankWorkM10
open AspisWideTower GSFixedInputDecoderFamily GSDecoderTapeReindex
open M31AcceptFiber M31RetryOutputFiber
attribute [local irreducible] GSDecoderActualBankM10.run GSDecoderActualBankM10.bankBudget

def reindexBudget : Nat := 1000*34*21377328

def run (inputs : Inputs WideExact 5) (coins : GSConcreteByteDecoderBank.RawCoins) :
    Option (Results WideExact 5) × Nat :=
  PublicParserWork.bind (GSByteSamplerWorkM10.sample 21377328 coins) (fun H =>
    let b := GSDecoderActualBankM10.run (P31^8) 149 inputs
      (flatBank WideExact (1025*112) (256*112) 149 H)
    (some b.1,b.2+reindexBudget+1))

attribute [local irreducible] GSByteSamplerWorkM10.sample actualWidePairSamplerTape

theorem value (inputs : Inputs WideExact 5) (coins : GSConcreteByteDecoderBank.RawCoins) :
    (run inputs coins).1 = GSConcreteByteDecoderBank.run inputs coins := by
  simp only [run,PublicParserWork.bind_value,GSByteSamplerWorkM10.value,
    GSConcreteByteDecoderBank.run,GSRejectingSamplerDecoderBank.sampleAndRun,
    GSDecoderActualBankM10.run_value]
  cases actualWidePairSamplerTape 21377328 coins <;> rfl

@[never_extract,noinline] def budget : Nat :=
  1401091454450+GSDecoderActualBankM10.bankBudget (P31^8) 149+reindexBudget+1

theorem work (inputs : Inputs WideExact 5) (coins : GSConcreteByteDecoderBank.RawCoins) :
    (run inputs coins).2 ≤ budget+1 := by
  have hb (H : ActualWidePairOutputTape 21377328) :=
    Nat.add_le_add_right (Nat.add_le_add_right
      (GSDecoderActualBankM10.run_work (P31^8) 149 inputs GSConcreteByteDecoderBank.field_card
        (flatBank WideExact (1025*112) (256*112) 149 H)) reindexBudget) 1
  have hh := PublicParserWork.bind_work (GSByteSamplerWorkM10.sample 21377328 coins)
    (fun H =>
      let b := GSDecoderActualBankM10.run (P31^8) 149 inputs
        (flatBank WideExact (1025*112) (256*112) 149 H)
      (some b.1,b.2+reindexBudget+1))
    1401091454450 (GSDecoderActualBankM10.bankBudget (P31^8) 149+reindexBudget+1)
    (GSByteSamplerWorkM10.concrete_work coins) hb
  simpa only [run,budget,Nat.add_assoc] using hh

theorem bounded (inputs : Inputs WideExact 5) (coins : GSConcreteByteDecoderBank.RawCoins)
    (out : Results WideExact 5) (ho : (run inputs coins).1 = some out) :
    GSBankOutputEnvelopeM10.Bounded out := by
  have hh := OptionWorkInvariantM10.bind_property
    (GSByteSamplerWorkM10.sample 21377328 coins)
    (fun H =>
      let b := GSDecoderActualBankM10.run (P31^8) 149 inputs
        (flatBank WideExact (1025*112) (256*112) 149 H)
      (some b.1,b.2+reindexBudget+1))
    (fun o => ∀ out, o = some out → GSBankOutputEnvelopeM10.Bounded out)
    (by intro out h; cases h)
    (fun H _ out hout => by
      have hh := GSBankOutputEnvelopeM10.actual_bounded (P31^8) 149 inputs
        GSConcreteByteDecoderBank.field_card (flatBank WideExact (1025*112) (256*112) 149 H)
      exact Option.some.inj hout ▸ hh)
  exact hh out ho

#print axioms value
#print axioms work
#print axioms bounded
end AspisR1.GSByteBankWorkM10
end
