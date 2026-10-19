import LiteralFreshBankAbortComposition

set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralFreshBankStrictBound

open AspisR1.LiteralFreshBankAbortComposition
open AspisR1.LiteralFreshAbortComposition
open AspisR1.PerAttemptEnvelope
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.GSConcreteByteDecoderBank
open FS FS2
open AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.SourceDuplexStep

/-- The 33 fresh-row classifier mass plus the actual fixed-input GS-bank
abort mass is strictly below 2^-100. The accepted-message event inclusion
remains a separate caller obligation. -/
theorem actualBankCombinedMass_lt
    {Aux : Type}
    (choose : LiteralTranscript.Prefix → Aux → LiteralTranscript.Message)
    (update : LiteralTranscript.Prefix → LiteralTranscript.Message → Aux →
      View Bytes State LiteralTranscript.Challenge → Aux)
    (inputsAt : LiteralTranscript.Prefix → Aux → Inputs K 5)
    (pub : LiteralTranscript.Public) (ctx : Aux) :
    combinedMass choose update (fun P c => bankAbortMass (inputsAt P c)) 33
      (FS.emptyPrefix pub) ctx < 1 / (2^100 : ℚ) := by
  have hmass := actualBankCombinedMass_le choose update inputsAt pub ctx
  have hslack : 33 * PerAttemptEnvelope.B + (1 / (2 : ℚ)^126) <
      1 / (2^100 : ℚ) := by
    unfold PerAttemptEnvelope.B
    norm_num
  exact hmass.trans_lt hslack

#print axioms actualBankCombinedMass_lt
end AspisR1.LiteralFreshBankStrictBound
end
