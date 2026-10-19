import LiteralFreshAbortComposition
import GSConcreteByteDecoderBank

set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralFreshBankAbortComposition

open AspisR1.LiteralFreshAbortComposition
open AspisR1.GSConcreteByteDecoderBank
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.LiteralTranscript
open AspisR1.LiteralFreshAttemptBound
open AspisR1.PerAttemptEnvelope
open FS FS2
open AspisV8R19.R572SequentialWordMass
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.SourceDuplexStep
open AspisV8R19.DuplexFrames
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open FS
attribute [local instance] Classical.propDecidable

/-- The fixed-input decoder bank abort probability. Its bound is uniform in
all point arrays, so those arrays may depend on the completed protocol prefix. -/
def bankAbortMass (inputs : Inputs K 5) : ℚ :=
  mean (fun xs : RawCoins => indicator (failed inputs xs))

theorem bankAbortMass_le (inputs : Inputs K 5) :
    bankAbortMass inputs ≤ (1 / (2 : ℚ)^126) := by
  simpa [bankAbortMass] using le_of_lt (failure_small inputs)

/-- Fresh 33-round challenge sampling plus an independent call of the actual
fixed-input GS byte bank. The bank guarantee is uniform for every input, hence
it remains valid when its received words and interpolation points are chosen
from the completed challenge transcript. -/
theorem actualBankCombinedMass_le
    {Aux : Type}
    (choose : LiteralTranscript.Prefix → Aux → LiteralTranscript.Message)
    (update : LiteralTranscript.Prefix → LiteralTranscript.Message → Aux →
      View Bytes State LiteralTranscript.Challenge → Aux)
    (inputsAt : LiteralTranscript.Prefix → Aux → Inputs K 5)
    (pub : LiteralTranscript.Public) (ctx : Aux) :
    combinedMass choose update (fun P c => bankAbortMass (inputsAt P c)) 33
      (FS.emptyPrefix pub) ctx ≤ 33 * B + (1 / (2 : ℚ)^126) := by
  exact combinedMass_le choose update
    (fun P c => bankAbortMass (inputsAt P c))
    (1 / (2 : ℚ)^126) (by positivity) 33 (FS.emptyPrefix pub) ctx
    (by simp [FS.emptyPrefix])
    (by intro P c hlen; exact bankAbortMass_le (inputsAt P c))

#print axioms bankAbortMass
#print axioms bankAbortMass_le
#print axioms actualBankCombinedMass_le
end AspisR1.LiteralFreshBankAbortComposition
end
