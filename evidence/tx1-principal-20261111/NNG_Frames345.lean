import NNG_Pure345
-- Rev4 frame retarget; the SAME reached decode equality is retained internally.
set_option autoImplicit false
namespace AspisR1.NNG_Phases345
open RSL
structure Parent where
 original : TX1_345.Args
 proofAccount : OwnedAccount
 publicAccount : OwnedAccount
 checkpointAccount : OwnedAccount
structure CheckpointData extends Parent where
 checkpointData : Bytes
structure PublicData extends CheckpointData where
 publicData : Bytes
structure Decoded (V : VLib) (C : TX1_345.S1Lib V) extends PublicData where
 statement : C.Statement
 decoded : C.decodeStatement publicData=some statement
structure Validated (V : VLib) (C : TX1_345.S1Lib V) extends Decoded V C where
 validated : C.validateStatement statement = true
structure Candidate (V : VLib) (C : TX1_345.S1Lib V) extends Validated V C where
 candidate : Bytes
structure ProofData (V : VLib) (C : TX1_345.S1Lib V) extends Candidate V C where
 proofData : Bytes
/-- Site-indexed allocation replies are invocation observations, universally
quantified, never successful-allocation premises. No allocation emits an event. -/
abbrev Allocation := Nat → Bool
end AspisR1.NNG_Phases345
