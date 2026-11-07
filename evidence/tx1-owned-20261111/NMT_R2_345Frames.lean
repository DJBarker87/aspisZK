import NMT_R2_Spec345
import NMT_R2_Observation
set_option autoImplicit false
namespace NMT_R2_345
open RSL
structure Parent where
 original : NMT_R2.TX1_345.Args
 proofAccount : OwnedAccount
 publicAccount : OwnedAccount
 checkpointAccount : OwnedAccount
structure CheckpointData extends Parent where
 checkpointData : Bytes
structure PublicData extends CheckpointData where
 publicData : Bytes
structure Decoded (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) extends PublicData where
 statement : C.Statement
structure Validated (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) extends Decoded V C where
 validated : C.validateStatement statement = true
structure Candidate (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) extends Validated V C where
 candidate : Bytes
structure ProofData (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) extends Candidate V C where
 proofData : Bytes
/-- Site-indexed allocation replies are invocation observations, universally
quantified, never successful-allocation premises. No allocation emits an event. -/
abbrev Allocation := Nat → Bool
end NMT_R2_345
