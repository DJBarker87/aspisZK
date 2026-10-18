import R1InitialWalk
import R1RawRoundDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSemanticRecovery
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}
def typed (p : Params M Cv L) (pubBytes : Bytes) (T : Table (Addr L) State)
    (fuel : Nat) (endpoint : State) : Option (State × List (Rec M)) :=
  (InitialWalk.walk p pubBytes T fuel endpoint).bind fun (c1, raw) =>
    (RawRoundDecode.decode p 0 raw).map fun rs => (c1, rs)

#print axioms typed
end AspisR1.UnifiedSemanticRecovery
end
