import NIW_AlignPacket
import NIT_FinishComposition
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignPacketPort
open Aeneas Aeneas.Std Result NIT_Cuts NIT_PairControl AspisR1Stage2

/-- The port consumes the supplied actual native reply, not a packet witness.
The only reply equality is the parent's reviewed return cut. -/
theorem returned (owner alpha message : Nat) (p : verifier.Prepared)
 (l : PairPort) (reply : NR) (afterOwner : Nat)
 (cut : cutPairPort owner alpha message p l (NIT_ErrorTransport.reply reply) afterOwner) :
 l.reply=NIT_ErrorTransport.reply reply ∧
 ok l.reply=NIT_ErrorTransport.full (ok reply) := by
 have same := (NIT_FinishComposition.pair_port owner alpha message p l _ afterOwner cut).symm
 exact ⟨same,congrArg Result.ok same⟩

/-- Outer failure has no returning PairPort reply to invent. -/
theorem failed (err : Error) :
 NIT_ErrorTransport.full (fail err : Result NR)=fail err := rfl

theorem diverged : NIT_ErrorTransport.full (div : Result NR)=div := rfl

#print axioms returned
#print axioms failed
#print axioms diverged
end AspisR1.NIW_AlignPacketPort
