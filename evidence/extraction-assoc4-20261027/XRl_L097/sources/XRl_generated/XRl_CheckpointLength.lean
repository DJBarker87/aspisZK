import XRl_CheckpointBytes
import XRk_ResultTools
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRl_CheckpointLength
/-- Size of every successful checkpoint external-model output. This uses its
actual final check; it does not assert the native checkpoint reaches that check
or that a physical account stores these bytes. -/
theorem accepted {H : Type} (d : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H)
    (bytes : alloc.vec.Vec U8) (run : verifier.checkpoint d p a proof pub hash=ok bytes) :
    bytes.val.length=(if p.variant matches .S1 then 4840 else 1768) := by
  unfold verifier.checkpoint at run
  obtain ⟨proofHash,_,run⟩ := bind_success _ _ _ run
  obtain ⟨publicHash,_,run⟩ := bind_success _ _ _ run
  obtain ⟨wideBytes,_,run⟩ := bind_success _ _ _ run
  obtain ⟨payload,_,run⟩ := bind_success _ _ _ run
  obtain ⟨checksum,_,run⟩ := bind_success _ _ _ run
  split at run
  · rename_i size
    unfold XRk_asSlice at run
    split at run
    · have actual := congrArg (fun s : Slice U8 => s.val.length) (Result.ok.inj run)
      exact actual.symm.trans size
    · cases run
  · cases run
#print axioms accepted
end XRl_CheckpointLength
