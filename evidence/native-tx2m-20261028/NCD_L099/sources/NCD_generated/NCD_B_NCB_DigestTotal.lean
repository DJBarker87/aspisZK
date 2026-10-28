-- Inherited body, import-only deployed-cohort retarget.
import RPz7_F3U_Rehash
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCB_DigestTotal
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation
/-- Total completion for the adopted oracle dictionary. This is a model
completion, not native request validity or a runtime SHA proof. -/
theorem total {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (hash : Hash) (parts : Slice (Slice U8)) :
    ∃ reply, (F3U_Rehash.dictionary H D).digest hash parts=ok reply :=
  ⟨encodeState (H (flatten parts)),rfl⟩
/-- On a reached runtime reply satisfying the existing SHA realization row,
the total model completion returns exactly the same bytes. -/
theorem reached {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (hash : Hash) (parts : Slice (Slice U8)) (reply : Array U8 32#usize)
    (runtime : decodeState reply=H (flatten parts)) :
    (F3U_Rehash.dictionary H D).digest hash parts=ok reply := by
  change ok (encodeState (H (flatten parts)))=ok reply
  rw [←runtime]
  exact congrArg Result.ok (array_roundtrip reply)
#print axioms total
#print axioms reached
end AspisR1.NCB_DigestTotal
end
