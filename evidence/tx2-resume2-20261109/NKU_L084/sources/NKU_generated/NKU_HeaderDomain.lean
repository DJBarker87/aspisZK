import NKU_HeaderSize
import NKK_LogReduce
set_option autoImplicit false
noncomputable section
namespace NKU_HeaderDomain
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
/-- A rejected length never reaches an iterator or digest. -/
theorem wrong_length {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (wrong : Slice.len bytes≠1768#usize) :
 NKU_HeaderValue.value d bytes .S2=pure (.Err .Checkpoint) := by
 unfold NKU_HeaderValue.value
 dsimp only
 rw [NKU_HeaderSize.size]
 simp only [NKK_LogReduce.lift_ok_bind]
 simp [wrong]
/-- Caller native checkpoint domain derived from the actual returned header,
not added as a successful-child or accepted-parent root hypothesis. -/
theorem length {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (reply : U8 × Usize)
 (returned : (NKU_HeaderValue.value d bytes .S2).result=ok (.Ok reply)) :
 bytes.val.length=1768 := by
 have size : Slice.len bytes=1768#usize := by
  by_contra wrong
  rw [wrong_length d bytes wrong] at returned
  cases returned
 have h:=congrArg UScalar.val size
 exact h
#print axioms wrong_length
#print axioms length
end NKU_HeaderDomain
