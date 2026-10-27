import R1Z.PV_CBL_PadDelimitedBytes
import R1Z.PV_CBL_PadModelBytes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadDelimitedSource
set_option autoImplicit false
theorem source (buffer : Array U8 64#usize) (pos : Usize) (hp : pos.val<64) :
    ∃ a, PV_CBL_ShaPadFixed.sha_pad_zero buffer pos = ok a ∧
      a.val = PV_CBL_PaddingModel.delimited buffer.val pos.val := by
  obtain ⟨a,ha,hc⟩ := PV_CBL_PadDelimitedBytes.source buffer pos hp
  refine ⟨a,ha,PV_CBL_PadListFacts.ext _ _ ?_ ?_⟩
  · rw [a.property,PV_CBL_PaddingLength.delimited_length buffer.val pos.val buffer.property hp]
    rfl
  · intro j hj
    have hj64 : j<64 := by simpa [a.property] using hj
    rw [hc j hj64,PV_CBL_PadModelBytes.delimited_byte buffer.val pos.val j buffer.property hp hj64]
#print axioms source
end R1Z.PV_CBL_PadDelimitedSource
