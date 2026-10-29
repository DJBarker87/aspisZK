import R1Z.PV_CBL_FinalizeSoftValue
import R1Z.PV_CBL_PadArraySource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FinalizeSoftSource
set_option autoImplicit false
def state (initial : Array U32 8#usize) (blocks : U64)
    (buffer : Array U8 64#usize) (pos : Usize) (hp : pos.val<64) : Array U32 8#usize :=
  let suffix := PV_CBL_Suffix64Value.value (PV_CBL_ShaBitLength.bitLength pos blocks)
  PV_CBL_FinalizeSoftValue.next initial (PV_CBL_PadArrayModel.first buffer pos suffix hp)
    (PV_CBL_PadArrayModel.second pos suffix)
theorem source (initial : Array U32 8#usize) (blocks : U64)
    (buffer : Array U8 64#usize) (pos : Usize) (hp : pos.val<64) :
    PV_CBL_FinalSoft.sha_finalize_soft_owned initial blocks buffer pos =
      ok (PV_CBL_DigestBytesValue.value (state initial blocks buffer pos hp),
          state initial blocks buffer pos hp,
          PV_CBL_PadArrayModel.first buffer pos
            (PV_CBL_Suffix64Value.value (PV_CBL_ShaBitLength.bitLength pos blocks)) hp,0#usize) := by
  obtain ⟨first,second,hr,hf,hs⟩ := PV_CBL_FinalizeSoftValue.source initial blocks buffer pos hp
  have hfirst : first=PV_CBL_PadArrayModel.first buffer pos
      (PV_CBL_Suffix64Value.value (PV_CBL_ShaBitLength.bitLength pos blocks)) hp := Subtype.ext hf
  have hsecond : second=PV_CBL_PadArrayModel.second pos
      (PV_CBL_Suffix64Value.value (PV_CBL_ShaBitLength.bitLength pos blocks)) :=
    PV_CBL_PadArraySource.option_ext _ _ (hs.trans (PV_CBL_PadArrayModel.second_val _ _).symm)
  rw [hr,hfirst,hsecond]
  rfl
#print axioms state
#print axioms source
end R1Z.PV_CBL_FinalizeSoftSource
