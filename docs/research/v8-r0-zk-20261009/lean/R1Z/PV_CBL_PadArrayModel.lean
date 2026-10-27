import R1Z.PV_CBL_PaddingLength
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadArrayModel
set_option autoImplicit false
def first (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize)
    (hp : pos.val<64) : Array U8 64#usize :=
  ⟨PV_CBL_PaddingModel.first buffer.val pos.val suffix.val,
    PV_CBL_PaddingLength.first_length buffer.val suffix.val pos.val buffer.property hp suffix.property⟩
def second (pos : Usize) (suffix : Array U8 8#usize) : Option (Array U8 64#usize) :=
  if pos.val<56 then none else
    some ⟨List.replicate 56 0#u8 ++ suffix.val,by simp [suffix.property]⟩
theorem first_val (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize)
    (hp : pos.val<64) :
    (first buffer pos suffix hp).val = PV_CBL_PaddingModel.first buffer.val pos.val suffix.val := rfl
theorem second_val (pos : Usize) (suffix : Array U8 8#usize) :
    (second pos suffix).map (fun a => a.val) = PV_CBL_PaddingModel.second pos.val suffix.val := by
  unfold second PV_CBL_PaddingModel.second
  split <;> rfl
#print axioms first
#print axioms second
#print axioms first_val
#print axioms second_val
end R1Z.PV_CBL_PadArrayModel
