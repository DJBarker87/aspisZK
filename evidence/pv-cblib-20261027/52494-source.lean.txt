import R1Z.PV_CBL_PadArrayModel
import R1Z.PV_CBL_PadContentSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadArraySource
set_option autoImplicit false
theorem option_ext {T : Type} {P : T→Prop} (a b : Option {x:T // P x})
    (h : a.map Subtype.val=b.map Subtype.val) : a=b := by
  cases a with
  | none => cases b <;> first | rfl | cases h
  | some a =>
    cases b with
    | none => cases h
    | some b =>
      apply congrArg some
      apply Subtype.ext
      exact Option.some.inj h
theorem source (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize)
    (hp : pos.val<64) :
    PV_CBL_ShaPadFixed.sha_pad_owned_split8 buffer pos suffix =
      ok (PV_CBL_PadArrayModel.first buffer pos suffix hp,
          PV_CBL_PadArrayModel.second pos suffix,
          PV_CBL_PadArrayModel.first buffer pos suffix hp,0#usize) := by
  obtain ⟨first,second,hr,hf,hs⟩ := PV_CBL_PadContentSource.source buffer pos suffix hp
  have hfirst : first=PV_CBL_PadArrayModel.first buffer pos suffix hp := Subtype.ext hf
  have hsecond : second=PV_CBL_PadArrayModel.second pos suffix :=
    option_ext _ _ (hs.trans (PV_CBL_PadArrayModel.second_val pos suffix).symm)
  rw [hr,hfirst,hsecond]
#print axioms option_ext
#print axioms source
end R1Z.PV_CBL_PadArraySource
