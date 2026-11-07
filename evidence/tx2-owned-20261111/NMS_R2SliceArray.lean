import NMS_R2AnyM
set_option autoImplicit false
namespace NMS_R2SliceArray
open Aeneas Aeneas.Std Result WP
/-- Total std slice/array comparison at the decoder's exact helper, reused
from the coherent symbolic std equality law. -/
@[step] theorem total {N : Usize} (a : Slice U8) (b : Array U8 N) :
 _root_.Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8 a b ⦃ _ => True ⦄ := by
 unfold _root_.Slice.Insts.CoreCmpPartialEqArray.ne core.slice.cmp.PartialEqSlice.ne
 split
 · apply exists_imp_spec
   obtain ⟨reply,run⟩ := NMS_R2AnyM.total
    (fun pair : U8 × U8 => core.cmp.PartialEqU8.ne pair.1 pair.2)
    (fun _ => ⟨_,rfl⟩) (a.val.zip b.to_slice.val)
   exact ⟨reply,run,trivial⟩
 · exact exists_imp_spec ⟨true,rfl,trivial⟩

#print axioms total
end NMS_R2SliceArray
