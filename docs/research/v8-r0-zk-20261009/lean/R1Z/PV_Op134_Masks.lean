import R1Z.PV_CBM_MasksReference
namespace R1Z.PV_Op134_Masks
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def masks : Array U16 64#usize := Array.make 64#usize [6144#u16, 6144#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6144#u16, 4097#u16, 2048#u16, 6145#u16, 2049#u16, 2048#u16, 6145#u16, 2049#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 4097#u16, 6145#u16, 6145#u16, 4097#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 1749#u16]
theorem source : PV_CBM_ReferenceRaw.reference.masks = ok (.Ok masks) := rfl
theorem length : masks.val.length = 64 := rfl
#print axioms source
#print axioms length
end R1Z.PV_Op134_Masks
