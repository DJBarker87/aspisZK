import R1Z.PV_RDCD_Wrapping194
set_option autoImplicit false
namespace R1Z.PV_RDCD_ShiftLiterals
open Aeneas Aeneas.Std
/- Exact finite set of renderer typing corrections from committed
   evidence/pv-cb-20261026/op107-normalization.json. These are primitive
   bitvector laws for arbitrary x; no edited regenerated declaration is used. -/
theorem count31 : (31#i32).val.toNat = (31#u32).val := rfl
theorem count1 : (1#i32).val.toNat = (1#u32).val := rfl

theorem shift31 (x : U64) :
    ((x.bv.ushiftRight ((31#i32).val.toNat % 64))#uscalar : U64) =
      U64.wrapping_shr x 31#u32 := rfl

theorem shift1 (x : U64) :
    ((x.bv.ushiftRight ((1#i32).val.toNat % 64))#uscalar : U64) =
      U64.wrapping_shr x 1#u32 := rfl
#print axioms count31
#print axioms count1
#print axioms shift31
#print axioms shift1
end R1Z.PV_RDCD_ShiftLiterals
