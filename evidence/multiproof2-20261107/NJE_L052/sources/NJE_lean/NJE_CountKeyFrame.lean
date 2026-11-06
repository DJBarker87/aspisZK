import NJE_CountArrayFrame

set_option autoImplicit false
namespace NJE_CountKeyFrame
open Aeneas Aeneas.Std

theorem whole (a : Array U32 16#usize) (i w : Usize)
    (ib : i.val<16) (wb : w.val<16) :
    NJA_CountDrop.keys (a.set w (U32.wrapping_shr (a.val[i.val]!) 1#u32))=
      AspisR1.MultiproofConeLiveOrder.write (NJA_CountDrop.keys a) i.val w.val := by
 funext j
 by_cases jb : j<16
 · exact NJE_CountArrayFrame.keys_write a i w ib wb j jb
 · have len : a.val.length=16 := a.property
   have setlen : (a.set w (U32.wrapping_shr (a.val[i.val]!) 1#u32)).val.length=16 :=
     (a.set w (U32.wrapping_shr (a.val[i.val]!) 1#u32)).property
   have noWrite : j≠w.val := by omega
   unfold AspisR1.MultiproofConeLiveOrder.write NJA_CountDrop.keys
   simp only [if_neg noWrite,List.getElem!_eq_getElem?_getD,
     List.getElem?_eq_none (by omega : a.val.length≤j),
     List.getElem?_eq_none (by omega :
       (a.set w (U32.wrapping_shr (a.val[i.val]!) 1#u32)).val.length≤j)]

#print whole
#print axioms whole
end NJE_CountKeyFrame
