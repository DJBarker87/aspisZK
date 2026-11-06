import NJE_CountArrayFrame

set_option autoImplicit false
namespace NJE_CountKeyFrame
open Aeneas Aeneas.Std

theorem outside (a : Array U32 16#usize) (j : Nat) (bound : 16≤j) :
    NJA_CountDrop.keys a j=0 := by
 unfold NJA_CountDrop.keys
 rw [List.getElem!_eq_getElem?_getD,List.getElem?_eq_none (by
   have h : a.val.length=16 := a.property
   omega : a.val.length≤j)]
 rfl

theorem whole (a : Array U32 16#usize) (i w : Usize)
    (ib : i.val<16) (wb : w.val<16) :
    NJA_CountDrop.keys (a.set w (U32.wrapping_shr (a.val[i.val]!) 1#u32))=
      AspisR1.MultiproofConeLiveOrder.write (NJA_CountDrop.keys a) i.val w.val := by
 funext j
 by_cases jb : j<16
 · exact NJE_CountArrayFrame.keys_write a i w ib wb j jb
 · have noWrite : j≠w.val := by omega
   unfold AspisR1.MultiproofConeLiveOrder.write
   rw [if_neg noWrite,outside _ j (by omega),outside a j (by omega)]

#print outside
#print axioms outside
#print whole
#print axioms whole
end NJE_CountKeyFrame
