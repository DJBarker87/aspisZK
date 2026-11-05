import NHI_Tensor
import NHM_DotCallDomain
set_option autoImplicit false
namespace NHX_VecPort
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev Vec := alloc.vec.Vec NQ

theorem borrow_value (v : Vec) : (alloc.vec.Vec.deref_mut v).1.val=(alloc.vec.Vec.deref v).val := by rfl

theorem back_value (v : Vec) (s : Slice NQ) :
 (alloc.vec.Vec.deref ((alloc.vec.Vec.deref_mut v).2 s)).val=s.val := by rfl

theorem back_canonical (v : Vec) (s : Slice NQ) (hs : NHI_CellCanon.slice s) :
 NHI_CellCanon.slice (alloc.vec.Vec.deref ((alloc.vec.Vec.deref_mut v).2 s)) := by
 simpa only [NHI_CellCanon.slice,back_value] using hs

theorem back_length (v : Vec) (s : Slice NQ) (hs : s.val.length=64) :
 (alloc.vec.Vec.deref ((alloc.vec.Vec.deref_mut v).2 s)).val.length=64 := by
 rw [back_value]
 exact hs

#print axioms borrow_value
#print axioms back_value
#print axioms back_canonical
#print axioms back_length
end NHX_VecPort
