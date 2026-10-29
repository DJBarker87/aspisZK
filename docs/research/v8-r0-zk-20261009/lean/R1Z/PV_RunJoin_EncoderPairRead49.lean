import R1Z.PV_DL_EncoderZip
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderPairRead49
open Aeneas Aeneas.Std Result

theorem even {A : Type} [Inhabited A] (q : Array A 1024#usize) (j : Usize) (hj : j.val<512) :
  Array.index_usize q (Usize.wrapping_mul 2#usize j)=ok q.val[2*j.val]! := by
  rw [PV_CBL_ArrayReadValue.read q _ (by rw [PV_DL_EncoderRange.even j hj];change 2*j.val<1024;omega)]
  rw [PV_DL_EncoderRange.even j hj]

theorem odd {A : Type} [Inhabited A] (q : Array A 1024#usize) (j : Usize) (hj : j.val<512) :
  Array.index_usize q (Usize.wrapping_add (Usize.wrapping_mul 2#usize j) 1#usize)=ok q.val[2*j.val+1]! := by
  rw [PV_CBL_ArrayReadValue.read q _ (by rw [PV_DL_EncoderRange.odd j hj];change 2*j.val+1<1024;omega)]
  rw [PV_DL_EncoderRange.odd j hj]

theorem basis {A : Type} [Inhabited A] (q : Array A 512#usize) (j : Usize) (hj : j.val<512) :
  Array.index_usize q j=ok q.val[j.val]! := PV_CBL_ArrayReadValue.read q j hj
#print axioms even
#print axioms odd
#print axioms basis
end R1Z.PV_RunJoin_EncoderPairRead49
