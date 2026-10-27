import RPt_FIo_ArrayCanon
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_ArrayBack
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem canonical {N : Usize} (a : Array NE N) (i : Usize)
    (old : NE) (back : NE → Array NE N)
    (run : Array.index_mut_usize a i=ok (old,back))
    (inv : FIo_ArrayCanon.Holds a) (value : NE) (hv : FIo_WideValues.Canon value) :
    FIo_ArrayCanon.Holds (back value) := by
  unfold Array.index_mut_usize at run
  obtain ⟨x,hx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same := congrArg Prod.snd (Result.ok.inj run)
  have backEq : back=Aeneas.Std.Array.set a i := same.symm
  rw [backEq]
  exact FIo_ArrayCanon.list_set FIo_WideValues.Canon a.val i.val value inv hv

#print axioms canonical
end AspisR1.FIo_ArrayBack
end
