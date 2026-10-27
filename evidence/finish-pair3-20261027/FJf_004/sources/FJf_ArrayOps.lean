import FJf_PointBody
set_option autoImplicit false
namespace AspisR1.FJf_ArrayOps
open Aeneas Aeneas.Std Result

theorem update_val {A : Type} {N : Usize} (a b : Array A N) (i : Usize) (x : A)
    (run : Array.update a i x=ok b) : b.val=a.val.set i.val x := by
  unfold Array.update at run
  split at run
  · cases run
  · cases Result.ok.inj run; rfl

theorem index_mut {A : Type} {N : Usize} (a : Array A N) (i : Usize)
    (x : A) (back : A → Array A N) (run : Array.index_mut_usize a i=ok (x,back)) :
    Array.index_usize a i=ok x ∧ back=Array.set a i := by
  unfold Array.index_mut_usize at run
  obtain ⟨v,hv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨hv,rfl⟩

theorem set_val {A : Type} {N : Usize} (a : Array A N) (i : Usize) (x : A) :
    (Array.set a i x).val=a.val.set i.val x := rfl

#print axioms update_val
#print axioms index_mut
#print axioms set_val
end AspisR1.FJf_ArrayOps
