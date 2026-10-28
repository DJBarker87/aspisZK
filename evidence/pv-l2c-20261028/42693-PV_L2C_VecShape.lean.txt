import PV_L2C_VecRead
set_option autoImplicit false
namespace PV_L2C_VecShape
open Aeneas Aeneas.Std Result PV_L2C_VecRead

theorem length {A : Type} {n : Nat} (hn : n≤Usize.max) (f : Fin n → A) :
    alloc.vec.Vec.len (vector hn f)=Usize.ofNatCore n hn := by
  apply UScalar.eq_of_val_eq
  change (List.ofFn f).length=n
  exact List.length_ofFn
#print axioms length

theorem active_read (f : Fin 1024 → Bool) (r : Usize) (hr : r.val<1024) :
    Aeneas.Std.Array.index_usize (active (n:=1024#usize) f) r=ok (f ⟨r.val,hr⟩) := by
  have hr' : r.val<(1024#usize).val := by scalar_tac
  exact read_active (n:=1024#usize) f r hr'
#print axioms active_read
end PV_L2C_VecShape
