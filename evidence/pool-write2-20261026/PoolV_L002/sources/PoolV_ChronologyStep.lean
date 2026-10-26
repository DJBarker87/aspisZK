import PoolV_ChronologySource
set_option autoImplicit false
namespace AspisR1.PoolV_ChronologyStep
open Aeneas Aeneas.Std Result ControlFlow

theorem step (new old : Slice U64) (i : Usize) (n o : U64) (d p : Bool)
    (hn : i < Slice.len new) (ho : i < Slice.len old)
    (rn : Slice.index_usize new i = ok n) (ro : Slice.index_usize old i = ok o) :
    PoolV_Chronology.chronology_scan_loop.body new old i d p =
      ok (cont (Usize.wrapping_add i 1#usize, d || decide (n < o), p || decide (n > o))) := by
  simp [PoolV_Chronology.chronology_scan_loop.body,hn,ho,rn,ro,lift]

theorem end_new (new old : Slice U64) (i : Usize) (d p : Bool)
    (hn : ¬ i < Slice.len new) :
    PoolV_Chronology.chronology_scan_loop.body new old i d p = ok (done (d,p)) := by
  simp [PoolV_Chronology.chronology_scan_loop.body,hn]

theorem end_old (new old : Slice U64) (i : Usize) (d p : Bool)
    (ho : ¬ i < Slice.len old) :
    PoolV_Chronology.chronology_scan_loop.body new old i d p = ok (done (d,p)) := by
  simp [PoolV_Chronology.chronology_scan_loop.body,ho]

theorem increment (new : Slice U64) (i : Usize) (within : i < Slice.len new) :
    (Usize.wrapping_add i 1#usize).val = i.val+1 := by
  have size := new.property
  have range : i.val + 1 ≤ Usize.max := by scalar_tac
  rw [Usize.wrapping_add_val_eq]
  have strict : i.val + (1#usize).val < UScalar.size .Usize := by
    simp only [UScalar.size,UScalarTy.numBits,Usize.max,Usize.numBits] at range ⊢
    scalar_tac
  rw [Nat.mod_eq_of_lt strict]
  rfl

#print axioms step
#print axioms end_new
#print axioms end_old
#print axioms increment
end AspisR1.PoolV_ChronologyStep
