import R1Z.PV_RunJoin_NativeQuarticTotal69
import R1Z.PV_RunJoin_LayoutArithmetic41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeRoundShape73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (row : U8)
    (lower : 15 ≤ row.val) (upper : row.val ≤ 24) :
    @r1_wire.row_shape (types base) (opsNative base heap box ops runtime world) row=
      ok (some (2#u8,896#usize)) := by
  have values : row.val=15 ∨ row.val=16 ∨ row.val=17 ∨ row.val=18 ∨ row.val=19 ∨ row.val=20 ∨ row.val=21 ∨ row.val=22 ∨ row.val=23 ∨ row.val=24 := by omega
  rcases values with h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
  · have eq : row=15#u8 := UScalar.eq_of_val_eq h15
    subst row
    change ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize))=ok (some (2#u8,896#usize))
    rw [PV_RunJoin_LayoutArithmetic41.mul 28#usize 32#usize 896#usize rfl]
  · have eq : row=16#u8 := UScalar.eq_of_val_eq h16
    subst row
    change ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize))=ok (some (2#u8,896#usize))
    rw [PV_RunJoin_LayoutArithmetic41.mul 28#usize 32#usize 896#usize rfl]
  · have eq : row=17#u8 := UScalar.eq_of_val_eq h17
    subst row
    change ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize))=ok (some (2#u8,896#usize))
    rw [PV_RunJoin_LayoutArithmetic41.mul 28#usize 32#usize 896#usize rfl]
  · have eq : row=18#u8 := UScalar.eq_of_val_eq h18
    subst row
    change ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize))=ok (some (2#u8,896#usize))
    rw [PV_RunJoin_LayoutArithmetic41.mul 28#usize 32#usize 896#usize rfl]
  · have eq : row=19#u8 := UScalar.eq_of_val_eq h19
    subst row
    change ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize))=ok (some (2#u8,896#usize))
    rw [PV_RunJoin_LayoutArithmetic41.mul 28#usize 32#usize 896#usize rfl]
  · have eq : row=20#u8 := UScalar.eq_of_val_eq h20
    subst row
    change ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize))=ok (some (2#u8,896#usize))
    rw [PV_RunJoin_LayoutArithmetic41.mul 28#usize 32#usize 896#usize rfl]
  · have eq : row=21#u8 := UScalar.eq_of_val_eq h21
    subst row
    change ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize))=ok (some (2#u8,896#usize))
    rw [PV_RunJoin_LayoutArithmetic41.mul 28#usize 32#usize 896#usize rfl]
  · have eq : row=22#u8 := UScalar.eq_of_val_eq h22
    subst row
    change ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize))=ok (some (2#u8,896#usize))
    rw [PV_RunJoin_LayoutArithmetic41.mul 28#usize 32#usize 896#usize rfl]
  · have eq : row=23#u8 := UScalar.eq_of_val_eq h23
    subst row
    change ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize))=ok (some (2#u8,896#usize))
    rw [PV_RunJoin_LayoutArithmetic41.mul 28#usize 32#usize 896#usize rfl]
  · have eq : row=24#u8 := UScalar.eq_of_val_eq h24
    subst row
    change ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize))=ok (some (2#u8,896#usize))
    rw [PV_RunJoin_LayoutArithmetic41.mul 28#usize 32#usize 896#usize rfl]

#print axioms complete
end R1Z.PV_RunJoin_NativeRoundShape73
