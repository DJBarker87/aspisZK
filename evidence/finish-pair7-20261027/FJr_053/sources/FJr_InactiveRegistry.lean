import FJc_S2Rows
import R0P.Copy
set_option autoImplicit false
namespace AspisR1.FJr_InactiveRegistry
open Aeneas Aeneas.Std

theorem list : FIo_Native.aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS.val.map UScalar.val=
    List.ofFn R0P.copyActiveRowMasks := by
  unfold FIo_Native.aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS
  simp only [Array.make,List.map_cons,List.map_nil,List.ofFn_succ,List.ofFn_zero,
    R0P.copyActiveRowMasks,Matrix.cons_val_zero,Matrix.cons_val_succ]
  rfl

theorem value (r : Nat) (hr : r<1024) :
    FJc_S2Rows.activeMask r=R0P.copyActiveRowMasks ⟨r/16,by omega⟩ := by
  have hi : r/16<FIo_Native.aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS.val.length := by
    rw [FIo_Native.aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS.property]
    omega
  have h := congrArg (fun xs : List Nat=>xs[r/16]?) list
  rw [List.getElem?_map,List.getElem?_ofFn,dif_pos (by omega : r/16<64),List.getElem?_eq_getElem hi,Option.map_some] at h
  unfold FJc_S2Rows.activeMask
  rw [List.getElem?_eq_getElem hi]
  exact Option.some.inj h

theorem member (r : Fin 1024) :
    (FJc_S2Rows.activeMask r.val >>> (r.val%16)) &&& 1=0 ↔ r∈R0P.copyInactiveRows := by
  rw [value r.val r.isLt]
  simp only [R0P.copyInactiveRows,Finset.mem_filter,Finset.mem_univ,true_and,R0P.CopyActiveRow,
    Nat.and_one_is_mod,Nat.shiftRight_eq_div_pow,Nat.testBit_eq_decide_div_mod_eq,decide_eq_true_eq]
  have h := Nat.mod_lt (R0P.copyActiveRowMasks ⟨r.val/16,by have:=r.isLt;omega⟩ / 2^(r.val%16)) (by decide : 0<2)
  omega

#print axioms member

#print axioms list
#print axioms value
end AspisR1.FJr_InactiveRegistry
