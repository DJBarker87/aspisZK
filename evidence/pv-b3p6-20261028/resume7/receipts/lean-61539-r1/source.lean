import PV_B3P_PatternSuccess227
import PV_B3P_LinkBounds227
import PV_B3P_ActiveSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem widen_u16 (x : U16) : (core.convert.num.FromUsizeU16.from x).val=x.val := by
  change (UScalar.cast .Usize x).val=x.val
  simp only [UScalar.cast_val_eq,UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> scalar_tac

theorem row_high (row : Usize) (hr : row.val<1024) :
    (Usize.wrapping_shr row 4#u32).val<64 := by
  change (row.bv.ushiftRight ((4#u32).val % UScalarTy.Usize.numBits)).toNat<64
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have hmod : (4#u32).val % UScalarTy.Usize.numBits=4 := by
    rw [UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> rfl
  rw [hmod]
  change row.val/16<64
  omega

theorem row_low (row : Usize) : (row &&& 15#usize).val<16 := by
  rw [UScalar.val_and]
  change row.val &&& 15 < 16
  exact lt_of_le_of_lt (Nat.and_le_right (n:=row.val) (m:=15)) (by omega)

theorem row_total (selectors : reference_copy_terminal.Selectors) (row : Usize)
    (hr : row.val<1024) : Success (reference_copy_terminal.Selectors.row selectors row) := by
  unfold reference_copy_terminal.Selectors.row
  simp only [lift,bind_tc_ok]
  apply bind
  · exact index selectors.high _ (row_high row hr)
  intro high
  apply bind
  · exact index selectors.low _ (row_low row)
  intro low
  exact qmul high low

#print axioms widen_u16
#print axioms row_high
#print axioms row_low
#print axioms row_total

theorem endpoint_total (values weights : Array aspis_core.field.QM31 2#usize)
    (endpoint : reference_copy_terminal.CompiledPoolV1PairForestEndpoint)
    (tag weight : U32) (patterns : Array aspis_core.field.QM31 14#usize)
    (selectors : reference_copy_terminal.Selectors) (he : EndpointSafe endpoint) :
    Success (reference_copy_terminal.accumulate_endpoint values weights endpoint tag weight patterns selectors) := by
  unfold reference_copy_terminal.accumulate_endpoint
  simp only [lift,bind_tc_ok]
  apply bind
  · apply row_total
    rw [widen_u16]
    exact he.1
  intro selector
  apply bind
  · apply index
    rw [widen_u8]
    exact he.2.1
  intro oldweight
  apply bind
  · exact qmul_m31 selector weight
  intro weighted
  apply bind
  · exact qadd oldweight weighted
  intro newweight
  apply bind
  · apply update
    rw [widen_u8]
    exact he.2.1
  intro weights1
  apply bind
  · exact ⟨_,rfl⟩
  intro lifted
  apply bind
  · apply index
    rw [widen_u8]
    exact he.2.2
  intro pattern
  apply bind
  · exact qadd lifted pattern
  intro compressed
  apply bind
  · apply index
    rw [widen_u8]
    exact he.2.1
  intro oldvalue
  apply bind
  · exact qmul selector compressed
  intro contribution
  apply bind
  · exact qadd oldvalue contribution
  intro newvalue
  apply bind
  · apply update
    rw [widen_u8]
    exact he.2.1
  intro values1
  exact ok _

#print axioms endpoint_total

theorem weight_total (link : reference_copy_terminal.CompiledPoolV1PairForestLink)
    (append_index : U64) (variant : reference_copy_terminal.PoolV1PairForestCompiledVariantV1)
    (hw : link.weight_kind.val≤4) :
    Success (reference_copy_terminal.link_weight link append_index variant) := by
  have hc : link.weight_kind.val=0 ∨ link.weight_kind.val=1 ∨ link.weight_kind.val=2 ∨ link.weight_kind.val=3 ∨ link.weight_kind.val=4 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4
  · have hk : link.weight_kind=0#u8 := UScalar.eq_of_val_eq h0
    simp only [reference_copy_terminal.link_weight,hk]
    exact ⟨_,rfl⟩
  · have hk : link.weight_kind=1#u8 := UScalar.eq_of_val_eq h1
    simp only [reference_copy_terminal.link_weight,hk]
    exact ⟨_,rfl⟩
  · have hk : link.weight_kind=2#u8 := UScalar.eq_of_val_eq h2
    simp only [reference_copy_terminal.link_weight,hk]
    exact ⟨_,rfl⟩
  · have hk : link.weight_kind=3#u8 := UScalar.eq_of_val_eq h3
    simp only [reference_copy_terminal.link_weight,hk]
    exact ⟨_,rfl⟩
  · have hk : link.weight_kind=4#u8 := UScalar.eq_of_val_eq h4
    simp only [reference_copy_terminal.link_weight,hk]
    exact ⟨_,rfl⟩

#print axioms weight_total
end PV_B3P_Success227
