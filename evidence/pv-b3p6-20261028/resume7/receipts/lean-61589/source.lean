import PV_B3P_AbsorptionSuccess227
import PV_B3P_CopyBasicsSuccess227
import PV_B3P_PreweightedSuccess227
import PV_B3P_PoseidonCellsSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem wrap_add_bound (x y : Usize) (n : Nat) (h : x.val+y.val<n) :
    (Usize.wrapping_add x y).val<n := by
  rw [Usize.wrapping_add_val_eq]
  exact lt_of_le_of_lt (Nat.mod_le _ _) h

theorem row_mul_bound (block : Usize) (hb : block.val<64) :
    (Usize.wrapping_mul block 16#usize).val<1024 := by
  rw [Usize.wrapping_mul_val_eq]
  change (block.val*16) % UScalar.size .Usize < 1024
  have hm := Nat.mod_le (block.val*16) (UScalar.size .Usize)
  omega

theorem row_address_bound (block offset : Usize) (hb : block.val<64) (ho : offset.val<16) :
    (Usize.wrapping_add (Usize.wrapping_mul block 16#usize) offset).val<1024 := by
  rw [Usize.wrapping_add_val_eq,Usize.wrapping_mul_val_eq]
  change ((block.val*16) % UScalar.size .Usize+offset.val) % UScalar.size .Usize < 1024
  have hm := Nat.mod_le (block.val*16) (UScalar.size .Usize)
  have ha := Nat.mod_le ((block.val*16) % UScalar.size .Usize+offset.val) (UScalar.size .Usize)
  omega

theorem checked_mul_exact (x y z : Usize) (h : x.val*y.val=z.val) :
    (x*y : Result Usize)=.ok z := by
  obtain ⟨s,hs,hval⟩ := WP.spec_imp_exists
    (UScalar.mul_spec (x:=x) (y:=y) (by rw [h]; scalar_tac))
  have heq : s=z := UScalar.eq_of_val_eq (by omega)
  simpa only [heq] using hs

theorem input_row_value : reference_terminal.INPUT_OCCUPANCY_ROW=.ok 1017#usize := by
  unfold reference_terminal.INPUT_OCCUPANCY_ROW
  rw [checked_mul_exact 63#usize 16#usize 1008#usize (by change 63*16=1008; rfl)]
  simp only [bind_tc_ok]
  exact checked_add_exact _ _ _ (by change 1008+9=1017; rfl)

theorem output_row_value : reference_terminal.OUTPUT_OCCUPANCY_ROW=.ok 1018#usize := by
  unfold reference_terminal.OUTPUT_OCCUPANCY_ROW
  rw [checked_mul_exact 63#usize 16#usize 1008#usize (by change 63*16=1008; rfl)]
  simp only [bind_tc_ok]
  exact checked_add_exact _ _ _ (by change 1008+10=1018; rfl)

theorem input_row_bind {α : Type} (f : Usize → Result α)
    (h : Success (f 1017#usize)) : Success (reference_terminal.INPUT_OCCUPANCY_ROW >>= f) := by
  rw [input_row_value]
  exact h

theorem output_row_bind {α : Type} (f : Usize → Result α)
    (h : Success (f 1018#usize)) : Success (reference_terminal.OUTPUT_OCCUPANCY_ROW >>= f) := by
  rw [output_row_value]
  exact h

theorem tweak_total (value : U32) (right_tweak : Bool) (lane : Usize) :
    Success (reference_terminal.tweak227 value right_tweak lane) := by
  unfold reference_terminal.tweak227
  split
  · apply lift_total
    split
    · exact add value _
    · exact ok value
  · exact ok value

theorem variant_output_total (variant : reference_terminal.CompiledVariant) :
    Success (reference_terminal.variant_expected_output variant) := by
  cases variant <;> exact ⟨_,rfl⟩

theorem scalar_total (variant : reference_terminal.CompiledVariant) (present : Bool)
    (input_asset output_scalar private_transfer_term withdrawal_term : aspis_core.field.QM31) :
    Success (reference_terminal.scalar_lanes variant present input_asset output_scalar private_transfer_term withdrawal_term) := by
  cases variant with
  | PrivateTransfer =>
    unfold reference_terminal.scalar_lanes
    apply bind
    · exact qadd output_scalar private_transfer_term
    intro value
    exact ok _
  | Withdrawal =>
    cases present with
    | false => exact ok _
    | true =>
      unfold reference_terminal.scalar_lanes
      apply bind
      · exact qadd output_scalar withdrawal_term
      intro value
      exact ok _

theorem copy_variant_total (variant : reference_terminal.CompiledVariant) :
    Success (reference_terminal.copy_variant variant) := by
  cases variant <;> exact ⟨_,rfl⟩

theorem digest_total (values : Array (Array U32 8#usize) 20#usize)
    (i : Usize) (hi : i.val<20) : Success (reference_terminal.digest227 values i) := index values i hi

theorem empty_root_total (level : Usize) (hi : level.val<21) :
    Success (reference_terminal.empty_root level) := by
  unfold reference_terminal.empty_root
  apply bind
  · exact index _ level hi
  intro words
  apply bind
  · apply index <;> scalar_tac
  intro word0
  apply bind
  · apply index <;> scalar_tac
  intro word1
  apply bind
  · apply index <;> scalar_tac
  intro word2
  apply bind
  · apply index <;> scalar_tac
  intro word3
  apply bind
  · apply index <;> scalar_tac
  intro word4
  apply bind
  · apply index <;> scalar_tac
  intro word5
  apply bind
  · apply index <;> scalar_tac
  intro word6
  apply bind
  · apply index <;> scalar_tac
  intro word7
  exact ok _

#print axioms wrap_add_bound
#print axioms row_mul_bound
#print axioms row_address_bound
#print axioms checked_mul_exact
#print axioms input_row_value
#print axioms output_row_value
#print axioms input_row_bind
#print axioms output_row_bind
#print axioms tweak_total
#print axioms variant_output_total
#print axioms scalar_total
#print axioms copy_variant_total
#print axioms digest_total
#print axioms empty_root_total
end PV_B3P_Success227
