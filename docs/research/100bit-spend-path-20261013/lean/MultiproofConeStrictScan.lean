import MultiproofConeCompactScan
import MultiproofConeSliceComposition

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeStrictScan
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft
open MultiproofConeCanonical MultiproofConeSlices MultiproofConeBool
open MultiproofConeOpeningRows MultiproofConeSliceComposition
attribute [local instance] Classical.propDecidable

/-- Complete extracted strict scanner at the actual frozen stored length.
The length is supplied by header admission, not a canonical-input hypothesis. -/
theorem scan_total (bytes : Slice U8) (length : bytes.val.length = 57607) :
    MultiproofParserRef.parser_reference.scan bytes =
      ok (decide (scan (bytesOf bytes.val))) := by
  have hl : Slice.len bytes = 57607#usize := UScalar.eq_of_val_eq length
  have b7495 : (7495#usize).val ≤ bytes.val.length := by change 7495 ≤ bytes.val.length; omega
  have b7751 : (7751#usize).val ≤ bytes.val.length := by change 7751 ≤ bytes.val.length; omega
  have b10055 : (10055#usize).val ≤ bytes.val.length := by change 10055 ≤ bytes.val.length; omega
  have b28359 : (28359#usize).val ≤ bytes.val.length := by change 28359 ≤ bytes.val.length; omega
  have ylen : (sub bytes 7031#usize 7495#usize).val.length = 464 := by
    rw [sub_length bytes 7031#usize 7495#usize (by scalar_tac) b7495]
    rfl
  have yscan := MultiproofConeCompactScan.check_values_total (sub bytes 7031#usize 7495#usize)
    (by rw [ylen])
  have olen : (sub bytes 10055#usize 28359#usize).val.length = 832*(22#u8).val := by
    rw [sub_length bytes 10055#usize 28359#usize (by scalar_tac) b28359]
    rfl
  have oscan := rows_total (sub bytes 10055#usize 28359#usize) 22#u8 olen
  rw [MultiproofParserRef.parser_reference.scan]
  simp only [hl,bne_self_eq_false,Bool.false_eq_true,if_false,
    range_total bytes 7031#usize 7495#usize (by scalar_tac) b7495,
    range_total bytes 7495#usize 7751#usize (by scalar_tac) b7751,
    range_total bytes 7783#usize 10055#usize (by scalar_tac) b10055,
    range_total bytes 10055#usize 28359#usize (by scalar_tac) b28359,
    bind_tc_ok,yscan,MultiproofConeCanonical.scan_total,oscan,decide_eq_true_eq,result_if_conj]
  apply result_decide_congr
  simp only [bytes_sub,
    show (7031#usize).val=7031 from rfl,show (7495#usize).val=7495 from rfl,
    show (7751#usize).val=7751 from rfl,show (7783#usize).val=7783 from rfl,
    show (10055#usize).val=10055 from rfl,show (28359#usize).val=28359 from rfl,
    show (22#u8).val=22 from rfl,
    show 7495-7031=464 from rfl,show 7751-7495=256 from rfl,
    show 10055-7783=2272 from rfl,show 28359-10055=18304 from rfl]
  have openings : AllOpenings 22 (slice (bytesOf bytes.val) 10055 18304) ↔
      ∀ j ∈ List.range 22, openingCanonical (slice (bytesOf bytes.val) (10055+j*832) 832) := by
    change AllOpenings 22 (slice (bytesOf bytes.val) 10055 (832*22)) ↔ _
    rw [all_slice]
    simp only [List.mem_range,Nat.mul_comm]
  simp only [openings,scan]

#print axioms scan_total
end AspisR1.MultiproofConeStrictScan
end
