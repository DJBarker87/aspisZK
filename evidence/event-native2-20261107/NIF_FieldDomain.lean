import NIF_ByteDomain
import MultiproofConeSlices
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIF_FieldDomain
open Aeneas Aeneas.Std Result OraclePortCompactDraft MultiproofConeCanonical

theorem canonical_window (bytes : AspisV8R19.DuplexFrames.Bytes)
 (checked : canonical bytes) (offset width : Nat)
 (oa : offset%4=0) (wa : width%4=0) (bound : offset+width≤bytes.length) :
 canonical (slice bytes offset width) := by
 have tail := ((MultiproofConeCanonicalAppend.canonical_take_drop bytes offset oa (by omega)).mp checked).2
 exact ((MultiproofConeCanonicalAppend.canonical_take_drop (bytes.drop offset) width wa
  (by simp only [List.length_drop];omega)).mp tail).1

/-- No successful decoder premise: each fixed32 part in the canonical128
window satisfies all eight natural limb bounds required by the emitted parser. -/
theorem selected (bytes : Slice U8) (size : bytes.val.length=128)
 (checked : canonical (bytesOf bytes.val)) (s : Nat) (inside : s<4)
 (part : Array U8 32#usize) (same : part.val=(bytes.val.drop (32*s)).take 32) :
 NIF_WideBytes.Canonical part := by
 apply NIF_ByteDomain.fixed32
 have window := canonical_window (bytesOf bytes.val) checked (32*s) 32
  (by omega) (by decide) (by simp only [bytesOf,List.length_map];omega)
 simpa only [bytesOf,same,List.map_take,List.map_drop,slice] using window

/-- Construct the exact native decoder result from canonical input bytes. -/
theorem read_total (bytes : Slice U8) (size : bytes.val.length=128)
 (checked : canonical (bytesOf bytes.val)) (i : Usize) (inside : i.val<4) :
 ∃ value, FIo_Native.weights.field bytes i=ok value := by
 have capacity : 128<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 let start := Usize.wrapping_mul i 32#usize
 let finish := Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize
 have sv : start.val=32*i.val := by
  change (Usize.wrapping_mul i 32#usize).val=_
  simp only [Usize.wrapping_mul_val_eq,show (32#usize).val=32 from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
 have fv : finish.val=32*(i.val+1) := by
  have next : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
   simp only [Usize.wrapping_add_val_eq,show (1#usize).val=1 from rfl]
   rw [Nat.mod_eq_of_lt (by omega)]
  change (Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize).val=_
  simp only [Usize.wrapping_mul_val_eq,next,show (32#usize).val=32 from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
 let part : Array U8 32#usize := ⟨(bytes.val.drop (32*i.val)).take 32,by
  change ((bytes.val.drop (32*i.val)).take 32).length=32
  simp only [List.length_take,List.length_drop];omega⟩
 have hc := selected bytes size checked i.val inside part rfl
 have read := MultiproofConeSlices.range_total bytes start finish (by omega) (by omega)
 have same : MultiproofConeSlices.sub bytes start finish=part.to_slice := by
  apply Subtype.ext
  simp only [MultiproofConeSlices.sub,List.slice,Array.to_slice,sv,fv,part]
  congr 1
  omega
 refine ⟨NIF_WideBytes.decode part,?_⟩
 unfold FIo_Native.weights.field
 simp only [lift,bind_tc_ok]
 rw [read,same]
 simp only [bind_tc_ok]
 rw [NIF_WideBytes.bytes_some part hc]
 rfl
#print axioms read_total
#print axioms canonical_window
#print axioms selected
end AspisR1.NIF_FieldDomain
