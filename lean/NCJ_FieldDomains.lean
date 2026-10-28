import NBQ_FieldTotal
import NCJ_TensorDomains
set_option autoImplicit false
noncomputable section
namespace NCJ_FieldDomains
open Aeneas Aeneas.Std Result AspisR1

theorem final_window (bytes : Slice U8) (size : bytes.val.length = 2048)
    (j : Usize) (bound : j.val < 64) :
    ∃ part : Array U8 32#usize,
      part.val=(bytes.val.drop (32*j.val)).take 32 ∧
      FIo_Native.weights.field bytes j = (do
        let decoded ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
          (NBG_WideBytes.limbs part)
        core.option.Option.unwrap decoded) :=
  NBQ_FieldTotal.range bytes j (by rw [size];omega)

theorem polynomial_window (bytes : Slice U8) (size : bytes.val.length = 224)
    (j : Usize) (bound : j.val < 7) :
    ∃ part : Array U8 32#usize,
      part.val=(bytes.val.drop (32*j.val)).take 32 ∧
      FIo_Native.weights.field bytes j = (do
        let decoded ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
          (NBG_WideBytes.limbs part)
        core.option.Option.unwrap decoded) :=
  NBQ_FieldTotal.range bytes j (by rw [size];omega)

theorem partial_index (s j : Nat) (hs : s<4) (hj : j<16) : 16*s+j<64 := by omega

theorem partial_partition (i : Nat) (h : i<64) :
    i/16<4 ∧ i%16<16 ∧ 16*(i/16)+i%16=i := by omega

theorem low_indices (s : Nat) (h : s<16) : s%4<4 ∧ s/4<4 := by omega

theorem point_indices (d : Nat) (h : d<5) (tau : Nat) (ht : tau<5) :
    9-2*tau<10 ∧ 8-2*tau<10 ∧ 2*tau≤8 := by omega

#print axioms final_window
#print axioms polynomial_window
#print axioms partial_index
#print axioms partial_partition
#print axioms low_indices
#print axioms point_indices
end NCJ_FieldDomains
