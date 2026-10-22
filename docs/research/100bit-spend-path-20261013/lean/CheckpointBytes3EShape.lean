import CheckpointBytes3ScalarShape

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes3EShape
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted OraclePortCkptAbi4Decode CheckpointBytes3ScalarShape
attribute [local instance] Classical.propDecidable

def eWords (w : Fin 8 → U32) : aspis_core.field.wide_exact.WideExact :=
  ⟨kWords (w 0) (w 1) (w 2) (w 3),kWords (w 4) (w 5) (w 6) (w 7)⟩

theorem from_limbs_shape (w : Fin 8 → U32) :
    aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [w 0,w 1,w 2,w 3,w 4,w 5,w 6,w 7]) =
      if CanonicalWide (eWords w) then ok (some (eWords w)) else ok none := by
  simp only [aspis_core.field.wide_exact.WideExact.from_limbs,Array.index_usize,
    aspis_core.field.P]
  simp [Array.make]
  split <;> simp_all [CanonicalWide,Canonical,eWords,kWords]
  split <;> simp_all [CanonicalWide,Canonical,eWords,kWords]
  split <;> simp_all [CanonicalWide,Canonical,eWords,kWords]
  split <;> simp_all [CanonicalWide,Canonical,eWords,kWords]
  split <;> simp_all [CanonicalWide,Canonical,eWords,kWords]
  split <;> simp_all [CanonicalWide,Canonical,eWords,kWords]
  split <;> simp_all [CanonicalWide,Canonical,eWords,kWords]
  split <;> simp_all [CanonicalWide,Canonical,eWords,kWords]

theorem e_shape (b : Slice U8) (width : b.val.length = 32) (w : Fin 8 → U32)
    (h0 : word_spec b 0#usize = ok (w 0))
    (h1 : word_spec b 4#usize = ok (w 1))
    (h2 : word_spec b 8#usize = ok (w 2))
    (h3 : word_spec b 12#usize = ok (w 3))
    (h4 : word_spec b 16#usize = ok (w 4))
    (h5 : word_spec b 20#usize = ok (w 5))
    (h6 : word_spec b 24#usize = ok (w 6))
    (h7 : word_spec b 28#usize = ok (w 7)) :
    decode_e_spec b = if CanonicalWide (eWords w) then ok (some (eWords w)) else ok none := by
  unfold decode_e_spec
  have len : Slice.len b = 32#usize := by
    apply UScalar.eq_of_val_eq
    simpa [Slice.len,Slice.length] using width
  rw [len]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    h0,h1,h2,h3,h4,h5,h6,h7,bind_tc_ok]
  exact from_limbs_shape w

#print axioms from_limbs_shape
#print axioms e_shape
end AspisR1.CheckpointBytes3EShape
end
