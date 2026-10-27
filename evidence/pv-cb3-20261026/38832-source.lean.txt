import R1Z.PV_CB3_Op258RowLaw
import R1Z.PV_CB3_Op258Step
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op258ZeroMaskStep
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
abbrev Rows := Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize)

def IsZero (masks : Array U16 64#usize) : Prop :=
  ∀ i : Usize, i.val < 64 → Array.index_usize masks i = ok 0#u16

theorem and_zero (x : U16) : 0#u16 &&& x = 0#u16 := by
  apply UScalar.eq_of_val_eq
  change (0#16 &&& x.bv).toNat = 0
  simp only [BitVec.zero_and]
  rfl

theorem body (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (hz : IsZero masks) (clear : Bool) (row : Usize)
    (hr : row < Slice.len values) (hmask : row.val < 1024) :
    PV_CB3_Op258Ref.reference.all_slots_clear_loop.body values masks chi clear row =
      ok (cont (clear,Usize.wrapping_add row 1#usize)) := by
  have hm := hz (Usize.wrapping_shr row 4#u32) ((PV_CB3_MaskShift.in_bounds row).mpr hmask)
  obtain ⟨r,hrd⟩ : ∃ r, Slice.index_usize values row = ok r :=
    ⟨_,PV_CB3_PoleIndex.slice_read values row hr⟩
  obtain ⟨left,hl⟩ := PV_CB3_StagedComposition.read_total r 0#usize (by decide)
  obtain ⟨right,hri⟩ := PV_CB3_StagedComposition.read_total r 1#usize (by decide)
  obtain ⟨a,ha⟩ := PV_CB3_StagedComposition.read_total left 0#usize (by decide)
  obtain ⟨b,hb⟩ := PV_CB3_StagedComposition.read_total left 1#usize (by decide)
  obtain ⟨c,hc⟩ := PV_CB3_StagedComposition.read_total right 0#usize (by decide)
  obtain ⟨d,hd⟩ := PV_CB3_StagedComposition.read_total right 1#usize (by decide)
  have hs := PV_CB3_Op258RowLaw.body values masks chi a b c d row clear 0#u16 r left right
    hr hm hrd hl hri ha hb hc hd
  simpa [and_zero,PV_CB3_Op258RowLaw.clearRow] using hs
#print axioms and_zero
#print axioms body
end R1Z.PV_CB3_Op258ZeroMaskStep
