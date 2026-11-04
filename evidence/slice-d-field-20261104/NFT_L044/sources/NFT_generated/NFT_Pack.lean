import NFT_PackPrefix
set_option autoImplicit false
noncomputable section
namespace NFT_Pack
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev Q := field.QM31
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev Whole := AspisR1.ExtractedMaskQmPackBase4Whole.inputAt

def padded (values : Slice Q) (short : values.length≤4) : Array Q 4#usize :=
  Array.make 4#usize (values.val ++ List.replicate (4-values.length) field.QM31.ZERO)
    (hl := by simp only [List.length_append,List.length_replicate];change values.val.length≤4 at short;change values.val.length+(4-values.val.length)=4;omega)

def paddedSlice (values : Slice Q) (short : values.length≤4) : Slice Q :=
  Array.to_slice (padded values short)

theorem padded_length (values : Slice Q) (short : values.length≤4) :
    (paddedSlice values short).length=4 := by
  change (padded values short).val.length=4
  exact (padded values short).property

theorem padded_canonical (values : Slice Q) (short : values.length≤4)
    (canonical : ∀ q ∈ values.val, Canonical q) :
    ∀ j : Fin 4, Canonical (Whole (paddedSlice values short) (padded_length values short) j) := by
  have zero : Canonical field.QM31.ZERO := by
    simp [Canonical,AspisR1.ExtractedMaskTowerAdd.CanonicalQM,
      AspisR1.ExtractedMaskTowerAdd.CanonicalCM,field.QM31.ZERO,field.CM31.ZERO]
  have allpad : ∀ q ∈ (paddedSlice values short).val, Canonical q := by
    intro q member
    change q ∈ values.val ++ List.replicate (4-values.length) field.QM31.ZERO at member
    rcases List.mem_append.mp member with original | padding
    · exact canonical q original
    · rcases List.mem_replicate.mp padding with ⟨_,same⟩
      simpa only [same] using zero
  intro j
  apply allpad
  exact List.getElem_mem _

theorem graph (values : Slice Q) (short : values.length≤4) :
    field.qm31_pack_base4 values=AspisR1.ExtractedMaskQmPackBase4Tail.run
      (Whole (paddedSlice values short) (padded_length values short)) := by
  obtain ⟨copied,copyrun,contents⟩:=NFT_PackPrefix.source field.QM31.ZERO field.QM31.Insts.CoreMarkerCopy values short
  have same : copied.val=(paddedSlice values short).val := contents
  have hrun := AspisR1.ExtractedMaskQmPackBase4Whole.after_eq_run copied
    (paddedSlice values short) same (padded_length values short)
  have checked : massert (Slice.len values≤4#usize)=ok () := by
    apply (Aeneas.Std.massert_ok _).2
    exact short
  rw [AspisR1.ExtractedMaskQmPackBase4Whole.generated_eq_prefix_after]
  simp only [checked,copyrun,hrun,bind_tc_ok]

/-- Arbitrary 0..4-term inputs compose through the exact checked copy prelude
and the adopted four-term arithmetic tail, with explicit zero padding. -/
theorem source (values : Slice Q) (short : values.length≤4)
    (canonical : ∀ q ∈ values.val, Canonical q) :
    ∃ out : Q, field.qm31_pack_base4 values=ok out ∧ Canonical out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out=
        AspisR1.ExtractedMaskQmPackBase4Arithmetic.mathematicalPack
          (Whole (paddedSlice values short) (padded_length values short)) := by
  rw [graph values short]
  exact AspisR1.ExtractedMaskQmPackBase4Fragments.run_success _ (padded_canonical values short canonical)

#print axioms graph
#print axioms padded_length
#print axioms padded_canonical
#print axioms source
end NFT_Pack
