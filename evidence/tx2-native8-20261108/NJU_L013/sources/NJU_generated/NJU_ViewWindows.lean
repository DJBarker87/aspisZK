import NJU_BadWindow
set_option autoImplicit false
namespace NJU_ViewWindows
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- An entered final View construction supplies this bound internally. -/
theorem entered_size (proof selected : Slice U8)
 (read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=8007#usize,«end»:=10055#usize}=ok selected) :
 10055≤proof.val.length := (PSem_Slices.range_bounds proof selected _ _ read).2

theorem lengths (proof : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact)
 (size : 10055≤proof.val.length) :
 (NJR_ViewFinish.view proof inactive).round0.val.length=224 ∧
 (NJR_ViewFinish.view proof inactive).round1.val.length=224 ∧
 (NJR_ViewFinish.view proof inactive).final_message.val.length=2048 := by
 change ((proof.val.drop 7527).take 224).length=224 ∧
  ((proof.val.drop 7783).take 224).length=224 ∧
  ((proof.val.drop 8007).take 2048).length=2048
 simp only [List.length_take,List.length_drop]
 omega

/-- Once the actual source has built the View, a failing window is a bad
word in one of the three actual slices. A short slice aborts earlier at the
View construction and is not assumed away by a proof-persistence premise. -/
theorem bad_current (proof : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact)
 (size : 10055≤proof.val.length)
 (bad : ¬ NJU_CurrentWindows.Holds (NJR_ViewFinish.view proof inactive)) :
 (∃ i,i<7 ∧ ∃ j,j<8 ∧ 2147483647≤NIG_FinishInput.word
  (NJR_ViewFinish.view proof inactive).round0.val (32*i+4*j)) ∨
 (∃ i,i<7 ∧ ∃ j,j<8 ∧ 2147483647≤NIG_FinishInput.word
  (NJR_ViewFinish.view proof inactive).round1.val (32*i+4*j)) ∨
 (∃ i,i<64 ∧ ∃ j,j<8 ∧ 2147483647≤NIG_FinishInput.word
  (NJR_ViewFinish.view proof inactive).final_message.val (32*i+4*j)) := by
 obtain ⟨s0,s1,sf⟩:=lengths proof inactive size
 by_cases h0 : NIG_FinishInput.Windows (NJR_ViewFinish.view proof inactive).round0 7
 · by_cases h1 : NIG_FinishInput.Windows (NJR_ViewFinish.view proof inactive).round1 7
   · right;right
     apply NJU_BadWindow.witness _ 64 sf
     intro hf
     exact bad ⟨h0,h1,hf⟩
   · exact Or.inr (Or.inl (NJU_BadWindow.witness _ 7 s1 h1))
 · exact Or.inl (NJU_BadWindow.witness _ 7 s0 h0)

#print axioms entered_size
#print axioms lengths
#print axioms bad_current
end NJU_ViewWindows
