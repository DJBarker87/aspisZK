import RPv_FJa_ArrayUpdate
import RPv_FJa_ReverseStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_SplitStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIv_PreparedNew (NP)
open FIw_ArrayValue (canonical)
abbrev Loop {N : Usize} := pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0 (N:=N)
/-- Invert a successful ORIGINAL split iteration; its arithmetic and both
writes preserve canonicality. No new whole-loop success premise is introduced. -/
theorem value {N : Usize} (weights out : Array NQ N) (p : NP) (c : NQ)
    (iter tail : FJa_ReverseStep.Rev) (index : Usize)
    (hc : Canon c) (hw : canonical weights)
    (hp : field.PreparedQm31Multiplier.new c=ok p)
    (hn : FJa_ReverseStep.next iter=ok (some index,tail))
    (run : Loop iter weights p=ok out) :
    ∃ (parent right left : NQ) (i i1 : Usize) (middle afterWrite : Array NQ N),
      Array.index_usize weights index=ok parent ∧
      field.PreparedQm31Multiplier.mul p parent=ok right ∧
      field.QM31.sub parent right=ok left ∧
      2#usize*index=ok i ∧ Array.update weights i left=ok middle ∧
      i+1#usize=ok i1 ∧ Array.update middle i1 right=ok afterWrite ∧
      canonical afterWrite ∧
      decode left+decode right=decode parent ∧
      Loop tail afterWrite p=ok out := by
  change pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0 iter weights p=ok out at run
  rw [pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0.eq_def] at run
  unfold FJa_ReverseStep.next at hn
  rw [hn] at run
  simp only [bind_tc_ok] at run
  obtain ⟨parent,hparent,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨right,hright,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨left,hleft,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨i,hi,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨middle,hmiddle,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨i1,hi1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨afterWrite,hafter,run⟩ := FIv_Map.bind_success _ _ _ run
  have hpc := FIv_NativeArray.canonical weights index parent hw hparent
  have v := FIz_SelectorSplit.value c parent right left p hc hpc hp hright hleft
  have cm := FJa_ArrayUpdate.canonical_write weights middle i left hw v.2.1 hmiddle
  have ca := FJa_ArrayUpdate.canonical_write middle afterWrite i1 right cm v.1 hafter
  exact ⟨parent,right,left,i,i1,middle,afterWrite,hparent,hright,hleft,hi,hmiddle,hi1,hafter,ca,v.2.2.2.2,run⟩
#print axioms value
end AspisR1.FJa_SplitStep
end
