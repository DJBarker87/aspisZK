import R1Z.BuilderBankMaterialization
import R0Z.BuilderWitnessMerged

/-! Componentwise handoff from Parts to the canonical writer. Content is
an explicit remaining callee obligation, not a source runtime inhabitant. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderPartsContent
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder
attribute [local instance] Classical.propDecidable

structure Content (pt : Parts) (w : RustWitness) (p : RustPublic) : Prop where
  blocks : ∀ h, h < 57 → pt.blocks.val[h]! = blockR w p h
  path : pt.path = okOr (pathR w p) (Array.repeat 1536#usize 0#u32)
  aux : pt.aux = okOr (auxR w p) (Array.repeat 256#usize 0#u32)

theorem cell_eq (pt : Parts) (w : RustWitness) (p : RustPublic)
    (hc : Content pt w p) (c : Fin 29) (r : Fin 1024) :
    BuilderBankCells.cell pt c.val r.val = copyCell w p c r := by
  unfold BuilderBankCells.cell copyCell
  split
  · split
    · rw [hc.blocks (r.val/16) (by omega)]
    · split
      · rw [hc.path]
      · rw [hc.aux]
  · rfl

/-- Bank splitting and merging preserves every canonical raw cell for all
records, independently of semantic admission. -/
theorem canonical_merge_cell (w : RustWitness) (p : RustPublic)
    (c : Fin 29) (r : Fin 1024) :
    copyCellMerged w p c r = copyCell w p c r := by
  let M : Nat → U32 := fun k => if h : k < 16384 then cellT w p ⟨k,h⟩ else 0#u32
  have hs : ∀ k, k < 16384 → (stableBank w p).val[k]! = if LateRow k then 0#u32 else M k := by
    intro k hk
    rw [stableBank,arrT_get _ k hk]
    dsimp only [M]
    rw [dif_pos hk]
  have hl : ∀ k, k < 16384 → (lateBank w p).val[k]! = if LateRow k then M k else 0#u32 := by
    intro k hk
    rw [lateBank,arrT_get _ k hk]
    dsimp only [M]
    rw [dif_pos hk]
    by_cases hr : LateRow k
    · rw [if_pos hr,if_pos hr]
      unfold LateRow at hr
      unfold cellT copyCell
      dsimp only
      rw [if_pos (show k/1024 < 16 by omega),if_pos (show k%1024 < 912 by omega)]
    · rw [if_neg hr,if_neg hr]
  obtain ⟨_,out,hout,hcells⟩ := merge_model M (stableBank w p) (lateBank w p) hs hl
  by_cases hc : c.val < 16
  · have hk : c.val*1024+r.val < 16384 := by have := r.isLt; omega
    unfold copyCellMerged
    rw [if_pos hc,show mergedR w p = ok out from hout,okOr_ok,hcells _ hk]
    dsimp only [M]
    rw [dif_pos hk]
    unfold cellT
    have h1 : (⟨(c.val*1024+r.val)/1024,by omega⟩ : Fin 29) = c := by
      apply Fin.ext; dsimp; have := r.isLt; omega
    have h2 : (⟨(c.val*1024+r.val)%1024,Nat.mod_lt _ (by omega)⟩ : Fin 1024) = r := by
      apply Fin.ext; dsimp; have := r.isLt; omega
    rw [h1,h2]
  · unfold copyCellMerged copyCell
    rw [if_neg hc,if_neg hc]

/-- Column-major readout with the thirteen padding columns made explicit. -/
def columnCell (flat : Array U32 16384#usize) (c : Fin 29) (r : Fin 1024) : U32 :=
  if c.val < 16 then flat.val[c.val*1024+r.val]! else 0#u32

theorem banks_columns (rw : RW) (rp : RP) (pt : Parts)
    (hp : parts rw rp = ok pt) (w : RustWitness) (p : RustPublic)
    (hc : Content pt w p) :
    ∃ merged, merged_banks rw rp = ok (true,BuilderBankMaterialization.stableModel pt,
      BuilderBankMaterialization.lateModel pt,merged) ∧
      ∀ c r, columnCell merged c r = copyCellMerged w p c r := by
  obtain ⟨merged,hm,hcells⟩ := BuilderBankMaterialization.banks_table rw rp pt hp
  refine ⟨merged,hm,fun c r => ?_⟩
  rw [canonical_merge_cell]
  unfold columnCell
  by_cases h : c.val < 16
  · rw [if_pos h,hcells _ (by have := r.isLt; omega)]
    have hd : (c.val*1024+r.val)/1024 = c.val := by have := r.isLt; omega
    have hr : (c.val*1024+r.val)%1024 = r.val := by have := r.isLt; omega
    rw [hd,hr]
    exact cell_eq pt w p hc c r
  · rw [if_neg h]
    unfold copyCell
    rw [if_neg h]

#print axioms cell_eq
#print axioms canonical_merge_cell
#print axioms banks_columns
end R1Z.BuilderPartsContent
