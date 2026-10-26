/- Namespace port of BuilderPartsComplete: same symbolic proof, actual forest extraction. -/
import R1Z.PV_Src_Forest_BlockCollect
import R1Z.PV_Src_Forest_Columns

/-! The actual successful Parts computation supplies every canonical content
field. No Content or trace equality hypothesis is taken. -/
set_option autoImplicit false
namespace R1Z.PV_Src_Forest_PartsComplete
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_Src_Forest_PrimitiveArguments
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder

theorem content (w : RW) (p : RP) (pt : Parts) (hp : parts w p = ok pt) :
    PV_Src_Forest_PartsContent.Content pt (wordWitness w) (wordPublic p) where
  blocks := PV_Src_Forest_BlockCollect.parts_blocks w p pt hp
  path := PV_Src_Forest_PathContent.parts_path_content w p pt hp
  aux := PV_Src_Forest_AuxContent.parts_aux_content w p pt hp

theorem banks_columns (w : RW) (p : RP) (pt : Parts) (hp : parts w p = ok pt) :
    ∃ merged out,
      merged_banks w p = ok (true,PV_Src_Forest_BankMaterialization.stableModel pt,
        PV_Src_Forest_BankMaterialization.lateModel pt,merged) ∧
      BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder.columns merged = ok out ∧
      (∀ c, c < 16 → (out.val[c]!).val.length = 1024) ∧
      ∀ c r, PV_Src_Forest_Columns.read out c r = copyCellMerged (wordWitness w) (wordPublic p) c r :=
  PV_Src_Forest_Columns.source_banks_columns w p pt hp (wordWitness w) (wordPublic p) (content w p pt hp)

#print axioms content
#print axioms banks_columns
end R1Z.PV_Src_Forest_PartsComplete
