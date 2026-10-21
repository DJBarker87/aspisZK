import R1Z.BuilderBlockCollect
import R1Z.BuilderColumns

/-! The actual successful Parts computation supplies every canonical content
field. No Content or trace equality hypothesis is taken. -/
set_option autoImplicit false
namespace R1Z.BuilderPartsComplete
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderPrimitiveArguments
open AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder

theorem content (w : RW) (p : RP) (pt : Parts) (hp : parts w p = ok pt) :
    BuilderPartsContent.Content pt (wordWitness w) (wordPublic p) where
  blocks := BuilderBlockCollect.parts_blocks w p pt hp
  path := BuilderPathContent.parts_path_content w p pt hp
  aux := BuilderAuxContent.parts_aux_content w p pt hp

theorem banks_columns (w : RW) (p : RP) (pt : Parts) (hp : parts w p = ok pt) :
    ∃ merged out,
      merged_banks w p = ok (true,BuilderBankMaterialization.stableModel pt,
        BuilderBankMaterialization.lateModel pt,merged) ∧
      AspisBuilderColumnsSource.pool_v1.pair_forest_copy_builder.columns merged = ok out ∧
      (∀ c, c < 16 → (out.val[c]!).val.length = 1024) ∧
      ∀ c r, BuilderColumns.read out c r = copyCellMerged (wordWitness w) (wordPublic p) c r :=
  BuilderColumns.source_banks_columns w p pt hp (wordWitness w) (wordPublic p) (content w p pt hp)

#print axioms content
#print axioms banks_columns
end R1Z.BuilderPartsComplete
