import R1Z.BuilderRecordsP6
import R1Z.BuilderBankMaterialization

/-! The D99 records route composed with full-bank materialization. The only
Parts hypothesis is its actual successful execution; its size is derived. -/
set_option autoImplicit false
namespace R1Z.BuilderRecordsBankStd
open Aeneas Aeneas.Std Result AspisBuilderRecordsReference
open pool_v1.pair_forest_copy_builder BuilderRecordsReference BuilderRecordsP6
open BuilderBankMaterialization

theorem route_std_table {w : RW} {p : RP} {input : Input} {out : U32} {rec : Option Note}
    {chg : Note} {s : Snapshot} {asset : U32} {empty : Roots}
    (p6 : Route w p input out rec chg s asset empty)
    (pt : AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.Parts)
    (hparts : AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.parts
      (bankWitness (witness input out rec chg)) (bankPublic (publicRecord rec s asset empty)) = ok pt) :
    ∃ merged, AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.merged_banks
      (bankWitness w) (bankPublic p) = ok (true,stableModel pt,lateModel pt,merged) ∧
      ∀ k, k < 16384 → merged.val[k]! = BuilderBankCells.cell pt (k/1024) (k%1024) := by
  rw [route_banks p6]
  exact banks_table _ _ pt hparts

#print axioms route_std_table
end R1Z.BuilderRecordsBankStd
