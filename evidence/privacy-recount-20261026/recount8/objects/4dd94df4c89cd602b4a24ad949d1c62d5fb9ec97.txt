import R1Z.BuilderTreeCarryExtracted
open Aeneas Aeneas.Std Result
namespace AspisBuilderTreeReference
/-- [aspis_statement::pool_v1::incremental_merkle::tree_reference::carry_step_owned]:
    Source: 'crates/aspis-statement/src/pool_v1/../../../../tools/r1-builder-reference/tree.rs', lines 95:0-99:1
    Visibility: public -/
def pool_v1.incremental_merkle.tree_reference.carry_step_owned
  {H : Type} (coreopsfunctionFnMutHPairArrayM318ArrayM318ArrayM318Inst :
  core.ops.function.FnMut H ((Array aspis_core.field.M31 8#usize) × (Array
  aspis_core.field.M31 8#usize)) (Array aspis_core.field.M31 8#usize))
  (frontier_node : Array aspis_core.field.M31 8#usize)
  (empty_node : Array aspis_core.field.M31 8#usize)
  (carry : Array aspis_core.field.M31 8#usize) (level : Std.Usize) (parent : H)
  :
  Result ((Array aspis_core.field.M31 8#usize) × (Array aspis_core.field.M31
    8#usize) × Std.Usize)
  := do
  let (a, _) ←
    coreopsfunctionFnMutHPairArrayM318ArrayM318ArrayM318Inst.call_mut parent
      (frontier_node, carry)
  let i ← lift (Std.Usize.wrapping_add level 1#usize)
  ok (a, empty_node, i)

end AspisBuilderTreeReference
