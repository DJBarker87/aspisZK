import R1Z.PV_Join_Wire_Op225
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry225
open Aeneas Aeneas.Std Result ProverRwFull PV_CB3_Op225Source
section
variable [ProverRwFull.ExternalTypes]
-- The extracted projection ignores both payloads. These total adapters are
-- data allowed by its original theorem, not representation assumptions.
def transfer : Transfer → Raw.Transfer := fun _ =>
  ⟨Array.make 32#usize (List.replicate 32 0#u8),
   Array.make 32#usize (List.replicate 32 0#u8), 0#u64,
   Array.make 8#usize (List.replicate 8 0#u32),
   Array.make 8#usize (List.replicate 8 0#u32), 0#u32,
   Array.make 8#usize (List.replicate 8 0#u32),
   Array.make 8#usize (List.replicate 8 0#u32)⟩
def withdrawal : Withdrawal → Raw.Withdrawal := fun _ =>
  ⟨Array.make 32#usize (List.replicate 32 0#u8),
   Array.make 32#usize (List.replicate 32 0#u8), 0#u64,
   Array.make 8#usize (List.replicate 8 0#u32),
   Array.make 8#usize (List.replicate 8 0#u32), 0#u32, 0#u32,
   Array.make 32#usize (List.replicate 32 0#u8),
   Array.make 8#usize (List.replicate 8 0#u32)⟩
end
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → Result
        aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun p => ProverRwP6TransitionSource.transition (toRaw transfer withdrawal p)
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op225 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext p
  exact R1Z.PV_Join_Wire_Op225.op225_source base ops transfer withdrawal p
#print axioms equation
end R1Z.PV_Join_Wire_Entry225
