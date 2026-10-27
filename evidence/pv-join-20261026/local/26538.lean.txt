import R1Z.ProverRwFullExternalTypes
open Aeneas Aeneas.Std

namespace PV_CB3_ShippedOp229
abbrev aspis_core.field.M31 := Std.U32

/-- Concrete carrier from aeneas-source-op229-001/Types.lean.txt. -/
structure aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 where
  next_pair_index : Std.U64
  next_root : Array aspis_core.field.M31 8#usize
  next_frontier : Array (Array aspis_core.field.M31 8#usize) 20#usize
end PV_CB3_ShippedOp229

namespace R1Z.PV_CB3_Afterstate
set_option autoImplicit false
open ProverRwFull
/-- Concrete extracted carrier selection; no field/representation premise. -/
@[reducible] def selectedTypes (base : ExternalTypes) : ExternalTypes :=
  {base with op20 := PV_CB3_ShippedOp229.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1}

theorem carrier (base : ExternalTypes) :
    @ExternalTypes.op20 (selectedTypes base) =
      PV_CB3_ShippedOp229.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 := rfl
#print axioms carrier
end R1Z.PV_CB3_Afterstate
