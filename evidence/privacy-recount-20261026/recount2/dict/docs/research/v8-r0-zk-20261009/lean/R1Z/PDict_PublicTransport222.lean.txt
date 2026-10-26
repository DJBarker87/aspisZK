import R1Z.PDict_Static222_09
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_PublicTransport222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap

theorem terminal (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base)
    (x : @Public base) (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize) (ch : aspis_core.state_only_prefix.r0.Challenges) :
    @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
      (types base F) (selected base F ops) (pub base F x) claims point ch =
    @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
      base ops x claims point ch := by
  change ops.op227 (unpublic base F (pub base F x)) claims point ch = ops.op227 x claims point ch
  rw [public_roundtrip]
#print axioms terminal
end R1Z.PDict_PublicTransport222
