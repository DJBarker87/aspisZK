import NFQ_COMBINED_IMPORT
set_option autoImplicit false
namespace NFQ_StatementLaws
open Aeneas Aeneas.Std Result
open FIq_Native.pool_v1

def expected : pair_forest_semantic_terminal.CompiledVariant → U32
  | .PrivateTransfer => 1#u32 | .Withdrawal => 0#u32

def copied : pair_forest_semantic_terminal.CompiledVariant →
    pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1
  | .PrivateTransfer => .PrivateTransfer | .Withdrawal => .Withdrawal

theorem expected_reference (v : pair_forest_semantic_terminal.CompiledVariant) :
    pair_forest_semantic_terminal.variant_expected_output v=ok (expected v) := by
  cases v <;> rfl

theorem copied_reference (v : pair_forest_semantic_terminal.CompiledVariant) :
    pair_forest_semantic_terminal.copy_variant v=ok (copied v) := by
  cases v <;> rfl

theorem limbs_reference (v : FIq_Native.field.QM31) :
    FIq_Native.state_only_poseidon.extension_limbs v =
      ok (Array.make 4#usize [v.c0.a,v.c0.b,v.c1.a,v.c1.b]) := rfl
#print axioms expected_reference
#print axioms copied_reference
#print axioms limbs_reference
end NFQ_StatementLaws
