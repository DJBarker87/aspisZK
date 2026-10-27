import R1Z.PDict_CopyCaller222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Pointwise structural transport for `host_semantic.no_pole`. -/
theorem erase_249 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) (h12 : PDict_MapErrTransport222.MapErrLaw base ops) :
    letI : ExternalTypes := base
    ∀ (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31),
    @host_semantic.no_pole (types base F) (selected base F ops) (compilation base F compiled) lambda chi =
    @host_semantic.no_pole base ops compiled lambda chi := by
  intro compiled lambda chi
  delta host_semantic.no_pole
  try simp only [erase_248 base F ops h12, PDict_FormatterTypeMaps.compilation]
  all_goals rfl
#print axioms erase_249

end R1Z.PDict_Static222
