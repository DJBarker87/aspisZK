import NNV_CommonAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_AdapterCommon
open Aeneas Aeneas.Std Result _root_.AdapterRw
/-- Getter transport is proved by source constructor cases, independently of
body continuations; it does not rewrite a nominal statement variant. -/
theorem source (st : AspisS6CurrentCodecInstallation.Statement) :
 aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common st =
 .ok (AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalCommonV1
  (NFY_NBN_StatementResult.common
   (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st))) := by
 cases st <;> rfl
#print axioms source
end AspisR1.NNV_AdapterCommon
end
