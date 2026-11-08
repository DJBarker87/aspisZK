import NNV_CommonAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_AdapterGetter
open Aeneas Aeneas.Std Result

theorem source (st : AspisS6CurrentCodecInstallation.Statement) :
 AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common st =
 .ok (S6N_Getters.commonValue st) := by cases st <;> rfl

theorem diagram (st : AspisS6CurrentCodecInstallation.Statement) :
 AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalCommonV1 (S6N_Getters.commonValue st) =
 NMT_345Dec.toT7 (NMT_345.commonValue (NNH_S1DecodeOk.carrier st)) := by
 rw [NNV_CommonAssociation.common]
 cases st <;> rfl
#print axioms source
#print axioms diagram
end AspisR1.NNV_AdapterGetter
end
