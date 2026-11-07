import NMP_Install150
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Finish136Transport
open Aeneas Aeneas.Std Result NMP_ResultTransport NMP_Transport
abbrev OldPublic := AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
/-- A representation adapter, NOT an assumed successful child or a row root.
The future canonical RowSpec_136 packet must interpret this exact complete
Result/ordered-effect callback before137 can become a candidate. -/
def adapt {H O : Type}
 (finish : OldPublic → AspisR1PublicPreparation.r1_wire.Prefix →
   AspisR1PublicPreparation.r1_wire.SemanticTranscript H →
   AspisR1PublicPreparation.r1_wire.Challenges → O →
   Result (core.result.Result (AspisR1PublicPreparation.r1_semantic.Verified H) AspisR1PublicPreparation.r1_wire.Error))
 (p : NMP_prepare.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pre : NMP_prepare.r1_wire.Prefix) (t : NMP_prepare.r1_wire.SemanticTranscript H)
 (ch : NMP_prepare.aspis_core.state_only_prefix.r0.Challenges) (obs : O) :=
 outer (inner fromT11 fromT12) (finish (toT9 p) (toT13 pre) (toT10 t) (toT3 ch) obs)

theorem same {H O : Type}
 (finish : OldPublic → AspisR1PublicPreparation.r1_wire.Prefix →
   AspisR1PublicPreparation.r1_wire.SemanticTranscript H →
   AspisR1PublicPreparation.r1_wire.Challenges → O →
   Result (core.result.Result (AspisR1PublicPreparation.r1_semantic.Verified H) AspisR1PublicPreparation.r1_wire.Error))
 (p : NMP_prepare.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pre : NMP_prepare.r1_wire.Prefix) (t : NMP_prepare.r1_wire.SemanticTranscript H)
 (ch : NMP_prepare.aspis_core.state_only_prefix.r0.Challenges) (obs : O) :
 outer (inner toT11 toT12) (adapt finish p pre t ch obs) =
 finish (toT9 p) (toT13 pre) (toT10 t) (toT3 ch) obs := by
 apply outer_inverse
 intro r
 exact inner_inverse fromT11 toT11 fromT12 toT12 fromT11_inverse fromT12_inverse r
#print axioms same
end AspisR1.NMP_Finish136Transport
