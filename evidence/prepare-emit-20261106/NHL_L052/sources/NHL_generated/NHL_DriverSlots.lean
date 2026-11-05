import NHL_Tx1Model
import NHL_PrepareModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_DriverSlots
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem prepare (base expected : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (g : NHL_PrepareStages.Scratch) :
 verifier.candidate.prepare (NHL_Tx1Model.children base expected) D pub proof hash none g=
 verifier.candidate.prepare base D pub proof hash none g := by
 simp only [verifier.candidate.prepare,NHL_Tx1Model.children,compact.LOGICAL_SEMANTIC,
   compact.OFF_SEMANTIC,compact.OFF_Y1,compact.OFF_INACTIVE,
   verifier.Error.Insts.CoreConvertFromCodecError]

theorem tx1 (base expected : Ops) {H : Type} (first : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H) :
 NHL_EmittedTx1.tx1 (NHL_PrepareModel.children base expected) first D pub public_bytes proof k hash none=
 NHL_EmittedTx1.tx1 base first D pub public_bytes proof k hash none := by
 simp only [NHL_EmittedTx1.tx1,NHL_PrepareModel.children,compact.OFF_FOLDED_ROOT,
   compact.OFF_ROUND1,aspis_core.field.wide_exact.WideExact.ZERO]
#print axioms prepare
#print axioms tx1
end AspisR1.NHL_DriverSlots
