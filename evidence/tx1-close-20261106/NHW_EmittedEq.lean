import NHW_EmittedTx1
import NHL_Tx1Model
import NHW_Prepare
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_EmittedEq
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Fresh NHR body retargeting is structurally identical to NHL's body. -/
theorem prepare (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (g : NHL_PrepareStages.Scratch) :
 NHW_EmittedPrepare.prepare ops D pub proof hash obs g=
 NHL_EmittedPrepare.prepare ops D pub proof hash obs g := rfl

theorem tx1 (ops : Ops) {H : Type} (first : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) :
 NHW_EmittedTx1.tx1 ops first D pub publicBytes proof k hash obs=
 NHL_EmittedTx1.tx1 ops first D pub publicBytes proof k hash obs := rfl
#print axioms prepare
#print axioms tx1
end AspisR1.NHW_EmittedEq
