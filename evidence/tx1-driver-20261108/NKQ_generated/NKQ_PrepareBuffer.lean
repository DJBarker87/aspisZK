import NKQ_PrepareStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_PrepareBuffer
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
abbrev Scratch := NHL_PrepareStages.Scratch
abbrev Out := NHL_PrepareStages.Out

def afterBuffer (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (hash : H) (g : Scratch) (r : core.result.Result verifier.View verifier.Error) : Result Out := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue v => NHL_PrepareStages.semanticCut ops D pub hash none g v
 | .Break residual => do
   let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual verifier.Prepared (core.convert.FromSame verifier.Error) residual
   ok (r,g)

theorem factor (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (g : Scratch) :
 NHL_PrepareStages.run ops D pub proof hash none g =
 (do let r ← NHL_PrepareStages.buffers ops D proof; afterBuffer ops D pub hash g r) := by rfl

theorem buffer_error (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (hash : H) (g : Scratch) (e : verifier.Error) :
 afterBuffer ops D pub hash g (.Err e)=ok (.Err e,g) := by rfl

#print axioms factor
#print axioms buffer_error
#print factor
end AspisR1.NKQ_PrepareBuffer
end
