import NHL_PrepareStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_PrepareStages
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
abbrev Scratch := NHL_PrepareStages.Scratch
abbrev Out := NHL_PrepareStages.Out

/-- Literal continuation around op9, with every semantic error mapped by the
frozen closure and scratch retained on rejection. Ops is used for this source
factorisation only; it is prohibited as an undispatched native root premise. -/
def afterSemantic (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (hash : H) (g : Scratch) (v : verifier.View)
 (r5 : core.result.Result (r1_semantic.Verified H) r1_semantic.Error) : Result Out := do
 let r6 ← AspisR1CurrentCaller.core.result.Result.map_err
   (verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError D) r5 ()
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r6
 match cf with
 | .Continue sem => do
   verifier.mark none verifier.Phase.Semantic
   ops.op8 D sem v hash g
 | .Break residual => do
   let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     verifier.Prepared (core.convert.FromSame verifier.Error) residual
   ok (r,g)

theorem factor (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (hash : H) (g : Scratch) (v : verifier.View) :
 NHL_PrepareStages.semanticCut ops D pub hash none g v =
 (do let r ← ops.op9 D pub v.semantic hash none; afterSemantic ops D hash g v r) := by rfl

theorem semantic_error (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (hash : H) (g : Scratch) (v : verifier.View) (e : r1_semantic.Error) :
 afterSemantic ops D hash g v (.Err e)=ok (.Err verifier.Error.Semantic,g) := by rfl

#print axioms factor
#print axioms semantic_error
#print factor
end AspisR1.NKQ_PrepareStages
end
