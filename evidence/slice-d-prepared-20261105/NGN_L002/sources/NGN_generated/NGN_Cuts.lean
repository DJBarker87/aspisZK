import NFW_PreparedControl
import NFW_PreparedResults
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGN_Cuts
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedScratchReachability NFW_PreparedControl

/-- Exact continuation at the final claim call, retaining rejection and scratch. -/
def claimCut (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (g : Scratch) (o : Opening H)
 (queries : Array U32 22#usize) (rho : aspis_core.field.QM31) (last : transcript.Transcript H) : Result Out := do
 let r ← B.claim D sem v.y1 v.inactive g o.kappa
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue claim => ok (.Ok (output sem v o.gamma o.kappa o.alpha rho queries claim last),g)
 | .Break residual =>
   let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     verifier.Prepared (core.convert.FromSame verifier.Error) residual
   ok (r,g)

def powersCut (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (o : Opening H)
 (queries : Array U32 22#usize) (rho : aspis_core.field.QM31) (last : transcript.Transcript H) : Result Out := do
 let g ← B.powers 29#usize o.gamma
 claimCut B D sem v g o queries rho last

def rhoCut (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (o : Opening H)
 (queries : Array U32 22#usize) (after : transcript.Transcript H) : Result Out := do
 let row ← o.row+1#u8
 let payload ← lift (Array.to_slice (Std.Array.empty U8))
 let (rho,last) ← PreparedModel.scalar_k B.sampling D after row payload
 powersCut B D sem v o queries rho last

def queryCut (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (old : Scratch) (o : Opening H) : Result Out := do
 let (r,after) ← B.sampling.queries D o.transcript o.row v.final_message
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue queries => rhoCut B D sem v o queries after
 | .Break residual =>
   let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     verifier.Prepared (core.convert.FromSame verifier.Error) residual
   ok (r,old)

/-- A syntactic model factorization: no native output equality is assumed. -/
theorem continuation (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (old : Scratch) (o : Opening H) :
 NFW_PreparedControl.continuation B D sem v old o=queryCut B D sem v old o := by
 rfl

theorem source (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (old : Scratch) :
 PreparedScratchModel.prepare B D sem v hash old=
 (do let o ← opening B D sem v hash; queryCut B D sem v old o) := by
 rw [NFW_PreparedControl.source]
 rfl
#print axioms continuation
#print axioms source
end AspisR1.NGN_Cuts
