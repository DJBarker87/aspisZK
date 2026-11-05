import NHS_PreparedPacket
import RPz7_RowShape_InstalledSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_NewPort
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation AspisR1ClaimPreparedBridge
/-- The freshly emitted constructor, on the complete current caller carriers. -/
def emitted {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
 (v : verifier.View) (hash : H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 Result (core.result.Result verifier.Prepared verifier.Error × Array aspis_core.field.wide_exact.WideExact 29#usize) := do
 let (r,scratch) ← NGN_Emitted.prepared NHL_PreparedScalars.actual
   (retainedDigest D) (retainedSem sem) (retainedView v) hash (mapArray retainedE g)
 ok ((match r with | .Ok x => .Ok (currentPrepared x) | .Err e => .Err (currentError e)),
     mapArray currentE scratch)

/-- Full Result, including both Errors and the correct post-scratch, with no
constructor-success premise. Native credit is the separate staged (ai) packet. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
 (v : verifier.View) (hash : H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 emitted D sem v hash g=
 originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D sem v hash g := by
 rw [originalNew_eq_transport]
 unfold emitted
 rw [NGN_EmittedEq.source]
 rfl

theorem slot (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
 (std : ClaimsUnrolledFinish.StdCalls) {H : Type} (D : aspis_core.digest.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 emitted D sem v hash g=(RowShape_InstalledSlots.verifierOps ops B std).op8 D sem v hash g :=
 source D sem v hash g
#print axioms source
#print axioms slot
end AspisR1.NHS_NewPort
