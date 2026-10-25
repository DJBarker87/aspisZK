import AuS1_OriginalRead
import AuS1_Enclosing
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_ClosedRead
open Aeneas Aeneas.Std Result
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared AspisR1ClaimPreparedBridge
attribute [local irreducible] AspisR1PublicPreparation.PreparedSourceEffects.prepare preparationEffects closedHashBoundaries closedHashQueries

 theorem frame {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) (out : verifier.Prepared)
    (root : Array U8 32#usize) (variant : view.variant = .S2) (folded : view.folded_root = some root)
    (success : erase (closedPreparationCode D sem view hash input) = ok (.Ok out,scratch)) :
    ∃ frame, Read (observe (run (closedPreparationCode D sem view hash input)).1) frame ∧
      BinRawByteCollisionTargets.pred 3 frame = some (decodeState root) := by
  unfold closedPreparationCode at success ⊢
  obtain ⟨value,hvalue,after,contains⟩ := AuS1_Suffix.right_read _ _ _ success
  rcases value with ⟨result,g⟩
  cases result with
  | Err error =>
    rw [erase_pure] at after
    cases after
  | Ok prepared =>
    have var : (retainedView view).variant = .S2 := by
      simp only [retainedView,variant,retainedVariant]
    have fr : (retainedView view).folded_root = some root := folded
    obtain ⟨frame,read,target⟩ := AuS1_OriginalRead.frame closedHashBoundaries closedHashQueries
      (retainedDigest D) (retainedSem sem) (retainedView view) hash
      (mapArray retainedE input) g prepared root var fr hvalue
    exact ⟨frame,AuS1_Suffix.left_read _ _ _ success frame read,target⟩

#print axioms frame
end AspisR1.AuS1_ClosedRead
end
