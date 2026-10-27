import RPv_FJa_ReadersOnRun
import RPv_FJa_BoxedSelAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_SelectorOnRun
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
/-- Original Claims reader and boxed selectors on the SAME accepted semantic
call and SAME alpha array. Canonicality, mass1 and selAt meaning are conclusions. -/
theorem value (std : ClaimsUnrolledFinish.StdCalls) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : r1_semantic.Verified H)
    (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors)
    (accepted : (AspisS1NativeBufferClaimTrace.semanticBase ops
      (ClaimsUnrolledFinish.install std B)).op9 D pub bytes hash none=ok (.Ok sem))
    (boxed : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point
      (FIq_Carriers.mapArray FIq_Carriers.toQ (retainedSem sem).alpha)=ok s) :
    FIr_GatherCallback.CanonClaims (FIq_Carriers.mapArray (FIq_Carriers.mapArray FIq_Carriers.toQ)
      (retainedSem sem).claims) ∧
    FIw_ArrayValue.canonical s.high ∧ FIw_ArrayValue.canonical s.low ∧
    (∑ h : Fin 64,FIv_NativeArray.value s.high h.val)=1 ∧
    (∑ l : Fin 16,FIv_NativeArray.value s.low l.val)=1 ∧
    FIw_PublicModel.selector s=R0P.SemSource.selAt (FIw_ArrayValue.decoded
      (FIq_Carriers.mapArray FIq_Carriers.toQ (retainedSem sem).alpha)) := by
  have readers := FJa_ReadersOnRun.value std ops B D pub bytes hash sem accepted
  have canonical := FJa_BoxedCanonical.value _ s readers.2 boxed
  have mass := FJa_BoxedMass.value _ s readers.2 boxed
  exact ⟨readers.1,canonical.1,canonical.2,mass.1,mass.2,
    FJa_BoxedSelAt.value _ s readers.2 boxed⟩
#print axioms value
end AspisR1.FJa_SelectorOnRun
end
