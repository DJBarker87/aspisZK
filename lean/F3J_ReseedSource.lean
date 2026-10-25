import F3J_BlockCalls
import PAln_Physical
import AuS1_Hash
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_ReseedSource
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation PreparedHashCode

theorem address (semantic : Array U8 32#usize) :
    flatten (CallerStep.reseedParts semantic .S2)=OpeningReseedFrame.frame 2 (decodeState semantic) := by
  simp only [CallerStep.reseedParts,CallerStep.openingDomain,CallerStep.variantTag,flatten,
    Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    OpeningReseedFrame.frame,TrailingStateFrame.frame]
  rw [PAln_Physical.state_bytes]
  rfl

theorem reached {Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (semantic : Array U8 32#usize) (out : transcript.Transcript Hash)
    (success : transcript.Transcript.new D hash semantic .S2=ok out)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H) :
    decodeState out.state=H (OpeningReseedFrame.frame 2 (decodeState semantic)) ∧
      observe (run (PreparedHashEffects.new effects D hash semantic .S2)).1=
        [(OpeningReseedFrame.frame 2 (decodeState semantic),decodeState out.state)] := by
  obtain ⟨seed,digest,same⟩ := CallerStep.opening_new_success D hash semantic .S2 out success
  have value := backend _ ⟨hash,_,seed,rfl,digest⟩
  change decodeState seed=H (flatten _) at value
  rw [address] at value
  have outState : out.state=seed := congrArg (fun t => t.state) same
  refine ⟨by rw [outState];exact value,?_⟩
  have call := digest
  unfold CallerStep.reseedParts CallerStep.openingDomain CallerStep.variantTag at call
  simp only [PreparedHashEffects.new,transport.Variant.tag,Bind.bind,Pure.pure,
    PreparedHashCode.bind,run,lift,liftM,MonadLift.monadLift,MonadLiftT.monadLift,effects,
    call,observe,List.flatMap_cons,List.flatMap_nil,List.singleton_append]
  rw [outState,← address]
  rfl

#print axioms address
#print axioms reached
end AspisR1.F3J_ReseedSource
end
