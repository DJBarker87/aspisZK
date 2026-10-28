import NDO_JGg_ScalarForward
import NDO_JGg_Opening27
import NDO_JGg_Opening28
import NDO_JGg_Opening29
import NDO_JGg_Opening30
import NDO_JGg_Opening32
set_option autoImplicit false
namespace AspisR1.JGg_Scalars
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisV8R19.SqueezeOracleBridge

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ (gamma kappa alpha0 alpha1 : aspis_core.field.WideExact) (rho : aspis_core.field.QM31),
      PreparedModel.scalar closedHashBoundaries.sampling D0
        (⟨encodeState JGg_Opening27.before,hash⟩ : transcript.Transcript Hash) 27#u8 JGg_Opening27.payload true=
        ok (gamma,(⟨encodeState JGg_Opening27.next0,hash⟩ : transcript.Transcript Hash)) ∧
      PreparedModel.scalar closedHashBoundaries.sampling D0
        (⟨encodeState JGg_Opening28.before,hash⟩ : transcript.Transcript Hash) 28#u8 JGg_Opening28.payload false=
        ok (kappa,(⟨encodeState JGg_Opening28.next0,hash⟩ : transcript.Transcript Hash)) ∧
      PreparedModel.scalar closedHashBoundaries.sampling D0
        (⟨encodeState JGg_Opening29.before,hash⟩ : transcript.Transcript Hash) 29#u8 JGg_Opening29.payload false=
        ok (alpha0,(⟨encodeState JGg_Opening29.next0,hash⟩ : transcript.Transcript Hash)) ∧
      PreparedModel.scalar closedHashBoundaries.sampling D0
        (⟨encodeState JGg_Opening30.before,hash⟩ : transcript.Transcript Hash) 30#u8 JGg_Opening30.payload false=
        ok (alpha1,(⟨encodeState JGg_Opening30.next0,hash⟩ : transcript.Transcript Hash)) ∧
      PreparedModel.scalar_k closedHashBoundaries.sampling D0
        (⟨encodeState JGg_Opening32.before,hash⟩ : transcript.Transcript Hash) 32#u8 JGg_Opening32.payload=
        ok (rho,(⟨encodeState JGg_Opening32.next0,hash⟩ : transcript.Transcript Hash)) := by
  dsimp only
  obtain ⟨gamma,gammaCall⟩ := JGg_ScalarForward.gamma _ _ _ _ _ _ (JGg_Opening27.source D hash)
  obtain ⟨kappa,kappaCall⟩ := JGg_ScalarForward.ordinary _ _ _ _ _ _ (JGg_Opening28.source D hash)
  obtain ⟨alpha0,alpha0Call⟩ := JGg_ScalarForward.ordinary _ _ _ _ _ _ (JGg_Opening29.source D hash)
  obtain ⟨alpha1,alpha1Call⟩ := JGg_ScalarForward.ordinary _ _ _ _ _ _ (JGg_Opening30.source D hash)
  obtain ⟨rho,rhoSample,rhoCall,rhoCanon⟩ := AspisR1ClaimPreparedBridge.SourceFromQm.scalar_k_source_success
    closedHashBoundaries.sampling _ _ _ _ _ _ (JGg_Opening32.source D hash)
  exact ⟨gamma,kappa,alpha0,alpha1,rho,gammaCall,kappaCall,alpha0Call,alpha1Call,rhoCall⟩
#print axioms source
end AspisR1.JGg_Scalars
