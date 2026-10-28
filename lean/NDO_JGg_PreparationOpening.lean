import NDO_JGg_QueryCalls
import NDO_JGg_ScalarCanon
set_option autoImplicit false
namespace AspisR1.JGg_PreparationOpening
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1ClaimPreparedBridge
open AspisV8R19.SqueezeOracleBridge
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ (gamma kappa alpha0 alpha1 : aspis_core.field.WideExact) (rho : aspis_core.field.QM31)
      (q : Array U32 22#usize) (powers : Array aspis_core.field.WideExact 29#usize),
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
        ok (rho,(⟨encodeState JGg_Opening32.next0,hash⟩ : transcript.Transcript Hash)) ∧
      QueriesModel.queries closedHashQueries D0
        (⟨encodeState JGg_Opening31.before,hash⟩ : transcript.Transcript Hash) 31#u8 JGg_Opening31.payload=
        ok (.Ok q,(⟨encodeState JGg_Opening31.next2,hash⟩ : transcript.Transcript Hash)) ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE gamma) ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE kappa) ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE alpha0) ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE alpha1) ∧
      powersPublic 29#usize gamma=ok powers := by
  dsimp only
  obtain ⟨gamma,kappa,alpha0,alpha1,rho,gc,kc,a0c,a1c,rc⟩ := JGg_Scalars.source D hash
  obtain ⟨q,qc⟩ := JGg_QueryCalls.source D hash
  have gcanon := JGg_ScalarCanon.gamma _ _ _ _ _ _ gc
  have kcanon := JGg_ScalarCanon.ordinary _ _ _ _ _ _ kc
  have a0canon := JGg_ScalarCanon.ordinary _ _ _ _ _ _ a0c
  have a1canon := JGg_ScalarCanon.ordinary _ _ _ _ _ _ a1c
  obtain ⟨powers,powersCall⟩ := JGg_Powers.source 29#usize gamma gcanon
  exact ⟨gamma,kappa,alpha0,alpha1,rho,q,powers,gc,kc,a0c,a1c,rc,qc,gcanon,kcanon,a0canon,a1canon,powersCall⟩
#print axioms source
end AspisR1.JGg_PreparationOpening
