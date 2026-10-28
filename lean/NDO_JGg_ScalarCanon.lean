import NDO_JGg_Scalars
import NDO_JGg_Powers
set_option autoImplicit false
namespace AspisR1.JGg_ScalarCanon
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1ClaimPreparedBridge

theorem gamma {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (out : aspis_core.field.WideExact)
    (call : PreparedModel.scalar closedHashBoundaries.sampling D before row payload true=ok (out,after)) :
    AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE out) := by
  exact scalar_candidate_gamma_canonical closedHashBoundaries.sampling D before after row payload out call
#print axioms gamma

theorem ordinary {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (out : aspis_core.field.WideExact)
    (call : PreparedModel.scalar closedHashBoundaries.sampling D before row payload false=ok (out,after)) :
    AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE out) := by
  exact AspisR1Post25SamplerOrdinaryCallbackV2.scalar_candidate_ordinary_canonical
    closedHashBoundaries.sampling D before after row payload out call
#print axioms ordinary
end AspisR1.JGg_ScalarCanon
