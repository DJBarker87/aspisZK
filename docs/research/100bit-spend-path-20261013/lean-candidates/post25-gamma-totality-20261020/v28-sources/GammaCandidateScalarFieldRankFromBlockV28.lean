import GammaCandidateScalarTotalityV27

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Post25Transcript.GammaCandidateSourceModel

theorem scalar_true_block_success_fieldRank {H : Type}
    (D : aspis_core.Digest32 H) (self after : transcript.Transcript H)
    (payload : Slice Aeneas.Std.U8) (block : Bytes32)
    (hblock : transcript.Transcript.block D self 27#u8 payload = .ok (block, after)) :
    ∃ out : E,
      ∃ hscalar :
        transcript.Transcript.scalar gammaCandidateOps D self 27#u8 payload true =
          .ok (out, after),
        scalar_true_success_fieldRank D self after payload out hscalar := by
  obtain ⟨out, hscalar⟩ := scalar_true_total_of_block_success
    D self after payload block hblock
  exact ⟨out, hscalar,
    scalar_true_success_fieldRank D self after payload out hscalar⟩

#print axioms scalar_true_block_success_fieldRank

end AspisR1Post25Transcript.GammaCandidateSourceModel
