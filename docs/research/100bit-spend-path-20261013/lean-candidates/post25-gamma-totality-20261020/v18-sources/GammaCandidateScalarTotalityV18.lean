import GammaCandidateTotalityV14
import GammaCandidateScalarTranscriptFieldRank

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Post25Transcript.GammaCandidateSourceModel

open AspisR1GammaCaller.DigitsModel
open AspisR1Post25Transcript.OrdinaryCandidateSourceModel

private def gammaToCandidateTotal (v : GammaWide) : CandidateWide :=
  ⟨⟨⟨v.c0.c0.a, v.c0.c0.b⟩, ⟨v.c0.c1.a, v.c0.c1.b⟩⟩,
    ⟨⟨v.c1.c0.a, v.c1.c0.b⟩, ⟨v.c1.c1.a, v.c1.c1.b⟩⟩⟩

theorem candidate_gamma_ops_total (block : Bytes32) :
    ∃ out : E, gammaCandidateOps.gamma block = .ok out := by
  obtain ⟨sample, hsample⟩ := candidate_gamma_total block
  refine ⟨fromWide (gammaToCandidateTotal sample), ?_⟩
  change (do
      let value ← AspisR1GammaCaller.sampler.gamma_sample candidateGammaHelpers block
      .ok (fromWide (gammaToCandidateTotal value))) =
    .ok (fromWide (gammaToCandidateTotal sample))
  rw [hsample]
  rfl

private theorem bind_pair_ok {α β γ : Type} (a : α) (b : β)
    (k : α → β → Result γ) :
    (do let (x,y) ← (Result.ok (a,b) : Result (α × β)); k x y) = k a b := by
  rfl

theorem scalar_true_total_of_block_success {H : Type}
    (D : aspis_core.Digest32 H) (self after : transcript.Transcript H)
    (payload : Slice U8) (block : Bytes32)
    (hblock : transcript.Transcript.block D self 27#u8 payload = .ok (block, after)) :
    ∃ out : E,
      transcript.Transcript.scalar gammaCandidateOps D self 27#u8 payload true =
        .ok (out, after) := by
  obtain ⟨sample, hgamma⟩ := candidate_gamma_ops_total block
  refine ⟨sample, ?_⟩
  unfold transcript.Transcript.scalar
  rw [hblock]
  rw [bind_pair_ok]
  simp only [if_true]
  rw [hgamma]
  -- Casting this fixed U8 row to Usize succeeds; trace.value is the generated
  -- no-op event and returns `ok ()`.
  have hcast :
      (lift (UScalar.cast .Usize (27#u8)) : Result Usize) = .ok (27#usize) := by
    decide
  rw [hcast]
  simp [trace.value]

#print axioms candidate_gamma_ops_total
#print axioms scalar_true_total_of_block_success

end AspisR1Post25Transcript.GammaCandidateSourceModel
