import R1LiteralTranscript
import R1SelectedChallengeMap

/-! Exact suffix equations under one byte oracle. Source call/log embedding,
byte framing and arithmetic transport are explicit premises, not inferred
from a successful model run. Roots are arbitrary bytes in the message. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawSamplerSuffixCorrespondence
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open LiteralTranscript
abbrev p := SelectedTranscriptParams.params
abbrev Oracle := Addr SelectedTranscriptParams.L → State

def absorption (P : LiteralTranscript.Prefix) (i : Nat)
    (m : SelectedTranscriptParams.Message) : Addr SelectedTranscriptParams.L :=
  UnifiedSampler.absorb p i (LiteralTranscript.erasePrefix P) m

/-- Rows 25, 27--30 and 32 have exactly the ordinary three-read law.
The premises can be discharged from source digest calls in a shared log. -/
theorem ordinary_correspondence (H : Oracle) (P : LiteralTranscript.Prefix)
    (i : Nat) (hi : i = 25 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 32)
    (m : LiteralTranscript.Message) (bytes : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase m = .payload bytes)
    (absorbed block next : State)
    (ha : H (absorption P i bytes) = absorbed)
    (hb : H (squeezeA p absorbed) = block)
    (hn : H (advanceA p absorbed) = next) :
    (eval H (LiteralTranscript.samp i P m).toProgram).2 =
      (.ordinary (SelectedChallengeMap.sigma i block), next) := by
  have hi0 : i ≠ 0 := by omega
  have hi26 : i ≠ 26 := by omega
  have hi31 : i ≠ 31 := by omega
  rw [LiteralTranscript.samp, hm,
    UnifiedSampler.row_ordinary p _ i hi0 hi26 hi31,
    DuplexSamplers.plain_eval]
  change (TranscriptView.liftChallenge
    (p.σ i (H (squeezeA p (H (absorption P i bytes)))),
      H (advanceA p (H (absorption P i bytes))))) = _
  rw [ha, hb, hn]
  rfl

/-- Row 26 returns the circle challenge from the squeeze, but carries the
state of the additional P3 reseed (not the pre-reseed advance). -/
theorem reseed_correspondence (H : Oracle) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (bytes : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase m = .payload bytes)
    (absorbed block advanced reseeded : State)
    (ha : H (absorption P 26 bytes) = absorbed)
    (hb : H (squeezeA p absorbed) = block)
    (hx : H (advanceA p absorbed) = advanced)
    (hr : H (OpeningReseedFrame.addr P.statement.tag
      (by have := P.statement.initFits; dsimp [SelectedTranscriptParams.L]; omega)
      advanced) = reseeded) :
    (eval H (LiteralTranscript.samp 26 P m).toProgram).2 =
      (.ordinary (SelectedChallengeMap.sigma 26 block), reseeded) := by
  rw [LiteralTranscript.samp, hm, UnifiedSampler.row_reseed,
    DuplexSamplers.reseeded_eval]
  change (TranscriptView.liftChallenge
    (p.σ 26 (H (squeezeA p (H (absorption P 26 bytes)))),
      H (OpeningReseedFrame.addr P.statement.tag _
        (H (advanceA p (H (absorption P 26 bytes))))))) = _
  rw [ha, hb, hx, hr]
  rfl

/-- The actual query target includes both the query vector and the state
selected by the stopping scan; replacing it by the eighth advance is invalid. -/
theorem query_correspondence (H : Oracle) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (bytes : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase m = .payload bytes) :
    (eval H (LiteralTranscript.samp 31 P m).toProgram).2 =
      UnifiedSampler.liftQuery (QueryFirstRead.result p H
        (QuerySampler.state p H (H (absorption P 31 bytes)))) := by
  rw [LiteralTranscript.samp, hm, UnifiedSampler.row_query]
  exact QuerySamplerBridge.output p H _ _

/-- Circle point views use the row-specific total maps, including fallback. -/
theorem circle_views (block : State) :
    R0P.SemSource.circleSampleParameter0
      (SelectedChallengeMap.rhoOf (SelectedChallengeMap.sigma 25 block)) =
        R0P.SemSource.circleSample0 block ∧
    R0P.SemSource.circleSampleParameter1
      (SelectedChallengeMap.rhoOf (SelectedChallengeMap.sigma 26 block)) =
        R0P.SemSource.circleSample1 block :=
  ⟨SelectedChallengeMap.first_circle_view block,
    SelectedChallengeMap.second_circle_view block⟩

/-- Gamma is the nonzero-rank sampler, not the ordinary field sampler. -/
theorem gamma_map (block : State) :
    SelectedChallengeMap.sigma 27 block =
      OpeningSamplerBound.gammaSample SelectedSamplerRanks.stateRank
        R0C.ModuloField.nonzeroRank block := SelectedChallengeMap.gamma_row block

theorem gamma_nonzero (block : State) : SelectedChallengeMap.sigma 27 block ≠ 0 := by
  rw [gamma_map]
  exact OpeningSamplerBound.gammaSample_ne_zero SelectedSamplerRanks.stateRank
    R0C.ModuloField.nonzeroRank block

theorem opening_maps (i : Nat) (hi : i = 28 ∨ i = 29 ∨ i = 30) (block : State) :
    SelectedChallengeMap.sigma i block =
      OpeningSamplerBound.sample SelectedSamplerRanks.stateRank
        R0C.ModuloField.fieldRank block := SelectedChallengeMap.opening_row i hi block

theorem rho_map (block : State) :
    SelectedChallengeMap.rhoOf (SelectedChallengeMap.sigma 32 block) =
      R0P.SemSource.qm31Sample block := by
  simp only [SelectedChallengeMap.sigma, show (32 : Nat) ≠ 27 by decide,
    show ¬ ((32 : Nat) = 28 ∨ 32 = 29 ∨ 32 = 30) by decide,
    show (32 : Nat) ≠ 31 by decide, if_false]
  exact SelectedChallengeMap.semChal_re block

#print axioms ordinary_correspondence
#print axioms reseed_correspondence
#print axioms query_correspondence
#print axioms circle_views
#print axioms gamma_map
#print axioms gamma_nonzero
#print axioms opening_maps
#print axioms rho_map
end AspisR1.RawSamplerSuffixCorrespondence
end
