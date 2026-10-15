import R1LiteralClassifier
import R1LiteralByteSampler
import R1LiteralProtocol
import R1AllAddressFiatShamir
import FS2.Verifier

/-! The selected 33-row protocol over all finite byte strings. The bounded
carrier only constructs protocol-format calls. The adversary, verifier and
oracle table below have unrestricted byte addresses. Both decoder and extractor
are parameters; the default extractor is specification-level choice.
The concrete classifier D1/D2 uses that default; this supplies no efficiency.
The conditional bound keeps raw-byte injection and collision mass explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralByteProtocol

open FS FS2 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open LiteralTranscript

abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev Address := Bytes
abbrev Proof := LiteralProtocol.Proof
abbrev Witness := SpendRelation.Wspend
abbrev Decoder := Address → Table Address State →
  Option (Sampler Address State (LiteralTranscript.Prefix × LiteralTranscript.Message × Challenge))
abbrev Extractor := Public → Table Address State → Option Witness

def protocol (decoder : Decoder)
    (extractor : Extractor := fun pub _ => GenericNoHit.chooseWitness LiteralProtocol.relation pub) :
    FS2.Protocol Public LiteralTranscript.Message Challenge Witness Proof Address State where
  r := 33
  msg := fun pf i => pf i
  samp := LiteralByteSampler.samp
  decode := decoder
  extract := extractor

def rows : RoundByRound' Public LiteralTranscript.Message Challenge Bytes State :=
  GenericNoHitFS2.rows LiteralClassifier.bad LiteralProtocol.relation LiteralClassifier.budget

theorem d1 (decoder : Decoder) : D1 (protocol decoder) rows :=
  GenericNoHitFS2.d1 (protocol decoder) LiteralClassifier.bad LiteralProtocol.relation
    LiteralClassifier.budget (fun _ _ => rfl)

theorem d2 (decoder : Decoder) : D2 (protocol decoder) rows := by
  apply GenericNoHitFS2.d2 (protocol decoder) LiteralClassifier.bad
    LiteralProtocol.relation LiteralClassifier.budget
  intro i P m hround hi _
  subst i
  exact LiteralClassifier.byte_density P m hi

#print axioms d1
#print axioms d2

theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (label : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
  cases s <;> rfl

theorem transcript_eq (decoder : Decoder) (extractor : Extractor)
    (H : Bytes → State) (pub : Public) (pf : Proof) (n : Nat) :
    (protocol decoder extractor).transcript H pub pf n =
      LiteralRun.transcript (fun a => H a.toBytes) pub pf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((protocol decoder extractor).transcript H pub pf n).ext (pf n)
        (eval H (LiteralByteSampler.samp n
          ((protocol decoder extractor).transcript H pub pf n) (pf n)).toProgram).2 = _
      rw [ih, LiteralByteSampler.eval_eq]
      rfl

theorem erased_transcript (decoder : Decoder) (extractor : Extractor)
    (H : Bytes → State) (pub : Public) (pf : Proof) (n : Nat) :
    erasePrefix ((protocol decoder extractor).transcript H pub pf n) =
      LiteralRun.erasedTranscript (fun a => H a.toBytes) pub pf n := by
  rw [transcript_eq]
  exact LiteralRun.erase_transcript _ pub pf n

theorem chainsRead (decoder : Decoder) (extractor : Extractor) :
    FS2.ChainsRead (protocol decoder extractor) := by
  intro i P m hi
  change firstCell (ProgramSamplerMap.map FS2.Duplex.Addr.toBytes
    (LiteralTranscript.samp i P m)) ≠ none
  rw [firstCell_map]
  have hn : firstCell (LiteralTranscript.samp i P m) ≠ none :=
    UnifiedSampler.firstCell_some _ _ _ _ _
  cases h : firstCell (LiteralTranscript.samp i P m) with
  | none => exact absurd h hn
  | some a => simp

private theorem firstCell_mem {I A C : Type} [DecidableEq I] [Inhabited A]
    (H : I → A) (s : Sampler I A C) (a : I) (ha : firstCell s = some a) :
    a ∈ (eval H s.toProgram).1.map Prod.fst := by
  cases s with
  | done c => cases ha
  | ask i k =>
      simp only [FS2.firstCell, Option.some.injEq] at ha
      subst i
      exact List.mem_cons_self ..
  | multi c cs nd k =>
      simp only [FS2.firstCell, Option.some.injEq] at ha
      subst c
      exact List.mem_cons_self ..

theorem readsChains (decoder : Decoder) (extractor : Extractor)
    (decision : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool) :
    FS2.ReadsChains (protocol decoder extractor)
      (FS2.verifier (protocol decoder extractor) decision) := by
  intro H pub pf i a hi ha
  apply FS2.verifier_reads (protocol decoder extractor) decision H pub pf i hi a
  exact firstCell_mem H _ a ha

/-- This is an oracle-model theorem with obligations, not a closed R1 bound.
In particular no injection theorem is transported through a noninjective
address map, and no finite input-length or CallsFit premise is present. -/
theorem conditional_bound {Y : Type} (decoder : Decoder) (extractor : Extractor)
    (rb : RoundByRound' Public LiteralTranscript.Message Challenge Bytes State)
    (dec : R0C.V3.Dec Public LiteralTranscript.Message Challenge Bytes State Y)
    (P : Program Bytes State Proof) (V : Public → Proof → Program Bytes State Bool)
    (pub : Public) (κ : Nat → ℚ) (Qtot : Nat)
    (hD1 : FS2.D1 (protocol decoder extractor) rb)
    (hCD : R0C.V3.ChainDensity3 (protocol decoder extractor) rb dec)
    (hD3 : FS2.D3 (protocol decoder extractor) rb V)
    (hV : FS2.ReadsChains (protocol decoder extractor) V)
    (inj : AllAddressFiatShamir.LazyInj (protocol decoder extractor) dec P V pub κ Qtot)
    (hQ : ∀ H : Bytes → State,
      FS2.distinctFirstReads (eval H (FS2.experiment P V pub)) ≤ Qtot) :
    lazyMean (FS2.experiment P V pub) emptyTable
      (fun v => indicator (FS2.accepts v ∧ FS2.extractFails (protocol decoder extractor) pub v)) ≤
      (Qtot : ℚ) * maxErr rb.ε 33 + κ Qtot :=
  AllAddressFiatShamir.soundness_bound (protocol decoder extractor) rb dec P V pub κ Qtot
    hD1 hCD hD3 (chainsRead decoder extractor) hV inj hQ

#print axioms firstCell_map
#print axioms transcript_eq
#print axioms erased_transcript
#print axioms chainsRead
#print axioms readsChains
#print axioms conditional_bound
end AspisR1.LiteralByteProtocol
end
