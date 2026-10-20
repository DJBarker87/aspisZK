import FullPublicTotalCase
import RawFullPublicSelection
import RawPublicSelectionLift
import RWireRawLiteralDecoderCompletion

/-! The all-33-round table-only selector recovers the actual public statement from
raw literal verifier executions, following an arbitrary consistent raw prefix.
The oracle domain stays unrestricted. Only protocol frames are projected to
the existing bounded-address proof. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawFullPublicSelection
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralLegacyRun CanonicalAddressEmbedding RWireLiteralLegacyDecoderCompletion

abbrev select := RawFullPublicSelection.select

theorem bounded_at_first_cell (decoder : LiteralByteProtocol.Decoder)
    (draw : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i)) (htag : pub.tag = 2)
    (prior : List (Bytes × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (Q : Nat)
    (hQ : firstReads emptyTable (rawTrace decoder draw H pub pf prior) ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred Q) emptyTable (rawTrace decoder draw H pub pf prior))
    (n : Nat) (hn : n < 33) (a : Addr L)
    (hfirst : firstCell (legacyProtocol.chain (fun b => H b.toBytes) pub (proof pf) n) = some a) :
    FullPublicSelection.select SelectedTranscriptParams.params a
      (tableBefore emptyTable (RawBoundedTrace.trace L (rawTrace decoder draw H pub pf prior)) a) =
        some pub := by
  let Hb : Addr L → State := fun b => H b.toBytes
  let tr := rawTrace decoder draw H pub pf prior
  let bp := RawBoundedTrace.trace L prior
  let P := RawBoundedProgram.readTrace bp (proof pf)
  let V := FS2.verifier legacyProtocol (fun _ _ => true)
  have hcons : ∀ q ∈ tr, q.2 = H q.1 := by
    intro q hq
    rcases List.mem_append.mp hq with hp | hv
    · exact hprior q hp
    · exact FS.eval_consistent H _ q hv
  have hP : eval Hb P = (bp,proof pf) :=
    RawBoundedProgram.eval_readTrace Hb bp (proof pf)
      (RawBoundedTrace.trace_consistent L H prior hprior)
  have htrace : (eval Hb (FS.experiment P V pub)).1 = RawBoundedTrace.trace L tr := by
    rw [FS.experiment_eval, hP]
    change bp ++ (eval Hb (V pub (proof pf))).1 =
      RawBoundedTrace.trace L
        (prior ++ (eval H (FS2.verifier (LiteralByteProtocol.protocol decoder) draw pub pf)).1)
    rw [RawBoundedProgram.trace_append,
      LiteralLegacyVerifierTrace.restricted_trace_eq decoder draw (fun _ _ => true) H pub pf hvalid]
  have hbQ : firstReads emptyTable (eval Hb (FS.experiment P V pub)).1 ≤ Q := by
    rw [htrace]
    exact (RawBoundedTrace.firstReads_trace_le L tr).trans hQ
  have hbout : ¬ hitsBad (badColl SelectedTranscriptParams.params Q) emptyTable
      (eval Hb (FS.experiment P V pub)).1 := by
    rw [htrace]
    exact RWireRawBoundedCollision.no_duplex_collision SelectedTranscriptParams.params
      H tr Q hcons hQ hout
  have hbtail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Q) emptyTable
      (eval Hb (FS.experiment P V pub)).1 := by
    rw [htrace]
    exact RWireRawBoundedCollision.no_tail_collision SelectedTranscriptParams.params.iv
      H tr Q hcons hQ hout
  have hpub : pub.pubBytes.length < 2^32 := by
    have hf := pub.initFits
    change 75 + pub.pubBytes.length ≤ 131072 at hf
    omega
  let m0 : BytesMessage := ⟨PublicInitFrame.emptyRecord, by decide⟩
  have hfirstP : firstCell (legacyProtocol.chain Hb pub (eval Hb P).2 n) = some a := by
    rw [hP]
    exact hfirst
  have hselect := FullPublicTotalCase.actual_first_cell SelectedTranscriptParams.params
    (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
    (fun _ _ => (none : Option Unit)) (fun _ _ => true) Hb pub P hpub htag (by intro i hi; rfl) rfl
    m0 rfl Q hbQ hbout hbtail n hn a hfirstP
  change FullPublicSelection.select SelectedTranscriptParams.params a
    (tableBefore emptyTable (eval Hb (FS.experiment P V pub)).1 a) = some pub at hselect
  rw [htrace] at hselect
  exact hselect

private theorem firstCell_mem {I A C : Type} [DecidableEq I] [Inhabited A]
    (H : I → A) (s : Sampler I A C) (a : I) (ha : firstCell s = some a) :
    a ∈ (eval H s.toProgram).1.map Prod.fst := by
  cases s with
  | done c => cases ha
  | ask i k =>
      simp only [firstCell,Option.some.injEq] at ha
      subst i
      exact List.mem_cons_self ..
  | multi c cs nd k =>
      simp only [firstCell,Option.some.injEq] at ha
      subst c
      exact List.mem_cons_self ..

theorem at_first_cell (decoder : LiteralByteProtocol.Decoder)
    (draw : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i)) (htag : pub.tag = 2)
    (prior : List (Bytes × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (Q : Nat)
    (hQ : firstReads emptyTable (rawTrace decoder draw H pub pf prior) ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred Q) emptyTable (rawTrace decoder draw H pub pf prior))
    (n : Nat) (hn : n < 33) (raw : Bytes)
    (hfirst : firstCell ((LiteralByteProtocol.protocol decoder).chain H pub pf n) = some raw) :
    select raw (tableBefore emptyTable (rawTrace decoder draw H pub pf prior) raw) = some pub := by
  rw [RWireRawLiteralDecoderCompletion.chain_firstCell_eq decoder H pub pf hvalid n (by omega)] at hfirst
  cases hf : firstCell (legacyProtocol.chain (fun b => H b.toBytes) pub (proof pf) n) with
  | none => simp [hf] at hfirst
  | some a =>
      have he : a.toBytes = raw := by simpa [hf] using hfirst
      subst raw
      have hmem := firstCell_mem (fun b => H b.toBytes)
        (legacyProtocol.chain (fun b => H b.toBytes) pub (proof pf) n) a hf
      obtain ⟨q,hq,heq⟩ := List.mem_map.mp hmem
      have ha : CanonicalByteAddress.Canonical a := by
        have hc := RawBoundedProgram.labels_eval CanonicalByteAddress.Canonical
          (legacyProtocol.chain (fun b => H b.toBytes) pub (proof pf) n).toProgram
          (LiteralLegacyVerifierTrace.chain_canonical (fun b => H b.toBytes) pub (proof pf) n)
          (fun b => H b.toBytes) q hq
        simpa [heq] using hc
      unfold select RawFullPublicSelection.select
      change RawPublicSelectionLift.select L
        (FullPublicSelection.select SelectedTranscriptParams.params)
        (toBytes (⟨a,ha⟩ : AddrC L))
        (tableBefore emptyTable (rawTrace decoder draw H pub pf prior)
          (toBytes (⟨a,ha⟩ : AddrC L))) = some pub
      rw [RawPublicSelectionLift.at_current_table L _ ⟨a,ha⟩]
      exact bounded_at_first_cell decoder draw H pub pf hvalid htag prior hprior Q hQ hout n hn a hf

#print axioms bounded_at_first_cell
#print axioms at_first_cell
#print axioms firstCell_mem
end AspisR1.RWireRawFullPublicSelection
end
