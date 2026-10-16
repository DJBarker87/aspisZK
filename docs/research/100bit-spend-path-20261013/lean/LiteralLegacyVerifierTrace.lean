import LiteralLegacyRun
import RawBoundedProgram
import R1UnifiedCanonicalLabels

/-! Exact verifier-trace reuse: the actual literal byte verifier has the
legacy unified verifier trace after canonical restriction. This proof uses
the existing all-continuations canonical-label theorem for sampler calls;
it imposes no condition on raw adversary queries. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralLegacyVerifierTrace

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralLegacyRun

theorem trace_eq_map (decoder : LiteralByteProtocol.Decoder)
    (draw : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool)
    (dold : UnifiedSampler.Prefix BytesMessage AspisWideTower.WideExact L →
      TranscriptView.Message BytesMessage → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i)) :
    (eval H (FS2.verifier (LiteralByteProtocol.protocol decoder) draw pub pf)).1 =
      ((eval (fun a => H a.toBytes)
        (FS2.verifier legacyProtocol dold pub (proof pf))).1.map
        fun q => (q.1.toBytes,q.2)) := by
  rw [FS2.verifier_eval, FS2.verifier_eval]
  change ((List.range 33).map fun i =>
    (eval H ((LiteralByteProtocol.protocol decoder).chain H pub pf i).toProgram).1).flatten =
    (((List.range 33).map fun i =>
      (eval (fun a => H a.toBytes)
        (legacyProtocol.chain (fun a => H a.toBytes) pub (proof pf) i).toProgram).1).flatten.map
          fun q => (q.1.toBytes,q.2))
  rw [List.map_flatten, List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i hi
  exact congrArg Prod.fst (LiteralLegacyRun.chain_eval_eq decoder H pub pf hvalid i
    (List.mem_range.mp hi))

theorem chain_canonical (H : Addr L → State) (pub : LiteralTranscript.Public)
    (pf : UnifiedProtocol.Proof BytesMessage) (i : Nat) :
    ProgramLabelRestriction.AllLabels CanonicalByteAddress.Canonical
      (legacyProtocol.chain H pub pf i).toProgram := by
  exact UnifiedCanonicalLabels.samp_allLabels SelectedTranscriptParams.params _ i
    (legacyProtocol.transcript H pub pf i) (legacyProtocol.msg pf i)

theorem verifier_trace_canonical
    (dold : UnifiedSampler.Prefix BytesMessage AspisWideTower.WideExact L →
      TranscriptView.Message BytesMessage → Bool)
    (H : Addr L → State) (pub : LiteralTranscript.Public)
    (pf : UnifiedProtocol.Proof BytesMessage) :
    ∀ q ∈ (eval H (FS2.verifier legacyProtocol dold pub pf)).1,
      CanonicalByteAddress.Canonical q.1 := by
  intro q hq
  rw [FS2.verifier_eval] at hq
  simp only [List.mem_flatten, List.mem_map] at hq
  obtain ⟨tr, ⟨i, _, he⟩, hmem⟩ := hq
  subst tr
  exact RawBoundedProgram.labels_eval CanonicalByteAddress.Canonical
    (legacyProtocol.chain H pub pf i).toProgram (chain_canonical H pub pf i) H q hmem

theorem restricted_trace_eq (decoder : LiteralByteProtocol.Decoder)
    (draw : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool)
    (dold : UnifiedSampler.Prefix BytesMessage AspisWideTower.WideExact L →
      TranscriptView.Message BytesMessage → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (pf i)) :
    RawBoundedTrace.trace L
      (eval H (FS2.verifier (LiteralByteProtocol.protocol decoder) draw pub pf)).1 =
      (eval (fun a => H a.toBytes)
        (FS2.verifier legacyProtocol dold pub (proof pf))).1 := by
  rw [trace_eq_map decoder draw dold H pub pf hvalid]
  exact RawBoundedProgram.trace_map_canonical _
    (verifier_trace_canonical dold (fun a => H a.toBytes) pub (proof pf))

#print axioms trace_eq_map
#print axioms chain_canonical
#print axioms verifier_trace_canonical
#print axioms restricted_trace_eq
end AspisR1.LiteralLegacyVerifierTrace
end
