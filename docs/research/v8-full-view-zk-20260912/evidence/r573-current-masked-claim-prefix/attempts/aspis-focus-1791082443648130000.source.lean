import AspisR569MaskedClaimCompleteConsts.Funs
import AspisV8R19.R196CurrentByteWriter
import AspisV8R19.R144BeforeOodBytesBridge
import AspisV8R19.R567ClaimSerializationInjectivity

/-! Draft for the selected masked-claim prefix.  This file is intentionally
uncompiled until the import-only R569 Types/Funs cache target is green.  The
statement retains every generated result/error and transcript state. -/
set_option autoImplicit false
namespace AspisV8R19.R573ClaimPrefixExecution

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open AspisR569MaskedClaimCompleteConsts
open AspisV8R19.R144BeforeOodBytesBridge
open AspisV8R19.R196CurrentByteWriter
open AspisV8R19.R567ClaimSerializationInjectivity

abbrev NQM31 := aspis_core.field.QM31
abbrev NTranscript := aspis_core.transcript.Transcript
abbrev NChallengeError := aspis_core.transcript.ChallengeSampleExhausted
abbrev NScheduleError := aspis_core.state_only_hiding.StateOnlyHidingScheduleError

def toCurrent (q : NQM31) : AspisR156FullFreeze.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def claimBytes (q : NQM31) : List U8 :=
  27#u8 :: 10#u8 :: qm31Bytes (toBefore (toCurrent q))

def scheduleResult : core.result.Result NQM31 NChallengeError →
    core.result.Result NQM31 NScheduleError
  | .Ok v => .Ok v
  | .Err _ => .Err .ChallengeSampleExhausted

def nativeAddress (t : NTranscript) (q : NQM31) : List U8 :=
  t.state.val ++ [0#u8, 31#u8] ++ claimBytes q

/- The following proof bodies are completed only after the R569 focused cache
is available.  They are written as named obligations rather than admitted
axioms: (1) unfold the four-field writer bridge to R196; (2) use
current_writer_exact for the final sixteen bytes; (3) normalize the two literal
array updates (27,10), `Array.to_slice`, and `map_err`; (4) use `Subtype.ext`
to replace the generated record slice with arbitrary `data` of equal `.val`.
The sampler is kept opaque. -/

theorem writer_bridge (q : NQM31) (out : Slice U8) :
    aspis_core.field.QM31.write_le_bytes q out =
      AspisR156FullFreeze.aspis_core.field.QM31.write_le_bytes (toCurrent q) out := by
  rfl

theorem new_writer_exact (q : NQM31) (out : Slice U8)
    (hout : out.length = 16) :
    aspis_core.field.QM31.write_le_bytes q out
      ⦃ r => r.val = qm31Bytes (toBefore (toCurrent q)) ⦄ := by
  rw [writer_bridge]
  exact current_writer_exact (toCurrent q) out hout

theorem toCurrent_injective : Function.Injective toCurrent := by
  intro x y h
  cases x with
  | mk x0 x1 =>
    cases y with
    | mk y0 y1 =>
      cases x0 with
      | mk x00 x01 =>
        cases y0 with
        | mk y00 y01 =>
          cases x1 with
          | mk x10 x11 =>
            cases y1 with
            | mk y10 y11 =>
              have h00 : x00 = y00 := by
                simpa only [toCurrent] using
                  congrArg (fun z : AspisR156FullFreeze.aspis_core.field.QM31 => z.c0.a) h
              have h01 : x01 = y01 := by
                simpa only [toCurrent] using
                  congrArg (fun z : AspisR156FullFreeze.aspis_core.field.QM31 => z.c0.b) h
              have h10 : x10 = y10 := by
                simpa only [toCurrent] using
                  congrArg (fun z : AspisR156FullFreeze.aspis_core.field.QM31 => z.c1.a) h
              have h11 : x11 = y11 := by
                simpa only [toCurrent] using
                  congrArg (fun z : AspisR156FullFreeze.aspis_core.field.QM31 => z.c1.b) h
              cases h00; cases h01; cases h10; cases h11; rfl

theorem claimBytes_injective : Function.Injective claimBytes := by
  intro x y h
  apply toCurrent_injective
  apply current_qm31_bytes_injective
  have htail := (List.cons.inj h).2
  simpa only [claimBytes] using (List.cons.inj htail).2

theorem nativeAddress_injective (t : NTranscript) :
    Function.Injective (nativeAddress t) := by
  intro x y h
  apply claimBytes_injective
  apply (List.append_right_inj (t.state.val ++ [0#u8, 31#u8])).mp
  simpa only [nativeAddress, List.append_assoc] using h

@[step] theorem new_writer_exact_step (q : NQM31) (out : Slice U8)
    (hout : out.length = 16) :
    aspis_core.field.QM31.write_le_bytes q out
      ⦃ r => r.val = qm31Bytes (toBefore (toCurrent q)) ⦄ :=
  new_writer_exact q out hout

theorem begin_exact (t : NTranscript) (q : NQM31) (data : Slice U8)
    (hdata : data.val = claimBytes q) :
    aspis_core.state_only_hiding.begin_state_only_masked_sumcheck t q = (do
      let t1 ← aspis_core.transcript.Transcript.absorb t 31#u8 data
      let (r, t2) ← aspis_core.transcript.Transcript.challenge_nonzero_qm31 t1
      ok (scheduleResult r, t2)) := by
  unfold aspis_core.state_only_hiding.begin_state_only_masked_sumcheck
  simp only [aspis_core.state_only_hiding.STATE_ONLY_HIDING_MASKED_ORACLE_DEGREE,
    aspis_core.state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS,
    aspis_core.transcript.label.M31_STATE_ONLY_HIDING_MASK_CLAIM]
  simp [lift, UScalar.cast, Array.to_slice, Array.update,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut]
  generalize htail : Slice.drop _ 2#usize = tail
  have hlen : tail.length = 16 := by
    simp [← htail, Slice.length]
  have hwriter := new_writer_exact q tail hlen
  cases hw : aspis_core.field.QM31.write_le_bytes q tail with
  | fail e => simp [hw] at hwriter
  | div => simp [hw] at hwriter
  | ok written =>
      simp [hw] at hwriter
      have hwlen : written.val.length = 16 := by
        rw [hwriter]
        exact qm31Bytes_length _
      have hrecord :
          (⟨([27#u8, 10#u8] ++ List.replicate 16 0#u8).setSlice! 2 written.val,
            by scalar_tac⟩ : Slice U8) = data := by
        apply Subtype.ext
        calc
          ([27#u8, 10#u8] ++ List.replicate 16 0#u8).setSlice! 2 written.val =
              [27#u8, 10#u8] ++ written.val := by
                rw [setSlice_append_replicate _ _ _ 16 (by rw [hwlen])]
                simp [hwlen]
          _ = claimBytes q := by simp [claimBytes, hwriter]
          _ = data.val := hdata.symm
      have hmap (t1 : NTranscript) :
          (do
            let x ← aspis_core.transcript.Transcript.challenge_nonzero_qm31 t1
            let r1 ← core.result.Result.map_err
              (BuiltinFnOnce NChallengeError NScheduleError) x.1
              aspis_core.state_only_hiding.StateOnlyHidingScheduleError.Insts.CoreConvertFromChallengeSampleExhausted.from
            ok (r1, x.2)) =
          (do
            let (r, t2) ← aspis_core.transcript.Transcript.challenge_nonzero_qm31 t1
            ok (scheduleResult r, t2)) := by
            simp [scheduleResult, core.result.Result.map_err]
      simpa only [bind_tc_ok] using congrArg
        (fun input : Slice U8 => do
          let transcript1 ← aspis_core.transcript.Transcript.absorb t 31#u8 input
          let x ← aspis_core.transcript.Transcript.challenge_nonzero_qm31 transcript1
          let r1 ← core.result.Result.map_err
            (BuiltinFnOnce NChallengeError NScheduleError) x.1
            aspis_core.state_only_hiding.StateOnlyHidingScheduleError.Insts.CoreConvertFromChallengeSampleExhausted.from
          ok (r1, x.2)) hrecord |>.trans (by simp [hmap])

end AspisV8R19.R573ClaimPrefixExecution
