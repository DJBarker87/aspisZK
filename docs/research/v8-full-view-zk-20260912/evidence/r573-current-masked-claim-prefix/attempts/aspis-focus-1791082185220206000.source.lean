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
              simp only [toCurrent] at h
              rcases h with ⟨h00, h01, h10, h11⟩
              simp [h00, h01, h10, h11]

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

/-
Target theorem after the generated cache is available:

  theorem begin_exact (t : NTranscript) (q : NQM31) (data : Slice U8)
      (hdata : data.val = claimBytes q) :
    aspis_core.state_only_hiding.begin_state_only_masked_sumcheck t q = do
      let t1 ← aspis_core.transcript.Transcript.absorb t 31#u8 data
      let (r, t2) ← aspis_core.transcript.Transcript.challenge_nonzero_qm31 t1
      ok (scheduleResult r, t2)

The final proof must preserve every failure from `absorb`, every sampler result
including exhaustion, and the returned transcript state.  It must not unfold
`challenge_nonzero_qm31`.
-/

end AspisV8R19.R573ClaimPrefixExecution
