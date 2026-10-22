# Checkpoint ordered effects fifth packet

Branch `codex/cx-ckpt-bytes5-20261022`. Additive modules only; work in progress.
No final source-stage join is claimed until its statement compiles.

The 03:00 success-conditioned ruling and 04:20 ordered-effect obligation apply.
The retained source callback-content/P6 boundary is unchanged. Every inner
source error, including Allocation, rejects. No allocation-availability premise.

Plan: first a reusable ordered state lift and source reconstruction, then
successful trace/content adoption, then the reached/strict/decision consumer.
D138's generic state equations are reused in shape; its privacy extraction
imports are intentionally avoided in this local soundness dependency cone.
No shipped change, existing Lean edit, shared object overwrite, host env J,
wallet/key operation, push or merge is authorized by this packet.

## Stage 1: reusable ordered state interpreter

`CheckpointBytes5Effect` reifies pure Result steps and digest reads, interprets
those reads into `(digest, appended ordered log)`, and proves generic bind,
lift, read, and erasure equations. `run_success` proves successful logged
execution erases to the identical Result value. Inner Error values retain
history; no oracle consistency or output equality hypothesis enters this lemma.

Effect-4 accepted: exit 0, 2.5499772909097373 seconds, peak RSS 2263072768
bytes, swaps 0, ten standard-axiom reports. Exact target, source revision,
source/import hashes, dependency fingerprint, command and reports are in
manifest.json and the receipt. Earlier elaboration/parse failures are retained
and excluded. Source resume reconstruction is still being checked; its first
two diagnostics do not count as proved results. No option or resource cap rose.

## Stage 2: complete retained resume reconstruction and exact log

`CheckpointBytes5Resume.source` kernel-checks erasure of the mechanically
reified instruction schedule against the complete retained resumeWithOps.
`CheckpointBytes5Trace.successful_log` strengthens the old three-call
inventory with an exact execution equation for arbitrary initial history.
The digest-free suffix includes comparison, every field read, canonicality,
query validation, fallible allocation, mutable weight writes and final cursor.
The three digests are appended in proof/public/checksum order, with no other
reads and no continuation resetting history. The theorem assumes actual
successful execution, not trace equality. Source inner errors still reject.

Accepted Resume-7: exit 0, 13.884923791978508 s, 2309373952 B RSS, swaps 0.
Accepted Trace-2: exit 0, 3.986098083201796 s, 2291089408 B RSS, swaps 0.
Effect-5 is current after generic conditional-observation equations were
added: exit 0, 2.769025417044759 s, 2265530368 B RSS, swaps 0.
Every theorem has a standard-axiom report; exact revisions/hashes/commands
and failed diagnostics remain in manifest.json. Recursion failures were
replaced by a named pure tail and per-bind congruence, without raising limits.
Writer effects, byte-input normalization and final stage composition remain.

## Stage 3: writer, authentic inputs and actual returned-state interpretation

`CheckpointBytes5Writer.writer_effects` proves the writer's three ordered
reads and authentic C5 encoding from the source selector's canonical input
fields. It uses source_body_c5, with the selector kept irreducible during
composition. The result is the actual writer slice used as the resume input.
`CheckpointBytes5Inputs.calls_inputs`/`calls_observation` identify proof/public
and checksum addresses from the retained source Calls, including exact checked
subtraction and prefix slice contents, not merely their widths.
`CheckpointBytes5Output.fields_observation` interprets actual returned raw
limbs numerically modulo p; canonical saved limbs roundtrip, and all returned
queries/accumulator fields agree. No choice-based output identification.

Accepted Writer-5: exit 0, 21.72884975001216 s, 3674685440 B RSS, swaps 0;
Inputs-2: exit 0, 11.35070116724819 s, 3663888384 B RSS, swaps 0;
Output-4: exit 0, 5.308121291920543 s, 3673571328 B RSS, swaps 0.
All new theorem reports standard, exact provenance in manifest.json.
The native direct writer-call schedule is checked read-only in
source-schedule.json. This audit is not a new physical Rust Vec owner theorem.
No per-call implementation changed; prior native operation gates are reused,
not represented as kernel axioms. No shipped file changed, hence no ELF gate.
The composed source stage and decision consumer are still being checked.

## Stage 4: success-conditioned reached checkpoint stage join

`CheckpointBytes5Join.successful_fields_and_reads` consumes the writer result
as the reader argument, derives authentic encoding, consumes
successful_saved_fields, derives allocation success, and proves the six reads.
`successful_stage` interprets actual returned source limbs and all queries;
that returned state drives advance by twelve. `error_rejects` maps every
source inner Error, including Allocation, to rejection. The final reached
join derives distinct queries from the actual reached decoder, then consumes
strictStage and reached_stage. No availability or collision-free premise.

Accepted Join-7: exit 0, 18.082328415941447 s, peak RSS 3680419840 B,
swaps 0. All five defining-module reports are standard. Exact command,
source revision, hashes, dependency fingerprint and full axiom lines are in
the receipt and manifest.json. Failed attempts remain explicitly excluded.

The remaining refinements are exactly **S2S10CallerBinding** and
**S1S7S8StateProvenance**, at the retained callback/content P6 boundary.
The first contains proof/public carrier identities and per-call ROM dictionary
interpretation. The second contains canonical **input** saved-ten fields,
variant, widths, next, and their reached-model provenance. Neither contains
source-output equality, log equality, ordered-read coverage, or observation
equality. Reached parser/query facts and successful source execution are
execution-context/conditioning facts, not additional refinement hypotheses.
These structures are not claimed to be instantiated for the frozen caller.
The physical native Vec/allocator/frozen-carrier interpretation remains the
same explicit P6 trust boundary as in bytes4; no new kernel Rust extraction
or whole-verifier AcceptedRunJoin is inferred from this content-stage result.

Verbatim established reached-stage statement:

```lean
theorem success_conditioned_checkpoint_stage_join {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (reserved : Bool) (wp : CheckpointBytes5Writer.Prepared) (wa : CheckpointBytes5Writer.Accumulator)
    (proof public1 : Slice U8) (stored : Bytes) (parsed : OraclePortCompactDraft.Parsed)
    (q : Fin 22 → Fin 262144) (tr : ErasedPrefix) (i : SourceInputs) (v : LiteralOpeningView.View)
    (input : OraclePortStoredDecisionDraftC4.input parsed q tr = some i)
    (query : OraclePortSelectedDraft.queries tr = some q)
    (caller : S2S10CallerBinding D hash H proof public1 stored tr.statement.pubBytes)
    (provenance : S1S7S8StateProvenance wp wa
      (prepared (OraclePortAcceptedContextC6.context parsed i v) i.data
        (SelectedChallengeMap.rhoOf i.rho) q)
      (OraclePortCheckpointStateC3.write (model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (p : verifier.Prepared) (a : verifier.Accumulator) (after : Log)
    (success : run D hash (stage reserved wp wa proof public1) [] = ok (.Ok (p,a),after)) :
    (observe after,some (resumedSource i.data p a)) =
      eval H (OraclePortFrozen2.checkpoint stored parsed q tr i v)
```
