# Source-run first25 frame identity

`SourceFull25.calls_of_run` constructs its log directly from the actual ordered
`BeginCalls.SemanticRun`: each cell retains that exact validated record, its
actual array slot, before/after transcripts, absorb/read1/read2 Digest32 calls,
actual QM31 sampler result, and carried successor. `run_full25_frames` proves
that log's framed slices equal the same Prefix array's first25 slices when the
actual row schedule is0 through24. No byte-equality premise is assumed.

This is a generic source lemma. It still requires A's actual post-begin tail
success result to supply rows15–24. It does not yet construct bounded selected
`Rec Message` values or identify selected table/oracle/init/context/C1/C2 data,
`htyped/ha`, or the requested actual `semChalsZ_read.hread`.

The accepted Transcript, Callers and Begin sources were refreshed against the
same a2b07cd9/c3dd345a carrier used by the current caller-prefix checkpoint.
The source declarations are repinned by its58-cut kit, retaining the new lead's
begin `inline(never)` attribute; the generated function bodies are unchanged.
There is no new QM31 model or sampler implementation.

| Exact target | Exit | Wall s | Peak RSS KiB | Swap | Axiom reports |
|---|---:|---:|---:|---:|---:|
| ExtractedDigest32Transcript |0|4.655|2650004|0|5|
| ExtractedDigest32Callers |0|3.734|2651840|0|11|
| ExtractedDigest32Begin |0|12.867|2750468|0|4|
| ExtractedSourceFull25Frames |0|2.533|2647924|0|4|

All24 reports use standard Lean axioms only. The sole Lean process ran in a
6GiB-high/8GiB-max/swap0 scope with atomic external-Lean suppression and arrival
monitoring. The original local structure-field/list-case proof failure is
retained as a failed receipt and excluded from acceptance. The corrected source
was checked; no unchanged rerun was used to erase the failure.

The76-member archive SHA256 is
`01d647db1554844ce984a78005cc74dd24cd79d4f9c3a6de694efe31e6f611aa`.
`manifest.json` and the archive retain exact commands, source revisions,
producing/import/object pins, failures, times, RSS, swap, limits and axiom logs.
Run `python3 verify.py` for a read/hash-only verification; it invokes no Lean,
Rust, runtime harness or SBF rebuild.
