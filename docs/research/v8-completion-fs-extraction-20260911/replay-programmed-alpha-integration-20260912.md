# Replay-programmed alpha reaches the literal sampler

Status: **PASS for the deterministic replay/sampler interface only**.

This milestone closes the previously recorded gap between installing a
programmed answer in the V7 start-only replay constructor and consuming that
answer through V8's literal nonzero-QM31 alpha sampler.

## Proved

`V7FsStateRestorationCoupling.constructLegalReplay_programmed_lookup` proves
that a successful legal replay retains the programmed answer as the first
lookup result at the exact transcript-driving input in the replay's final
oracle table.  The proof uses the append-only table invariant and first-match
lookup semantics; it does not assume the lookup as a coupling field.

`FSV8AlphaReplayCandidateIntegration.legal_replay_programming_drives_alpha_candidate`
specialises that invariant to the source-derived alpha boundary and canonical
QM31 output.  Running the literal candidate sampler against the projected
final replay oracle returns the programmed field value.

## Scope and remaining obligations

This result proves neither that the collector requests the canonical 29-by-4
configuration matrix nor that all selected cells share the required common
pre-alpha chronology.  It assigns no probability to prior-target, absent,
collision, replay failure, or incomplete-collection events.  Permitted-access
payment extraction, the total accepted-execution partition, and the global
`< 2^-100` composition remain open.

The V7 file change adds generic proof lemmas only.  It changes no protocol,
parser, transcript, verifier acceptance, or deployed implementation.

## Focused checks

Pinned Lean: `4.32.0`.  The union cache was reused; this was not a clean
first-party dependency rebuild.

```text
lean -j1 -M7500 -o <union-cache>/AspisFormal/K1/V7FsStateRestorationCoupling.olean \
  AspisFormal/AspisFormal/K1/V7FsStateRestorationCoupling.lean
exit 0; 9.03 s; max RSS 5,640,568,832 bytes; swap 0

lean -j1 -M7500 \
  docs/research/v8-completion-fs-extraction-20260911/lean/FSV8AlphaReplayCandidateIntegration.lean
exit 0; 12.09 s; max RSS 5,608,390,656 bytes; swap 0
```

Both promoted declarations report only `propext`, `Classical.choice`, and
`Quot.sound`.  The retained sources contain no `sorry` or new `axiom`.

