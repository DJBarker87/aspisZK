# Actual bounded transcript functions now have causal Script producers

Base: `7e947e6a983d3e079ca67217bd9753351a398b7a`.
New source only: `lean/FSTranscriptScript.lean`; earlier FS modules unchanged.

## Endpoint

The earlier `FSFirstFresh` result applied to `Script.run`, while the actual
source-shaped `FSBoundedTranscript` samplers were independent functions.
That was a real composition gap. This leaf constructs scripts for absorb,
squeeze, buffered word consumption, each eight-attempt limb, all four limbs,
and the complete QM31 challenge. It proves equality with the corresponding
existing functions for **arbitrary tape and initial cache/log/state**.

The result equality includes the return value, transcript digest, full cache,
next tape index and entire chronological log. No coherence certificate or
successful sampler result is a premise. A sampler rejection is represented by
the returned inner `none`, with precisely its consumed state. The script's
outer `some` means the bounded interpretation ran, NOT that sampling succeeded.

`constructBoth_valid_from_empty` consequently proves that the actual
`FSBoundedTranscript.constructBoth` path preserves complete/coherent history
and chronological freshness flags, including both commitment-building scripts,
both challenges, cached repeats and every abort branch. Its only inputs are
the tape, initial digest and two causal root-building programs.

`constructBoth_first_fresh` applies that constructed invariant: a recorded input
in the actual two-commitment path has a genuinely fresh first logged occurrence.
No caller-supplied freshness or source/script equality is required.

## Causal/resource details

`promote`/`pad` change only static budgets and perform no dummy hash calls.
`bind` executes its continuation only if the first script returns, on exactly
the first script's returned oracle. All continuations inspect previous results,
not a completed proof body or future tape.

The sampler script has a conservative 66-call allowance, proved also for the
existing source-shaped function by `challenge_call_allowance`. It comes from
allowing two calls for every possible word read plus the first block, not a
measurement and not a tight claim that the source performs 66 hashes. The
buffered implementation generally uses far fewer. This allowance is not a
security-error multiplier or a CU forecast.

## Checks and provenance

Commands ran in the pinned local Lean folder, `lake env lean -j1 -M2048`,
using Lean 4.33.1 / `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
The four first-party dependencies were compiled into `/tmp` earlier this task;
their source/artifact hashes are recorded. Std is the installed pinned cache.
This is focused leaf evidence, NOT a fresh complete release rebuild.

Final command:

```
LEAN_PATH=/tmp /usr/bin/time -l lake env lean -j1 -M2048 FSTranscriptScript.lean
```

Exit 0; wall 3.83s; peak RSS 678,772,736 bytes; zero swaps. Durable log:
`results/v8-completion-fs-extraction-20260911/fs-script-leaf-20260912/compile.log`.
Sibling `import-provenance.sha256` records sources and imported artifacts.

`run_absorb` and `run_squeeze` are axiom-free. `run_challenge` uses `propext`.
The constructed-history/freshness endpoints use only standard foundations
`propext`, `Classical.choice`, `Quot.sound` (exact lists in log).

Exact executable controls include canonical zero challenge success and
all-255 first-limb exhaustion, retaining two squeeze/advance calls. Generic
symbolic proofs cover retry/refill/abort cases; tests do not replace those proofs.

Local development failures were elaboration issues: an ambiguous `Oracle`
namespace, a missing induction generalization and nested match normalization.
They were fixed locally without altering the target equality or source behavior.
No broad historical replay, deployment, production edit or protocol change ran.

## Remaining boundary

This connects the existing source-shaped functions to the cached causal model.
It is not a Rust/Aeneas operational-semantics proof. It does not yet produce
the complete selected verifier/adversary program or the later nonzero, OOD,
query and semantic/relation stages. The digest at the empty-start endpoint is
a raw initial input; authentic profile/statement preparation must be constructed
or passed from an already proved coherent earlier execution.

Fresh flags are deterministic evidence of tape consumption, NOT yet conditional
uniformity. The probability law, adversarial prequeries/retries/restoration
coupling, extraction resources and global probability composition remain open.
No grinding credit, global security claim, proof-body or acceptance change.
