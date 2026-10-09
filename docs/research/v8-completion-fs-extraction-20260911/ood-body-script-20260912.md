# Same-body OOD answer script bridge

Base revision: `d5fc7315aa3fb1a3caac50b2ac93ab12b65da98b`.

`lean/FSV8OODBodyScript.lean` closes the deterministic gap left by
`FSOODPair.lean`. It does not add a probability theorem.

## Constructed chronology

`checkedBodyPairScript` performs, on one carried full-256 oracle state:

1. the existing three-candidate `circleScript decode 3` first-point sampler;
2. a caller-bounded `Script` that may hash while computing/checking the first
   answer, with only the realised first point as its argument;
3. absorption under label 62 of sample byte 0 followed by the 29 exact
   same-body fields at indices 359 through 387;
4. the existing `distinctScript decode firstPoint 3` sampler, including all
   inner circle retries and all three duplicate-point retries;
5. a second bounded answer script whose explicit arguments are only the two
   realised points;
6. absorption under label 62 of sample byte 1 followed by the 29 exact
   same-body fields at indices 388 through 416.

`lean/FSV7OODBodyScript.lean` instantiates the construction with the already
reviewed `FSV7OODSampler.decodePoint`. Thus the source-shaped script reuses the V7
`c0.a,c0.b,c1.a,c1.b` decoder and secure rational circle map rather than
introducing a second map. The focused leaf remains generic in `decode` so it
can be compiled against the small transcript closure without rebuilding the
6.5 GiB historical V7 arithmetic dependency.

For this concrete instantiation, `successful_source_is_canonical` proves that
every successful raw execution used canonical source limbs, and
`successful_source_points_distinct` projects the nested script execution onto
the existing functional V7 sampler result and applies
`FSV7OODSampler.second_success_distinct`. The latter is a theorem about the
actual successful `sourceScript` result, not a post-hoc checked wrapper and not
a distribution assumption.

Each answer record is assembled from 29 consecutive 16-byte chunks of the
same body. `answer_bytes_size` proves the source record size `1 + 29*16 = 465`.
`CanonicalOODFields` is the literal four-little-endian-limb `< 2147483647`
condition for precisely those 58 fields. `checkedBodyPairScript` aborts before
the OOD transcript slice if it fails, and `checked_success_canonical` derives
the condition on every successful execution. This local guard mirrors the
earlier all-697-field source parser check; it does not claim an Aeneas/Rust
refinement of that parser.

`run_answerScript` proves that an answer builder's successful payload is
replaced by the exact body row while its oracle state is retained unchanged.
Consequently all builder calls, cache hits, fresh calls and abort state are
carried into the following absorption. `body_pair_prefix` and
`body_pair_valid` derive append-only chronology and the existing
cache/log/first-fresh invariant for the complete script, including failure
paths. Static padding performs no dummy oracle call.

The types do not pass the second point, query schedule, later proof fields or
future tape entries into the first builder. As usual for a higher-order Lean
model, a caller could close an arbitrary constant into a supplied function;
the theorem is a source-interface construction, not a language-level
noninterference theorem for opaque closures.

## Focused evidence

Command:

```text
python3 docs/research/v8-completion-fs-extraction-20260911/FocusedLeaves.py --root FSV8OODBodyScript
```

Successful receipt:
`results/v8-completion-fs-extraction-20260911/FSV8OODBodyScript-kh5dvayp/report.json`.

- exact changed target: `FSV8OODBodyScript.lean`;
- exit status: 0;
- target wall time: 0.725 seconds;
- sampled target process-tree peak RSS: 715,568 KiB;
- swap: 0;
- source revision: `d5fc7315aa3fb1a3caac50b2ac93ab12b65da98b` plus this scoped uncommitted leaf;
- toolchain: Lean 4.33.1, commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`;
- memory limit passed to Lean: `-M2048`;
- `#print axioms`: only `propext` and `Quot.sound` for the new results; no
  `sorryAx`.

The runner compiled only the small dependency closure and the changed leaf.
It did not run a package manifest, historical V7 arithmetic replay, Rust/SBF
build, Aeneas replay, or runtime suite. Earlier failed edit snapshots are
retained as diagnostic evidence and are superseded by the receipt above.

The same source was subsequently checked on the historical pinned Lean
4.32.0 toolchain (commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`)
on the NUC through Tailscale.  The focused target exited zero in 0.79 seconds,
used 777,044 KiB peak RSS and zero swap under a 10 GiB cgroup cap, and printed
only `propext` and `Quot.sound`.  Source and artifact hashes and the complete
log are in `results/v8-completion-fs-extraction-20260911/ood-body-pinned-v1/`.

The concrete V7 instantiation was then compiled as the only changed target on
the same pinned toolchain, reusing the existing V7 sampler and generic body
script artifacts. The target exited zero in 3.91 seconds, used 6,522,572 KiB
peak RSS and zero swap under `MemoryHigh=7G`, `MemoryMax=8G`, and
`MemorySwapMax=0`. Its `#print axioms` audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`. Source/artifact
hashes and the complete log are in
`results/v8-completion-fs-extraction-20260911/ood-body-concrete-pinned-v1/`.

## Claims deliberately absent

No sampler independence, uniformity, fresh-exposure law, ROM coupling,
Fiat--Shamir loss, Rust source refinement, evaluation correctness of the 29
answers, accepted-payment theorem or 100-bit security claim is asserted.
Those require the later first-exposure scheduler/probability bridge and the
source evaluation relation, not merely this deterministic chronology.
