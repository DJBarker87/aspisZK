# Chronological authentication answer-prefix producer

Base `93cab4705bc39beb8fb5649c153e2529633e270c`. New leaf:
`lean/FSAuthenticationPrefixes.lean`; prior modules untouched.

## Constructed endpoint

The source-shaped `constructBoth` execution stores complete 256-bit answers.
This leaf derives `(actual_input_bytes, first_26_answer_bytes)` records from
that same log. The truncation is literal `List.take 26 (List.ofFn answer)`,
matching `crates/aspis-core/src/v7_merkle208.rs::truncate_sha256_v7`'s byte
prefix; `truncate_length` proves the exact output length. This is source-shaped
byte correspondence, not a translated Rust theorem.

`projected_cuts` proves both concrete commitment cut lengths are ordered and
that their projected answer records are exact takes of one final projected
log. C1 and C2 cuts remain post-builder/pre-root-absorption; repeated calls are
preserved, not deduplicated. `result_final` derives that the successful returned
RootCuts stores the very same final transcript/oracle returned by execution.

`projected_answers_from_empty` constructs prefix answer consistency with that
same final full-answer cache. `advertised_total_answers_from_empty` supplies
the total-view equality shape consumed by older prefix-authentication lemmas,
without accepting supplied inclusion, answer-consistency or root-equality-only
premises. Inputs are tape, initial digest, bounded C1/C2 producer programs and
success of this independently defined early execution. Cache completeness and
coherence come from the prior constructed execution theorem.

## Important boundaries

The older inspected `AuthenticatedEarlyC1Prefix.lean` imports V7 modules and
uses `RawHashInput`, `Digest208` and `OrderedRawQueryLog`. Those types and their
serialized grammar have NOT been silently equated to this leaf's byte-list
types. Its old `accepted_opening_prefix_or_late_target_or_collision` is not
invoked here. The concrete type/grammar conversion and the later authentication
hash calls still need connecting.

In particular, this final log ends after C2 root absorption; it is not claimed
to contain every eventual proof-opening verification call. Extending this log
through the later source execution and instantiating exact accepted-opening
conditions remains necessary before consuming the old authentication theorem.

No collision-freedom is assumed. Different full hash answers can project to
the same 208 bits, and different inputs can return the same answer. The cache
and full log remain untruncated for the adversary. `totalView208` defaults to a
zero digest only on unobserved inputs, while all advertised-answer equalities
are derived for actually logged inputs. That default supplies no unqueried
random-oracle answer or claimed probability bound.

## Checks and evidence

Focused local command, using previously compiled exact dependency artifacts:

```
LEAN_PATH=/tmp /usr/bin/time -l lake env lean -j1 -M2048 \
  -o /tmp/FSAuthenticationPrefixes.olean FSAuthenticationPrefixes.lean
```

Pinned Lean 4.33.1 / `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
Exit 0; wall 2.69s; peak RSS 686,669,824 bytes; zero swaps. All printed
declarations use only `propext` and `Quot.sound`.
Logs and exact source/import/artifact hashes are under
`results/v8-completion-fs-extraction-20260911/fs-auth-prefix-leaf-20260912/`.
This is focused source-shape checking, not a new independent whole dependency
rebuild or kernel replay; parent integration records that separately.

Executable controls include a true projection collision (answers differing
only in their last six bytes), a successful two-builder execution, C1/C2
prefix lengths 1/7 and final projected log length 8. They demonstrate
nonvacuity and collision tolerance, not an accepted payment or security rate.

No source acceptance/protocol/body/CU changes; no remote jobs, commits or push
by this agent. No global soundness, FS probability or privacy claim added.
