# R15 universal schedule extension and experiment boundary

Date: 2026-09-19. Base revision:
`b520113dcbca1e2dbcf8fa5d8b2793fe17038223`.

## New formal result

`lean/AspisV8R15/RawScheduleExtension.lean` proves
`zero_extension_exact`: over any commutative ring, the two-fibre four-slot
statistic equals its zero-extended statistic on **every** injective containing
schedule, of any size and order. No uniformity, independence, public-query
selection or adaptivity restriction is a premise.

`q4_q6_zero_extension` instantiates the result at 22 queries, fibres 4 and 6,
and the literal eight certificate scalars. Thus authenticated mask-annihilator
and target-statistic identities on that pair transfer without change to any
such schedule. The leaf does not formally prove the Rust encoder's certificate
products or the event probability; those remain separate from this algebra.

Focused command, in the existing `/Users/dominic/ZK/AspisFormal` cache:

```sh
/usr/bin/time -l lake env lean -j1 -M1800 \
  /Users/dominic/ZK/.worktrees/ZK-v8-privacy-repair-20260913/docs/research/v8-full-view-zk-20260912/lean/AspisV8R15/RawScheduleExtension.lean
```

Final leaf: exit 0, wall 11.02 s, peak RSS 1,379,647,488 bytes, swaps 0.
Both endpoints print exactly `[propext, Classical.choice, Quot.sound]`.
No `sorry`, added axiom, unchecked computation or production change.

Retained failed preflight: importing all of `Mathlib.Tactic` caused the Lean
memory cap to terminate the process (exit 134; wall 21.17 s; peak RSS
2,372,075,520 bytes; swaps 0). The replacement removed that unused broad
import instead of raising the cap. The reduced-import generic predecessor
then compiled (exit 0; 5.35 s; 1,379,958,784 bytes; swaps 0), before adding the
literal coefficient instantiation and performing the final leaf check above.
No package-wide or unchanged full replay was run.

## The authenticated host is not the intended experiment

The now-recovered v4 host uses fixed repeated-byte attempt secrets and an
in-memory nonce store. Its `live_context.rs` loader also constructs fixed
note secrets, a single-output leaf, and `selected_second = false`; it does
not accept either member of the arbitrary two-witness challenge game.
The live loader's SHA-256 is
`6c71cdf5e5677761b638e8532981ca7f75b1387475b31d821bf4775431780bd2`,
verified equal to the selected `9e432896` Git blob. The extended
`tools/audit_r15_q22_source_slice.py` checks these facts in addition to host
reconstruction. This is source-text evidence, not an entropy distribution
or a compiled generated-host run.

An exhaustive search of locally reachable Git blob versions at the three
missing-preimage paths checked 16 dispatch versions, 20 verifier-lib versions,
and 2 harness-main versions. None matched the respective retained SHA-256
pins. No pin was waived or replaced, and no remote artifact was assumed.

The old `SAME_PUBLIC_ATTACK.md` had overstated the ideal uniform-subset
calculation as a completed actual-source advantage claim. Its scope is now
corrected; the negative certificate and source regressions are retained.

## Next source work

Determine whether the authenticated host-only dependency subset can run in
an isolated research harness without the three verifier/harness preimages.
If so, first replay the unchanged host, then explicitly distinguish any
test-only witness/entropy/oracle hooks from the pinned program. A controlled
oracle fixture can demonstrate a concrete execution, not establish its
probability in the real shared-oracle experiment. No full privacy claim or
production adapter change follows from this step.
