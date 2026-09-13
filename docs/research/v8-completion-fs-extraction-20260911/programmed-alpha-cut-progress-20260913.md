# Programmed alpha-cut progress — 2026-09-13

## Result

The successful exact-root bridge now has the operational machinery needed to
cut a compiled verifier run at a causal `Script.bind` while retaining
programmed cache entries.  The new results do not require the prefix to use
its entire static query allowance and do not assume a globally unprogrammed
oracle.

The checked chain is:

1. `runMachine_bind_returned_split` decomposes a normally returned compiled
   machine bind into its actual returned prefix and continuation.  The
   continuation receives `fuel - prefix.steps`; final oracle and step counts
   are preserved.
2. `returned_compileScript_aligned_with_fuel` proves finite-tape/programmed
   alignment for any normally returned compiled `Script`, with arbitrary
   supplied fuel.  Normal return, rather than a static room premise, supplies
   the executed-branch fuel fact.
3. `returned_bind_constructs_programmed_cut` combines those results and
   constructs the finite result and programmed-aligned state at the cut.
4. `returned_preAlpha_constructs_programmed_marker_cut` factors the actual
   pre-alpha grammar and constructs the `BeforeAlphaMarker` value, its own
   returned digest, the aligned marker state and the successful one-query
   continuation.
5. `returned_factoredMiddle_constructs_preAlpha_cut` lifts the result to an
   accepted source-shaped factored middle and retains the post-alpha
   continuation.

These are deterministic execution/refinement lemmas.  They assign no
probability to the alpha request and do not yet claim that the internal middle
cut has been derived from every accepted exact-root run.  The next bridge is
the structural descent through `factoredWholeStagedScript` and
`factoredPrefixMiddleScript`, after which the exact marker request can be fed
to the programmed target/disposition law.

## Evidence

Focused Lean 4.32.0 jobs ran on the NUC through Tailscale in individual
systemd user scopes with `MemoryHigh=8G`, `MemoryMax=9G`,
`MemorySwapMax=0`, and `RuntimeMaxSec=600`.

| Leaf | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8SuccessfulProgrammedAlignmentFuel.lean` | 0 | 2.56 s | 6,552,520 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8SuccessfulBindPrefix.lean` | 0 | 2.63 s | 6,556,944 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8ReturnedBindMachineSplit.lean` | 0 | 2.60 s | 6,534,800 KiB | 0 | `propext`, `Quot.sound` |
| `FSV8SuccessfulProgrammedBindCut.lean` | 0 | 2.61 s | 6,551,076 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8ProgrammedBeforeAlphaMarkerCut.lean` | 0 | 2.68 s | 6,758,652 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8ProgrammedMiddlePreAlphaCut.lean` | 0 | 2.70 s | 6,753,608 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |

`FSV8SuccessfulBindPrefix.lean` is the narrower exact-static-budget
predecessor.  No complete manifest replay was performed because only focused
leaves changed.

## Security implication and boundary

This closes the generic operational objection that a programmed/cached alpha
path cannot be cut without assuming fresh-only state or worst-case unused
fuel.  It does **not** yet close the alpha probability event: the whole-root
to-middle structural descent and the actual target/disposition inclusion are
still required.  Extraction, global probability composition, and literal
Rust refinement remain unchanged obligations.
