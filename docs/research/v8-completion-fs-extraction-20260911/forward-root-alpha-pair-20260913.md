# Forward V8 root and alpha-pair checkpoint

Status: **proved source-root and pair-input interfaces; atomic restoration
continuation still open**.

Base revision: `69f14b835ba283a1e8e0bc289dcc80dd9560d574`.

## Why the previous reverse route stops

A completed `SuccessfulReplay` cannot determine a nonanticipating pre-fork
random-oracle strategy.  Its `constructLegalReplay` state is already after
programming the alpha-output coordinate, and its arbitrary
`postForkController` need not give one fixed answer to the unobserved
transcript-advance coordinate on every counterfactual continuation.
`ProjectionFacts` aligns the realised post-programming execution only.  It
does not identify that counterfactual pair law.

The existing total configuration classifier correctly retains the further
case in which a requested replay input differs from the actual alpha input.
Consequently no theorem from the current checked-cell inputs alone can
construct the required pre-fork cursor.

## New forward source root

`FSV8ExactRootCursor.lean` constructs the missing earlier object directly:

1. it starts the hidden-tape adversary from the literal empty oracle;
2. its callback passes exactly the adversary-returned body to
   `wholeStagedScript` through `compileScript`;
3. its returned `Runtime.output` is dependently indexed by that same body;
4. `sourceOrigin` packages the identical hidden start for the existing
   start-only collector;
5. `runExactRoot` runs this cursor on the exact compiler's one uniform master
   tape;
6. `run_exact_root_trace_is_erased_exposure_trace` proves that the causal
   exposure trace is the erasure of that same result-carrying execution; and
7. the existing exact-count and raw causal-target probability bounds apply to
   this V8 cursor without importing V7's hard-wired future-free verifier.

This closes construction of a same-body V8 *root cursor*.  It does not yet
install the restoration client, prove that the root returns successfully, or
bound the separate algebraic bad-alpha event.

## Exact alpha pair

`FSV8ActualAlphaAtomicPairInputs.lean` proves that the actual candidate
squeeze begins with the adjacent inputs

```text
digest ++ [1]
digest ++ [2]
```

and that they are distinct.  The continuation is answer-dependent.  For an
actual aligned successful legal replay, its driving input is exactly the
first input, and its final table contains the programmed fork output at that
input.

This is not a `PreparedConcreteRestoration`: the current V8 execution does
not produce V7's `RawVerifierExecution`, `ConcreteRestorationNode`, or indexed
`FutureFreeTransition`, and its retained replay state is too late to serve as
the pre-programming base.

## Finite-tape scheduler segment

`FSV8FiniteTapeSchedulerSegment.lean` proves controller equality only on
reachable history extensions, then relates the global finite-tape machine to
the dropped answer suffix and the scheduler's literal continuation.  It does
not assert equality of the two controllers on arbitrary histories.  Its last
theorem currently consumes an executable successful projected-prefix result;
construction of that result from a returned machine is the next local seam.

## Probability separation

The exact-compiler causal target event bounds full-digest/cached/late-target
hazards in the erasure of the forward root cursor.  It does **not** include the
field-algebraic bad-alpha root event.  That event still needs the live V8
three-attempt nonzero script packaged into V7's variable-prefix duplex
skeleton, followed by the corresponding pushforward/conditional-law theorem.

## Remaining producer

The next global constructor must be forward and executable.  Starting from
`runExactRoot`, it must locate the actual alpha squeeze in the returned root,
emit `.forkPair` before either coordinate is programmed, use the two adjacent
master-tape answers, replay the hidden-tape adversary, and run the selected
same-body V8 verifier on the returned body.  A successful collected cell must
then be shown to be the cell produced by this continuation.  Caller-supplied
configuration alignment, cursor existence, terminal equality, or a completed
replay are not acceptable substitutes.

## Focused checks

All checks used Lean 4.32.0 with the pinned union cache and a 7.5 GiB process
limit, one process at a time.

| Leaf | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8ExactRootCursor.lean` | 0 | 12.20 s | 5,791,793,152 B | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8ActualAlphaAtomicPairInputs.lean` | 0 | 12.15 s | 5,694,078,976 B | 0 | same standard set |
| `FSV8FiniteTapeSchedulerSegment.lean` | 0 | 21.30 s | 5,710,708,736 B | 0 | final theorem: same standard set |

No complete dependency replay, Rust/Aeneas refinement, global probability
composition, or payment extraction test was run at this checkpoint.
