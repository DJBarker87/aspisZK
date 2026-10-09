# Programmed extraction replay to source `SuccessfulReplay`

Status: checked deterministic bridge.  It does not yet construct the replay
matrix, its common fork boundary, or the global random-oracle probability law.

## Result

The older `FSV8V7WholeScriptAlignment.StateAligned` excluded every oracle
containing a programmed entry.  That made it inapplicable to the extraction
forks: the fork output is installed in the oracle table before the verifier
continues.

`FSV8V7ProgrammedAlignment.lean` removes only that restriction.  Its alignment
relation projects every actual table entry into the functional cache.  A read
of either a previously fresh or a programmed entry is a cache hit and consumes
no fresh answer.  Only a missing input consumes the next element of the finite
fresh-answer tape.  Structural induction on `Script` proves exact result and
final-state alignment, including abort.

`FSV8ProgrammedProjectionAlignment.lean` constructs that relation from explicit
operational history facts.  It retains programmed cache entries while matching
the genuinely fresh chronological history to one explicit finite tape.

Finally,
`ExtractionCollectorVerifiedSuccessfulReplay.checked_cell_constructs_successfulReplay`
starts from a `CheckedCell`.  Such a cell contains the equality showing that
`verifiedSourceAttempt` actually produced it.  The theorem:

1. reconstructs the legal operational replay;
2. obtains its exact returned body and normally returned selected-verifier
   output;
3. aligns that machine run with `wholeStagedScript` on the projected state;
4. excludes the functional-abort branch from the observed machine return;
5. constructs the existing `SuccessfulReplay` using the functional run; and
6. proves that the successful replay used the submitted body and that its body,
   record and final digest reconstruct the cell's complete accepted value.

The theorem does not accept a `SuccessfulReplay`, source-run success, body
equality, record equality, or final-digest equality as a premise.

It does accept a `CheckedCell`, whose dependent `checked` field proves that
the actual `verifiedSourceAttempt` and selected checker produced that cell.
Thus checker acceptance is visible in the input; what is newly constructed is
the corresponding functional `wholeStagedScript` run under programmed-oracle
alignment.  The hostile premise review found no hidden body/source equality,
but specifically rejects describing this as success independently of the
checked-cell premise.

## Premise boundary

The following premises remain real producers for the eventual adaptive
Fiat--Shamir theorem:

| Premise | Meaning | Current producer status |
|---|---|---|
| `CheckedCell.checked` | the actual replay plus selected verifier produced this checked cell | constructed by `verifiedAttempt`; matrix generation still separate |
| `boundaryFacts` | replay-final history/cache/fresh counts project to the stated finite tape | explicit interface; global ROM execution must construct it |
| `totalRoom`, `freshRoom`, `tapeRoom` | this verifier continuation fits declared call/fresh/tape bounds | explicit resource obligations; not inferred here |
| `tape`/`finiteTape` | the functional infinite tape and the controller's finite tape agree on the available prefix | explicit; the random uniform law is not asserted by this deterministic theorem |

These premises are not source-success conclusions, but the last three rows are
still part of the missing actual causal-distribution coupling.  A caller cannot
use this theorem to claim that an arbitrary `CompleteMatrix` was generated, or
that four alpha cells share one pre-alpha history.

## Alpha boundary

`FSV8AlphaChallengeInputBridge.lean` separately identifies the first alpha
candidate input from the real `candidateScript` as the post-nonce digest bytes
followed by tag byte `1`.  It constructs configurations which differ only in
their programmed fork output.  It intentionally does not yet prove that a
completed source run constructs that post-nonce transcript or that the four
operational replays share its pause.

## Focused evidence

Pinned Lean 4.32.0, union cache, `-j1 -M7500`; this was not a clean transitive
source rebuild.

| Leaf | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8AlphaChallengeInputBridge.lean` | 0 | 17.91 s | 5,798,477,824 B | 0 | `propext`, `Classical.choice`, `Quot.sound` (subsets per declaration) |
| `FSV8V7ProgrammedAlignment.lean` | 0 | 7.80 s | 5,620,498,432 B | 0 | standard three only |
| `FSV8ProgrammedProjectionAlignment.lean` | 0 | 6.78 s | 5,641,109,504 B | 0 | standard three only |
| `ExtractionCollectorVerifiedSuccessfulReplay.lean` | 0 | 13.21 s | 5,825,904,640 B | 0 | standard three only |

No retained source contains `sorry` or a new `axiom`.  Source and artifact
hashes are recorded in the machine report under
`results/v8-completion-fs-extraction-20260911/programmed-replay-source-bridge-v1/`.

## Security implication

The machine-versus-functional gap caused specifically by programmed extraction
entries is closed for one checked replay, subject to explicit tape projection
and resource facts.  No probability term is reduced by this deterministic
bridge.  The next causal obligation is to construct, rather than assume, the
shared pre-alpha pause and prefix consistency for the four alpha continuations
of each gamma row.  Global security bits remain unset and grinding contributes
zero bits.
