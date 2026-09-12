# Same-body response-compatible replay matrix

Status: focused deterministic bridge; chronological fork production and global
soundness remain open.

## New checked endpoint

`lean/ExtractionCollectorCausalMatrix.lean` replaces the final-only matrix's
arbitrary replay records with cells containing actual successful
`wholeStagedScript` executions.  For every selected cell it now derives:

- the valid, length-22 query schedule from that cell's successful suffix;
- the canonical 697-field word from that same submitted body;
- its response0, final256 and later responses from that word; and
- successful `SameBodyRelation.consume` plus equality with the serialization
  of one response-compatible row strategy.

The four alpha cells may vary only after alpha in the constructed strategy.
Their common response0 is a premise of `AlphaPrefixCompatible`; final256 and
later responses are selected after alpha from the corresponding successful
cell.  No `consume = some _`, final equality, later-response equality,
serialized-word equality, quotient, recovered tuple, terminal acceptance or
payment witness is assumed by `row_consume_succeeds` or
`row_serialized_word`.

## Hostile-review boundary

This endpoint does **not** prove that the four successful cells are forks of
one chronological source history.  Each `SuccessfulReplay` currently carries
its own tape and oracle.  Equality of kappa, tau and parsed response0 values is
not equality of the pre-alpha execution state.  Accordingly the retained
source calls this a response-compatible strategy, not an actual replay-causal
strategy.

The next producer obligation is precise: construct the 29-by-4 matrix from the
state-restoration experiment so that every row's cells share the same actual
pre-alpha source/oracle prefix, and derive `AlphaPrefixCompatible` from that
construction.  This must preserve replay failures, resource failures and
missing cells rather than assuming `CompleteMatrix`.

Even after that producer exists, verifier acceptance must still imply the
per-cell terminal/fold facts needed by four-alpha and 29-gamma reconstruction.
Permitted-access payment extraction and the adaptive Fiat--Shamir probability
lift remain separate open gates.

## Focused evidence

Both changed leaves were checked with Lean 4.32.0 using the pinned union cache
and `-j1 -M7500`.  This was a focused cached check, not a clean first-party
dependency rebuild.

| Target | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `ExtractionCollectorFinalMatrix.lean` | 0 | 4.45 s | 5,840,961,536 bytes | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `ExtractionCollectorCausalMatrix.lean` | 0 | 11.19 s | 5,844,992,000 bytes | 0 | `propext`, `Classical.choice`, `Quot.sound` |

Source hashes:

- `ExtractionCollectorFinalMatrix.lean`:
  `e41f0d9522260beab4e6dfb3ac8bbd68596b389daf2ed07f61be81dc17f344b7`
- `ExtractionCollectorCausalMatrix.lean`:
  `6dee601b0bef3b92e97bad6272a6da0ea2cfd7ba24dc536678a64782c3301e01`

The logs and artifact hashes are in
`results/v8-completion-fs-extraction-20260911/response-compatible-matrix-v1/`.

## Security implication

This removes a same-word relation-consumption premise for a matrix whose cells
are individually successful source-shaped runs.  It does not reduce the
unbounded global accepted-but-unextracted term, because matrix availability,
shared-prefix replay legality, fold correctness and checked payment extraction
are not yet proved.  Global security bits therefore remain unset.
