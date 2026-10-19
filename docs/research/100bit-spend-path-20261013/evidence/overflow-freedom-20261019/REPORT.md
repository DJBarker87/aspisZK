# Stage-1 overflow review: incomplete, blocked before Lean execution

Branch: `codex/r1-overflow-free-20261019`. Task base: `f9016d0a2`.
Handover snapshot: `93f5025d9`. No push or merge performed.

The previous worker left an inventory skeleton and helper scripts, but no Lean
proofs or receipts. This packet expands the inventory, reruns the lexical scan,
checks exact integer envelopes, and records why no new Lean theorem can yet be
counted. It does **not** close R22 or complete the requested stage-1 proof.

## Reviewed cones and evidence

The inventory is `../../design/OVERFLOW-FREEDOM-INVENTORY-20261019.md`. It lists
field leaves, semantic polynomial loops, round/prepare orchestration, strict
field/indexed decoders, batched rho updates, and source-level optimized
weights/fast_pairing/fast_dots. It separates failure-capable scalar operations,
indexing, total casts, explicit checked/wrapping operations, and caller premises.
The census is a conservative lexical aid, not a complete transitive-call-graph
or typed proof certificate. Library internals and the caller links listed as
open still need formal coverage.

`operation-census.json` pins six extraction/model inputs. `census-check.json`
records that all their monadic bind lines were retained and all source hashes
matched. Historical prepared and optimized current bodies are distinguished;
S1/S3/S4/S5/S7/S9 remain extraction/re-pin frontiers.

`bounds-preflight.json` records 24 passing exact-integer envelope checks,
including raw-pairing pre-subtraction sums, retained rho residues plus four
products, seven fast-dot batches, and 4096 private-dot folds. This is Python
integer arithmetic, **not** Rust execution or a machine-checked totality proof.

`theorem-index.json` records exact names and file:line locations for inspected
existing results. Their old receipts were read, but these results were **not
freshly recompiled** in this packet. Total-execution statements are separated
from success-inversion statements, whose direction is insufficient for R22.

## New draft, not an accepted theorem

`../../lean/R22FastPairingRawRanges.lean:11`:
`AspisR1.R22FastPairingRawRanges.partial_le_three_p`.

`../../lean/R22FastPairingRawRanges.lean:23`:
`AspisR1.R22FastPairingRawRanges.raw_ranges`.

The draft bounds both partial folds and each ordered arithmetic intermediate
of the private Q::raw/mul formulas under the canonical product cap. It is a
source-shaped Nat lemma, not an extraction of Q. It has not been compiled,
so no type-correctness, kernel-proof or axiom claim is made for it.

## Exact blocker and status

The binding `local-lean.txt` rule requires free+inactive >=10 GiB before every
compile, with the shared flock, own object directory, and -M4400. The recorded
preflight measured 4,093,919,232 bytes (3.81 GiB) and refused to start Lean.
The receipt records `status=not_started_memory_gate`, `exit=null`, and null
compile wall/RSS; there are no #print axioms results. This is not an OOM or
failed proof, and no cap was raised. A request for available memory or an
explicit gate override was sent to the user; no override is assumed.

The launcher now creates its own object directory, checks memory while holding
the lock, and records source revision/hash, direct-import object fingerprints,
command, ordered LEAN_PATH, compiler hash, swap readings and immutable attempt
receipts. No existing Lean module was edited.

## Findings and remaining work

No overflow on an admitted input was established. This is **not** evidence
that none exists. No wrapping_*/checked_* source policy was changed. Arbitrary
unrestricted helpers can overflow; the inventory names the range premises
that prevent that and the strict parser theorem supplying canonical limbs:
`AspisR1.ActualDecodeKStrictQM31Parser.source_refines`.

Still required: compile/audit the draft and focused consumers of reused results;
prove total strict indexed decoding; propagate actual parser/sampler ranges;
compose ten semantic rounds and prepare children; extract/re-pin optimized
weights/private pairing/fast dots; prove their actual bodies and source-loop
correspondence; compose rho phase/cadence/index invariants with stage 1; and
prove the deployed-to-checked acceptance direction. Stage 2 is deferred until
its extraction. The replacement parser and Merkle path code are excluded.

No full manifest replay, SBF build, Rust build, or release claim was attempted.
