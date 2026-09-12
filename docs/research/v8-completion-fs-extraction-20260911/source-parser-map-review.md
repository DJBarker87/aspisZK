# Fixed-field source inventory and first chronological gaps

Scope: current checkout `fc1fda1ac416a901fe4b8e88d8dda296fc54e2aa`.
The machine map pins individual source hashes independently of this revision.
No production, verifier acceptance, wire, or checked Lean source was changed.

## What was executed

`SameBodySourceMap.py` extracted **the verbatim `relation_callback.rs::parse`
function**, retained its source hash, and compiled it with the actual checkout
`crates/aspis-core/src/field.rs`. Only the surrounding constants, `Wire`/error
types, and synthetic test driver are harness declarations. This is not a
second Python transcription of the parser.

Command, from the repository root:

```sh
python3 docs/research/v8-completion-fs-extraction-20260911/SameBodySourceMap.py --out results/v8-completion-fs-extraction-20260911/source-parser-20260912-v1
```

The output directory must not already exist; reruns use a new suffix.
The existing bounded local subprocess runner was reused without modification.
`rustc 1.93.0 (254b59607 2026-01-19)`, optimized `-O`, both exits zero.
Compiler wall time 1.071 s, sampled aggregate peak 137,728 KiB;
test wall time 0.361 s, timed child peak 1,851,392 bytes; both swaps zero.
This is parser testing, not proving time or CU.

Results:

- All 297 admitted body lengths, from 24,890 to 40,282 bytes, give 697 fields
  and the correct equal frontier halves.
- Mutating each of the 697 canonical fixed fields changes its actual parsed
  value while retaining both roots and query bytes.
- Setting each of the 2,788 fixed-field limbs to the modulus rejects.
- Six malformed lengths reject.
- A deliberately malformed packed-record prefix is retained by `parse`:
  packed canonicality is deferred, exactly as documented by `SelectedWireBytes`.
  This is neither complete verifier acceptance nor a payment forgery.

Full commands, source hashes and logs are in
`results/v8-completion-fs-extraction-20260911/source-parser-20260912-v1/`.
The tests do not execute Lean or prove Rust refinement.

## All 697 producers

`field-source-map.json` has one entry per fixed field, with its exact 16-byte
offset, four-limb rule, Rust reader, causal boundary, polynomial coefficient
index or row/lane, and corresponding functional Lean producer.

The partition is `1 + 10*27 + 3*29 + 1 + 2*29 + 4*6 + 256 = 697`.
Semantic coefficient 1 and relation coefficient 4 are reconstructed, not
transmitted. Only lanes 0 through 27 of each ordinary row feed the 84-value
semantic projection; lane 28 remains in the 29-lane ordinary/OOD batching.
Final256 is fixed before queries despite appearing after later responses in
the serialization. The map does not confuse byte order with challenge order.
Roots, nonces, packed records and frontier halves are separately inventoried.

## Exact first chronological mismatches

1. `SameBodyOpenedRun.run` computes inverses before calling the Merkle verifier.
   `relation_callback::opened_values_prepared` first decodes/composes packed
   values, then authenticates, then computes the line inverses. The existing
   theorem honestly gives the conjunction of successful pure checks. It is
   not an effect-order refinement: malformed geometry can change which hash
   calls occur before rejection.
2. `FSV7SelectedBodyScript.selectedScript` is specifically the parsed Merkle
   suffix. It does not execute packed-field canonicality or geometry guards.
   Therefore it cannot be substituted wholesale for the Rust opened-value
   function, although it can be called after those source guards have been
   established in the correct chronology.
3. Its leaf calls follow sorted descriptor order. This matches the selected
   `v8_auth_order` branch (`auth_order::entries`), not the unflagged Rust
   branch, which hashes in original query ordinal and sorts afterward.
   A pure hash-function equality proves neither call-sequence equality nor
   equality for an arbitrary stateful diagnostic backend. The source already
   preserves a regression demonstrating that distinction.
4. The terminal leaf executes the complete folded covector dot, whereas the
   selected structured Rust path separately evaluates ordinary, query and
   sparse-image contributions. `TypedRelationTerminal.post_terminal` is
   algebraic evidence for that split, not a translated `Description::terminal`
   implementation. That source/functional producer is still needed.

No probability is assigned to these missing correspondences. They are not
hash-failure alternatives. The map does not infer the selected binary's cfg
set merely from source presence; its build manifest must pin that set.

## Smallest next literal-source leaf

The bounded first target is the selected fixed-field decoder loop:

> Under the actual parser length guard, its `chunks_exact(16)` traversal
> returns exactly 697 QM31 values; at each ordinal the value is precisely the
> four canonical little-endian limbs at bytes `16*i..16*i+16`, or the call
> rejects on the first noncanonical limb.

This target has no adversary strategy, image, semantic, terminal, or
`EncodedCausalFields` assumption. The functional theorem
`SelectedWireBytes.fixed_fields` already supplies its Lean side. The new
actual-source tests cover the Rust side. A literal Rust execution semantics /
extracted body for the `chunks_exact`/`collect` loop and the small field decoder
has **not** been built in this task, so universal Rust-to-Lean refinement is
not asserted. It should be done before attempting a whole-verifier translation.

Even that proof would only establish parsed field identity. It would not
construct a uniform causal strategy from a Fiat–Shamir execution; the
per-history producer for `EncodedCausalFields` remains a separate obligation.

Status: field inventory and optimized actual-parser controls PASS;
the focused source-shaped Lean cursor and sequential-limb leaves PASS under
the pinned historical Lean 4.32.0 toolchain with only standard axioms;
fresh dependency rebuild/kernel checks NOT RUN; literal-source refinement NOT PROVED;
global soundness/Fiat–Shamir/checked extraction OUT OF SCOPE for this leaf.
