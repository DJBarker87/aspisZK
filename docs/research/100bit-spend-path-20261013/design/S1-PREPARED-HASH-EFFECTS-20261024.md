# S1 preparation: exact source-shaped hash effects, 2026-10-24

S1 and S6 remain OPEN. This packet supplies the complete preparation hash-call
representation needed for the outstanding ordered-oracle join. It does not
claim native SHA, SDK/account, frozen2 operation, or global soundness closure.
No shipped Rust or source adoption, release artifact, deployment, or CU changes.
S2 ownership remains transferred; this packet does not modify its track.

## Exact established claims

All files below are in `lean-candidates/s126-caller-boundary-20261021/`.

- `S1PreparedSourceEffectsV1`: the original complete Prepared::new body, with
  seven full typed child operations generalized to a monad. `source_exact`
  gives complete Result and returned scratch equality with
  `OriginalPreparedNative.prepare`, without a success premise.
- `S1PreparedHashEffectsV1`: original transcript new/absorb/block bodies,
  generalized only at the actual digest child calls. Their source
  interpretations equal the original functions on every outcome.
- `S1PreparedHashCodeV1`: typed digest calls retain the digest dictionary, hash
  carrier, grouped input slices and continuation. Result steps retain fail/div.
  The run log retains attempted digest calls, including the failing/diverging
  reply; `run_value` proves exact value erasure. These events are attempted
  source digest calls, not yet a proof of physical SDK/oracle queries.
- `S1PreparedHashErasureV1`, `S1PreparedScalarEffectsV1`,
  `S1PreparedScalarErasureV1`: full source evaluation of the lifted transcript
  and scalar/rho procedures, including their errors and returned state.
- `S1PreparedQueryEffectsV1`, `S1PreparedQueryErasureV1`: the COMPLETE original
  materialized query procedure, including all sixteen read/advance digest calls
  before scanner selection. Query rejection returns the original absorbed state;
  acceptance retains the actual selected state and all 22 embed/trace calls.
  Unused materialized suffix calls are not erased or reordered.
- `S1PreparedCompleteHashErasureV1.preparation_erasure`: composing these
  procedures yields exactly original preparation's complete Result and scratch,
  for both fold variants. Non-hash operation boundaries remain explicit.
- `S1ClosedPreparationHashCodeV1.closedPreparationCode_installed`: the complete
  representation, with the EXISTING concrete sampler/query/embedding/serializer/
  powers/claim installation, erases to the precise `(closedInstall ops).op8`
  already consumed by the owned stage1/first caller theorem. There is no free
  sampling/query record, separate child success, desired output, canonicality,
  or totality hypothesis in this equality. Full current carriers are retained.

Before: the existing caller theorem supplied preparation's result and joint
challenge trace under the concrete installed child operations, without an
explicit digest-call program for its full preparation execution.
After: the same installed operation has a source-shaped digest-call program
whose evaluation is proved equal on all outcomes. This supplies the object
that must be interpreted and compared in the actual ordered-oracle join.
It DOES NOT discharge that join by calling an arbitrary dictionary concrete.
No native cryptographic/source correspondence premise is removed by this step.

## Pins and validation

The authoritative research checkout was re-observed at
`b797d6d360b460b527c046e37dad1106e8beeabc`; this work starts from isolated
`a2c24e8ad34530df76d30f4bd61609594b07d17f`. Existing
`evidence/s126-current-caller-20261021/s1-native-word-control-source-pins.json`
retains the historical b272 extraction, adopted 258 source, and b797 source
inventories. verifier/candidate/transcript source equality must not be promoted
to equivalence of the differing numeric helper files. The current SDK authority
and its separate extraction/state obligations are unchanged.

`evidence/s126-current-caller-20261021/s1-prepared-effects-targets.json` selects
only exit-zero attempts. Every selected attempt retains the exact target,
command, source revision/hash/snapshot, tool/direct-import hashes, wall time,
peak RSS, zero process swaps, and full standard-only `#print axioms` reports.
`...-import-pins.json` pins the selected transitive warm object closure by
hash; no compiled objects are distributed. `...-tool-pins.json` and
`...-reused-pins.json` pin generators/checker/runner and prior accepted packets.
The four generator materialization records pin exact source spans and check
their deterministic transformations. Historical source headers containing
resource overrides are not copied into the new query target.

Only focused changed modules compiled, using the atomic local mkdir lock,
Lean 4.32, `-j1 -M4400`, and warm imports. No package replay or cold build.
The initially deep query reflexivity/simplification attempts failed at default
recursion limits; the accepted proof instead walks individual bind
continuations. No heartbeat/recursion overrides were added. Failed attempts
(including compiler error-recovery sorryAx reports) are diagnostics only.
The same projection-by-projection approach avoids expansion of the complete
concrete query record in the closed caller proof.

Accepted focused targets total 193.259086 seconds; maximum process RSS
3,881,615,360 bytes; zero process swaps; 25 standard-only axiom reports.
`git diff --cached --check` reports only the original copied trailing space on
Prepared::new's row29 scalar-call line, in the generated target and its exact
receipt snapshot. Those raw source-body bytes are preserved deliberately.

Audit: `python3 tools/s1-prepared-effects-20261024/check.py`.

## Exact remaining enclosing obligations

1. Interpret this complete call program with the actual native SHA flattened
   inputs and the accepted source/runtime port, preserving order, early exits,
   error behavior and returned state. The old SourceDigestOracle input grammar
   does not cover the 62-byte P3 opening initializer. The source initializer is
   the actual 29-byte domain, variant byte and 32-byte semantic state, in three
   grouped parts. Do not default or omit it. Keep all sixteen query digests,
   including the unused suffix, in the experiment transport.
2. Connect that interpreted execution to the matching fixed frozen2 prepare
   operation and caller. Generic BodyJoins on arbitrary dictionaries or Result
   erasure alone do not identify the fixed source/model operation instances.
3. Finish native arithmetic/Std/P6 interpretation, purity and abort transport
   for powers/field/Dot/new/push/finish and wide add/mul. Prior normal-return
   Kani control checks and borrowed-helper extraction are reused, not extended
   here into unrestricted native totality.
4. S6 still requires actual SDK/account execution and source/oracle bindings
   beyond the proved full decoded-public reuse, complete codec roundtrip and
   removed byte-public admission premise. Reuse S2's owning-session work.

This is an all-outcomes Result equality, not a claim that arbitrary preparation
inputs succeed. Invalid folded-root unwraps, allocation/runtime failures and
non-hash child totality remain at their established explicit boundaries. No
additional R22 TOTAL claim is made by this packet. The <=2^-100 per-attempt
target without grinding credit remains unchanged and not yet established.
