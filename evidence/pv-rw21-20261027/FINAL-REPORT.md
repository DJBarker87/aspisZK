Branch `codex/cx-prover-rw-20261023`; base `0242bd9221`. Formal audit revision
`626de88c53405e333348d574de4330bd2b229029` (see exact full revision in receipts).
Stopped on budget exhaustion: **100 Lean attempts (60 pass, 40 fail), 10 Kani
runs**, 14 uncharged reservation refusals. IDs 37700–37813 consumed; next 37814.

V164 historical hypotheses `{source_law, context_identity}` had already become
`{P_source_p6}` in rw19. **rw21 before/after: `{P_source_p6}` → `{P_source_p6}`**.
The concrete context identity remains discharged; native op223 association is
OPEN. Final cb3/cb searches found no `op223_source`. The auxiliary Source16
consumer checks endpoint/no-pole transport on the actual 16-limb call shape;
it does not remove the privacy consumer's source premise.

V163: **whole deployed model construction OPEN; transfer fixture OPEN;
withdrawal fixture OPEN; general byte equation OPEN**. Stable published name:
`R1Z.ProverRw21ModelInstance` (first published in `c35f9d8192`). It constructs
mathematical transcript serialization, never projects actual source output;
it is not yet the deployed-input protocol instance requested by join4.

Proved: mathematical semantic/compact/query/node serialization and the
57,607-byte successful output; audit observations and the explicit rw18 caller
criterion; canonical wide carrier/byte image; exact arbitrary-slice serializer
loop under the usize bound, consumed by the dictionary installed in
`ProverRwP6BodyStore`; exact finite mathematical wide sequence encoding.
All 57 retained new focused modules are checked. No endpoint, RunJoin, E1/E2,
client-route, or side-channel premise was removed, added, or weakened.

Measured Kani outcomes: arity-zero and arity-16/lambda-zero pass; six timeouts;
one MIR overflow assertion; one rejected overflow-off configuration. The latter
was not bypassed. The MIR assertion is not established as a shipped-release ROW
counterexample. See [native configurations](KANI-PLAN.json) and
[overflow analysis](OVERFLOW-CONFIGURATION.json).

The last three attempts were reserved and used for the combined audit:

| ID / target | Exit | Wall | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| 37811 ComponentInputs | 0 | 2.91 s | 4,307,576 | 0 |
| 37812 AxiomsAudit | 0 | 2.07 s | 4,301,464 | 0 |
| 37813 FrozenManifest | 0 | 1.89 s | 4,300,216 | 0 |

Exactly **477 declarations**, standard axioms only (`propext`,
`Classical.choice`, `Quot.sound`). Cached-component replay, **not a clean-source
rebuild**. [Frozen inputs](frozen-component-inputs.json),
[exact audit coverage](final-audit-results.json), and
[all 110 run receipts](receipts.tsv) retain target, exit, wall, peak RSS, swap,
revision, source/dependency hashes and full `#print axioms` results.
[Stage commits](stage-commits.txt) record `git log --oneline 0242bd9221..HEAD`
through the formal freeze; the final evidence commit follows it.

No shipped-code or soundness/ledger changes; no local Lean compiles or toolchain
rebuild. [Scheduling exceptions](SCHEDULING-EXCEPTION.md) record one accidental
scope overlap and one admission retry 22 seconds early; both were corrected.
[Cleanup](cleanup-host.json) confirms inactive own scopes, removed Cargo cache,
retained shared Lean imports, and no wallet keys created or removed. Shared
solver temporary files lacked exact ownership attribution and were retained.

Only proposed/uncompiled: material/caller continuation and the enclosing
sumcheck fixed-point transport, preserved in `drafts/`. The round transport
itself is checked. Next deliverable: prove the native op223-to-P6 complete
Result law, then construct the deployed mathematical protocol instance and
prove transfer, withdrawal, and general proof-byte equations through
`ProverRw21CallerCriterion.criterion` / `ProverRw18ContextDataIff.criterion`.
**The privacy target is not established.**
