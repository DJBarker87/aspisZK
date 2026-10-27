# pv-runjoin13 — ELF gate passed; new extraction obstruction awaits ruling

**Target not yet established. Stage 3 remains open.** Branch
`codex/pv-runjoin-20261026`, entry `dd58cab6376dbd844f32ae764d88c4ca3d780e37`.
The authorized closure-only edit is committed in `2910da23a3`; verbatim diff:
`shipped-records.diff`. Exactly one shipped file changed, only inside records:
two Option matches and two 20-element while/index array initializations.
File SHA-256: `b45b6f97c27c891022475a4b5cf7c13b2c3efcd333f3281cb26ce44bad31d629`.
No additional shipped edit, revert, repin, merge, push, shared env-J write or
wallet-key deletion occurred.

Gate (a) PASSED, source `2910da23a3b4a3f780611728d3af122457bbef85`:

| Target | SHA-256 | Exit | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| default | f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 | 0 | 66.707 | 683352 | 0 |
| devnet | 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 | 0 | 65.911 | 682456 | 0 |
| Pool | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | 0 | 61.961 | 678032 | 0 |

Exact commands/environment/resources are in build-*/receipt/receipt.json and
command.json. #print axioms is N/A: these are ELF builds. The missing historical
devnet template caused one precompile failure; the committed historical command
supplied the identical public IDs for its replacement. Three artifact keys remain
retained at mode 0600 (`key-retention.json`). Gates (b)/(c) were NOT run;
`GATE-PLAN.md` specifies the combined records/op223 lead-owned comparison.

Extraction used unchanged pinned Charon/Aeneas, preflight on. Eight Aeneas and
13 Charon/metadata-build receipts are indexed in `extraction-run-index.json`.
Direct raw-inclusive extraction fails on raw's unchanged FnOnce closure.
Isolating raw exposes **records:230 / InterpAbs.ml:1955** at the original
`let pair = &input.pair` branch. Default/strict joins and owned adapters fail
there. Monomorphization fails at the two Option language items. Optimized foreign
metadata retains the same obstruction when the root is actually retained.
Aeneas06's exit 0 is REJECTED: it omitted records; its external templates are
quarantined text, never imported. Forwarder thresholds leave both relevant LLBC
bodies byte-identical; no unchanged Aeneas rerun was made.

No R_shipped constant was accepted. Both shipped fixture identifications,
compiler-return/selected-i/transition equations, deployed public binding and
P ∧ T non-vacuity remain OPEN. Prior reference theorems and 21 root-cell proofs
are retained, not relabelled shipped facts. Constructed P remains {source public
binding, trace}; deployed P remains OPEN; record counts 2/8/6 → 2/8/6.
Endpoint premises removed/added/weakened: 0/0/0. T remains exactly entropy_law,
entropy_kernel, observation and hypothetical; observer/simulator unchanged.

Budget: Lean 0/100, Kani 0/2; no env-J IDs used. 50897–50899 remain reserved.
This is NOT budget exhaustion or a checked ROW counterexample. Focused kernel
trust audit is pending; no new Lean theorem/axiom is claimed.

Next deliverable requires the pending lead ruling on the unapplied, one-line
`pair-borrow-proposal.diff` (`let pair = input.pair`, whose type is Copy).
The prompt explicitly permits only closure replacements, so that additional
source line cannot be applied without authorization. If authorized, commit it
and rebuild all three ELFs immediately before resuming extraction/proof work.
