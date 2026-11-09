# PCQE_ HANDOFF: phase P1d (retry of P1c-failed selections with the rebuilt ORIGINAL Aeneas)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; no equality proof written (P2/P3). Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 (tree d461fbc5..., Cargo.lock 5782e6a3...). Host workspace /home/dombarker/project-offloads/codex-pc-prov-p1d-20261109/.

## Tools (PCQE_TOOLS.json)
Aeneas: rebuilt original b59d5188, sha256 959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3, from the P4c host workspace by path (read-only); the hash is asserted before every use (PCQE_extract.py) and recorded in every PCQE_Exxx_PINS.json. Charon: original XRa_bin/charon daad69be (driver efdbe5b8), the same binary P1c used. Overflow checks ON exactly as P1c. **Every PCQE_ emission comes from the original Aeneas, a different tool from the b59d5188-extended behind the PCQ_/PCQC_ emissions; P2/P6 must use the gate-compatible library for them.**

## Results (11 extraction scopes of 20, 0 Lean; one at a time; caps 3G/4G swap 0, 180 s unraised)
| run | selection | exit | wall | peak RSS |
|---|---|---|---|---|
| E001 | S004 r0::transport::order | 0 | 30.1 s | 0.70 GiB |
| E002 | encode_digest_canonical solo | 0 | 79.2 s | 0.64 GiB |
| E003 | S016 Dot::push (+loop, loop.body) | 0 | 98.5 s | 0.53 GiB |
| E004 | S022 Weights::raw (+closure, closure_1) | 0 | 95.8 s | 0.52 GiB |
| E005 | S019 r1_wire via claims | 2 | 94.5 s | 0.52 GiB |
| E006 | S010 (7 roots) | 124 | 180 s | 0.65 GiB |
| E007 | compact::expand_values (copy_from_slice, fill opaque) | 0 | 101.9 s | 0.52 GiB |
| E008 | S012 split A (3 non-boxed roots) | 0 | 100.7 s | 2.04 GiB |
| E009 | S012 split B (3 boxed roots) | 124 | 180 s | 0.63 GiB |
| E010 | S010 split A (common, statement_public_common, transition_kind) | 0 | 81.3 s | 0.64 GiB |
| E011 | S010 split B (4 boxed decoders) | 124 | 180 s | 0.64 GiB |

Newly obtained emissions (PCQE_COVERAGE.json, name-level only): S004 order; encode_digest_canonical_loop(+body); Dot::push_loop(+body); Weights::raw.closure/closure_1; S1 expand_values (first fresh emission, the input to ExpandValuesFrozenEq); S010 common/statement_public_common/transition_kind/CommonV1; S012 digest_is_canonical(+loop,+body), decode_pool_v1_pair_live_snapshot_v1, encode_pool_v1_pair_late_public_statement_v1, the two snapshot/statement types (the two opaque validators/encoders appear as axiom-only). Summary: 20 FRESH_PRESENT, 2 FRESH_EXTERNAL_AXIOM_ONLY, 16 MISSING of the 38 tabled P1c-MISSING names. p2_emission_dirs_per_gate_module lists the emission dirs.

## Still failing (PCQE_FAILURES.json)
S019: Internal error r1_semantic.rs 47:8-55:1, InterpMatchCtxs.ml 230 (P1c site differed); not retried. S010 and S012 boxed-decoder roots: 180 s timeouts three times (E006, E009, E011), cgroup peak 3.28 GB at the MemoryHigh throttle, so Aeneas grows past 3G on the boxed decoders; boxed root class retired, needs an opaque callee or source-level restructure, which this job does not decide. Also MISSING: MASTER_OFFSET, PoolV1PairForestTerminalRequestV1, asq8_reference_envelope, POOL_V1_PAIR_CAPACITY (constants/types not emitted by these roots).

## Not established
No emission is claimed equal to a gate definition; the ON/OFF and equality work is P2/P3. Name-level presence is not equality. PCQE_HAND_MODELS.json is a record only (no trust row proposed). Files: PCQE_COVERAGE/FAILURES/ATTEMPTS/CLASSIFICATIONS/TOOLS/HAND_MODELS, per-run PCQE_Exxx/receipt.json and PCQE_Exxx_emitted/ (PINS, raw, xz logs), scripts PCQE_make_spec.py, PCQE_build.py, PCQE_chain.sh, PCQE_specs.sh.
