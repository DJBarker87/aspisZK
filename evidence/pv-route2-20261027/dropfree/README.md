# LOG D280 Drop-free measurements (in progress)

Fresh resume budget: 60 Lean emission type checks, 0 Kani. Assigned IDs 53300–53599. Earlier route-two artifacts and tally are historical.

`probes/*.rs` are evidence-only candidates. No patch is applied to a shipped crate or program or to the extractor. `native/` contains finite differential checks and exact retained comparator source, not proofs. Digest probes explicitly narrow generic library quantifiers to concrete SHA-256. Op36 narrows arbitrary destructible T / Vec ownership to Copy T / a caller-owned fixed-capacity carrier, retaining the entire error carrier. It does not discharge the generic Vec row.

Raw extracted Lean is retained under `generated-*`. `lean/` contains namespace-import routing, axiom-audit commands, and the documented pinned-backend shift-literal compatibility port only. Acceptance requires a nonempty root, successful type check, no opaque external function placeholder, and only standard axioms. Source equivalence, native effects, callback laws and adoption are separate gates.

The early host `revision` records the frozen source base (922ca3d252), with exact probe hashes for then-uncommitted evidence-only inputs. After preparation commit03af1fff3f, it records that immutable probe revision for subsequent runs; the dependency source snapshot remains frozen at the earlier base. Each Charon package `lib.rs` is the corresponding source snapshot when its run started. Intermediate rejected sources remain separate. The drafting scripts preserve experiments; final probe and per-run hashes are authoritative until the final manifest is frozen.

For op36 the full generic owned-Vec conversion is also measured freshly, preserving `Err(Vec<T>)` and non-Copy/destructible elements. The Copy/fixed-capacity successor is an explicitly narrower feasibility measurement, not a substitute discharge of that row. There is no claim that borrowing/copying the input proves the generic ownership conversion.
