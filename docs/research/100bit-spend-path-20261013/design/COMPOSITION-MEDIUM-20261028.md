# Composition medium for the native bridges (lead design note, 2026-10-28)

Status: lead method ruling (w), within the owner-approved direct native-bridge route (contract amendment, third). It changes no target, metric or game. The owner may object or narrow it.

**CORRECTION (lead, 2026-10-28, after NCQ_):** the original sentence "It adds no trust item" is SUPERSEDED as unsupported. NCQ_ (evidence/native-topspec-20261028/NCQ_TOPSPEC.md) shows that linking Kani-proved Rust contracts to the headline's native1/native2 needs an explicit cross-tool semantic transport (Kani/CBMC and Charon/Aeneas agree on Rust semantics for the enumerated bodies, plus the recorded association of those Rust entries with native1/native2/op43/hashv). That link is not checkable in Lean. The owner decided (2026-10-28, amendment fifth): it is an explicit clarification of existing P6/D188 tool trust, scoped to the receipts; uses are reported as reclassification. The correction concerns reporting, not the protocol or the proofs.

## The obstruction every lane hit

The headline AspisR1.RPx_Deployed.deployed takes each deployed transaction as ONE opaque native function (`native1`, `native2`). Its premise `extraction : AeneasExtraction (sdk (config missing ...)) native1 native2 hashv` says that this opaque function matches the SDK/cohort model. Lean cannot see inside `native1`. So per-function native facts, proved in Kani about the Rust functions, can never be joined into a Lean theorem about `native1`: Lean has no object for "the Rust function that native1 calls". The two top-down jobs (NCL_ for TX1, NCK_ for TX2) and the skeleton jobs (NCE_, NCM_) ran into exactly this. NCL_ correctly refused to write "lower-unit hypotheses" as Lean propositions, because there is no Lean term for the native callee they would quantify over.

## Where composition can happen

The call structure of the real program is visible to Kani, which compiles the actual Rust. Kani's function contracts compose soundly inside Kani: `proof_for_contract(f)` proves that the actual body of f meets its contract, and `stub_verified(f)` lets every caller be verified with f replaced by that verified contract. Ruling (t) admitted contracts after three fidelity controls, with per-shape controls and matched failing controls on every use.

The composition medium is therefore Kani contracts, bottom-up along the real call graph:
1. For each reached function f, a contract C_f relates its inputs to its result and effects, with a `modifies` clause for its frame. The postcondition is stated by a Rust reference function `f_ref`: a direct transliteration of the cohort model's f, written as plain safe Rust (the P6 "owned safe reference" of the 2026-10-26 Vec/Box ruling).
2. Kani proves C_f for the actual frozen body of f, with every callee replaced by its own verified contract (stub_verified), and a matched failing control at each level.
3. Lean proves, once per function, that the Aeneas extraction of `f_ref` equals the cohort model's f on the caller-established domain. This is the only Lean obligation per function; it is a model-to-model proof.
4. At the top, Kani proves the contract of the actual entry function (stage1, stage2), so `native1` and `native2` meet a contract whose reference is the cohort SDK model. That is the component of the `extraction` premise the bridges discharge, with the composition done by Kani rather than by a hand-written argument.

What stays outside this medium: field multiplication (Lean-discharged stubs, opaque-call-log form); copies (KMX_ stubs); digest values (the runtime SHA trust row); the allocator (the existing Allocator item); safe Vec/Box internals (Aeneas std model under the 2026-10-26 ruling); and the toolchain itself (Kani trust as narrowed by amendment four; the K-1 and K-2 findings stand).

## Consequences for current work

- Existing local Kani results with failing controls are reused as the base level of contracts wherever their asserted property is the function's full result/effect relation; otherwise they are evidence toward a contract.
- Lean "skeletons" over the cohort models (NCE_, NCL_, NCK_) remain useful as the model-side composition. Their lower-unit "hypotheses" are replaced by the per-function reference equalities of step 3.
- The bridge question per function becomes a precise deliverable: (C_f proved with callee contracts and controls) + (extract(f_ref) = cohort f in Lean).

## Pilot

NCO_ pilots this end to end on one small vertical slice: a function with at least two levels of callees whose leaves are already CLOSED. If the pilot holds (contracts compose, controls fail as required, the Lean reference equality goes through), every lane switches to this medium.
