PILOT RESULT: **partly**. The requested complete vertical slice is not established.

Branch `codex/cx-native-cpilot2-20261028`; no push or merge. Outputs: NCP_PILOT.md (controls, obstacles and timings), NCP_SLICE_BRIDGE.md (exact claims), NCP_STUBS.md, NCP_ATTEMPTS.jsonl (204 distinct receipt rows), NCP_VALIDATION.json.

## Established

The actual frozen digest decoder satisfies a safe Rust reference contract on every32-byte input (K038/K039), and its verified caller works with a matched failing control (K040/K041). The complete Result/digest shape fidelity controls are K018–K023. X002 and `NCP_DecodeReference.reference_source` (L048) prove the extracted reference equals the selected cohort decoder, including all errors and every successful limb.

The canonicality scanner has actual-body and verified-caller contract pairs K042–K045; `NCP_CanonReference.source` (L056) connects its extracted reference to the SAME pair_tree_profile model. The existing NBD_DigestInduction source/termination proof is reused. Fixed-slice exact8/exact32 have revised actual/caller pairs K058–K065 and `NCP_ExactReference.source` (L054). Native domain: widths8/32 and slice length<=33 ONLY. Model range lemmas in NCP_CallerDomains prove all21 digest windows and the index window in688 bytes. No N=4 or unbounded native exact claim.

`NCP_ModelDischarge.u03/u05` instantiate the prior cohort equations with explicit model references and no lower-codec hypotheses. This is model-side discharge. No U03/U05 native CLOSED-CONDITIONAL row is relabelled unconditional: their complete caller contracts have not been established in the new medium. The DigestDecode condition now has a checked LOCAL leaf witness available for lead adoption.

## Obstructions and next deliverable

Vec verified substitution fails codegen: Result<Vec<u8>,u8> lacks Arbitrary (K010). The real-body control passes; a compiler error is not a successful weak-contract negative control. For/enumerate microcontrols crash the pinned compiler; actual encoder K070 also crashes, on borrowed invariant dereference. The borrowed afterstate-validator invariant initially crashes; a local ghost alias gets past codegen, then K066 times out90s (wall98.878168s, peak6,531,304KiB, swap0). No complete validator contract is proved. The own queue incorrectly submitted its negative K067 before classifying the timeout; it was explicitly stopped (CBMC status15), receives no credit, and no further same-member contract retry occurred.

K068/K069 instead check ONE frontier iteration at arbitrary prestate/level<20 with the verified canonicality callee. NBH_Frontier.afterstate_loop remains the model induction; this does not supply the missing Kani whole-function contract.

After native exhaustion, X004 extracts the encode reference, L058/L059 compile its definitions with standard axioms, and L060 attempts the generic ONE-ITERATION equality. Checked shifts/casts and four writes versus the little-endian setSlice remain unresolved. Its failed candidate is NCP_EncodeStep_UNACCEPTED.lean.txt, excluded from imports. Next Lean deliverable: prove that generic checked word/store step, then a decreasing-loop equality. Next native deliverable: repair/isolate the frozen iterator/invariant shapes with controls, then produce the missing full callee contracts before enclosing callers. Never rerun K066 unchanged or increase the cap/timeout.


## Remaining members: why native work remains

| Member | Required Kani work | Remaining Lean/reference work |
|---|---|---|
| U02 DigestEncode raw/canonical | actual encoder contract blocked by K070 invariant compiler ICE; word-only diagnostics do not suffice | X004 extracted; L060 word/store step and full loop equality remain open |
| U03 afterstate decoder | full validator contract plus parent contract under verified digest/exact callees | extract/equate its complete safe reference; existing NBN conditional model law retained |
| U03 afterstate encoder | validator and digest contracts, then its20-row encoder loop/caller contract | complete reference extraction/equality and frame composition |
| U03 live encoder | digest/validator contracts and native20-row mutable-slice caller/frame | same reference and error/output-state equality |
| U03 late encoder | live/afterstate callee contracts, fill/order/error/frame caller contract | complete1520-byte reference equality |
| U05 ASF8 validator | late/digest and TransferEncode/WithdrawalEncode contracts, then validator contract | complete safe-reference extraction/equality; model equation alone is already checked |
| U05 ASF8 encoder | validator/late/payment/digest contracts and complete1880-byte caller contract | complete safe-reference extraction/equality |

Transfer/withdrawal encoders still depend on the open raw digest encoder contract. The Vec interface remains unadmitted. These are implementation proof gaps, not new cryptographic assumptions. Native exhaustion was followed by the remaining independent Lean work; now BOTH budgets are exhausted, so remaining Lean gaps are also stated rather than hidden behind native blockers.


## Validation, resources and trust

70/70 Kani runs;60/60 conservatively charged Lean slots (59 Lean invocations and the L036 preflight);4 extraction scopes. NCP_ATTEMPTS.jsonl has204 unique rows, including metadata validations. Every Kani run has a fresh complete frozen package/edge comparison, offline mode, and unchanged frozen Cargo.lock5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef. Rust compilation is optimized. Each prover/extractor runs alone for this job in a freshly admitted exit0/allowed:true scope:6G high/8G max/swap0/tasks64; Lean-M7000. No cap or timeout increase.

L057 is the focused final audit of all CLAIMED new theorem roots and helper reference definitions: exit0, wall2.024834166979417s, peak5,399,168KiB, swap0. Exact dirty source revision/hash and dependency fingerprints are in its receipt. Accepted roots use only propext/Classical.choice/Quot.sound (or fewer). L059 audits the additional emitted encode definitions; L060 fails and is excluded. Rejected Lean diagnostics containing sorryAx supply zero credit. No new axiom, admission, native_decide, or manual heartbeat/depth increase is present in accepted sources.

The coherent SInt2 workspace/objects were reused. The private cache was COPIED from the two read-only seed caches:586 imported files retain their original hashes;636 files remain. All219 Aeneas library objects actually selected by LEAN_PATH are pinned in NCP_RESOLVED_AENEAS_PIN.json. X001–X004 retain exact Charon/Aeneas source/executable pins, commands, generated output hashes and errors. The helper external TEMPLATE axiom was never imported; a checked alias to the existing generic cohort map_err definition is used instead.

Retained: approved runtime/allocator/TrustedStd/SDK trust, narrowed D188/extraction/compiler/ABI/source-to-ELF boundaries, frozen3, RuntimePersistence, the approved two-transaction game, L154 as statement parameter and the RPx_Deployed.deployed headline. No metric, protocol, game or trust item changed; no XRn join kit, SHA-value model or field-multiplication proof/stub is introduced. S2 and the deployed100-bit target remain NOT established.


## Freeze, reproduction and host state

All496 frozen crate/program files were byte-checked against4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Six scratch files contain insert-only cfg instrumentation; all frozen function bodies remain byte-identical. Repository crates/programs were never edited. Apply the EXACT mandated KMX patch, copy its root stub into the statement library, then the retained NCP_harness.patch for the final scratch configuration. Per-attempt source hashes, snapshots/journal and historical stage commits identify earlier configurations; do not attribute an earlier verdict to a different final-cache artifact. NCP_FINAL_GOTO_CACHE_PINS.json explicitly pins final cache state only.

No shipped-file change or ELF rebuild trigger. Inherited artifact pins, NOT rebuilt here:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Host scratch `/home/dombarker/project-offloads/codex-cx-native-cpilot2-20261028` retains sources, receipts and generated text. Own Rust targets (1,850,874,120 bytes) and empty solver temp directory were removed after preserving artifact pins. The private cache `/home/dombarker/project-offloads/codex-cx-cpilot2-cache-20261028` is RETAINED. No own prover remains. No wallet/key operation, session-A worktree/candidate edit, other worker-prefix edit, shared launcher repair, binary/object/ELF/archive commit, push or merge occurred.
