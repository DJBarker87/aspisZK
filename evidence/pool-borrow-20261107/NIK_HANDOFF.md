# NIK Pool borrow discipline handoff — PARTIAL

Branch codex/cx-pool-borrow-20261107. No push, merge, shipped-file change, key operation or ELF rebuild. Frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. The deployed invariant and 100-bit per-attempt target are not yet established. No Pool-consumer row is closed.

## Established / measured

NIK_CENSUS.json and NIK_GRAPH.json retain frozen-source AST and the Pool crate's own optimized rustc 1.94.1 MIR: 668 source functions, 871 emitted headers, 372 source functions matched to MIR, 2,353 call sites, 353 borrow/accessor/CPI/drop events; every such event's source owner/name is corroborated (zero unresolved event owners). This is a generic compiler census, not proof of deployed monomorphized root reachability. Trait/indirect/name-only graph candidates remain explicit.

NIK_DISCIPLINE.md reviews all 13 exclusive-guard functions and lists every emitted source function. Three CPI sites hold exclusive guards, and apply_authorized_append_after_checked_state_v1 holds guards across before_persist (which reaches withdrawal CPI). Initialization retains guards in a Vec across loop iterations. These require exact child footprint/alias packets; a blanket no-live-guard-at-every-child assertion is not an adequate invariant. Pool uniqueness call lists are recorded without attributing the verifier's distinctness bridge to different Pool bodies.

The inventory is broader than NIE's seven data_is_empty sites: five data_len and nine lamports sites are also listed, for 21 infallible source accessor sites. NIK_OPEN_SITES.md records actual entry/alias/child/CPI and saturation obligations. No production inputs, transaction shapes or reachable panic are constructed.

Twelve current model theorems give physical-cell footprint composition, alias transfer, counter headroom and conditional closed-scope induction. Existing NIE exclusive cleanup is imported rather than reproved. NIK_Invariant.scope_model_invariant assumes a ScopeRun of the library scope calculus; it is NOT an instantiated program-wide Pool theorem and does not discharge native implementation premises.

## Validation / limits

NIK_L012 co-imports NGK_COMBINED_IMPORT, NIE_COMBINED_IMPORT, every current NIK model and AspisR1.RPx_Deployed.deployed. All 13 raw roots pass ax2 with standard axioms only. Eight inherited audit fidelity fixtures match. The NFX-method owner/import scan exits 0 on 13,487 modules, 690,356 declarations, 24,459,057 references: no dangling reference, incompatible owner or import mismatch. Exact receipts, source/dependency hashes, wall/RSS/swap/revision/axioms are in NIK_ATTEMPTS.jsonl and NIK_AUDIT.json. These audits establish coherence of this partial work, not native closure.

The single actual-body extraction reaches Charon output, then Aeneas exits 2 at opaque AccountInfo variant lookup. NIK_FAILING_STEP.md preserves it and the repaired Lean elaboration failures. Native per-function certificates and matched controls were NOT implemented; 0 Kani runs are claimed. No copy/field/function-pointer/native-contract credit, new trust row or security premise removal is claimed. RuntimeCpiReadonlyEntry7 is unused. All approved existing runtime/SDK/P6 trust remains. Frozen3, L154 as a statement parameter, narrowed D188, privacy and the two-transaction design are unchanged.

Budget: 0/100 Kani; 22/60 L slots; 1/1 extraction; 1/1 MIR. This is an incomplete whole-budget campaign, expressly disclosed in NIK_REMAINING.md with each native member and its missing packet. No assertion is made that all remaining native attempts are impossible. Next: original close_program_account_v1 typed local-record scope certificate, then the remaining independent functions, root admission and actual child/CPI footprints.

## Restore / retained artifacts

Host /home/dombarker/project-offloads/codex-cx-pool-borrow-20261107. Retained cache /home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NIK_exports_20261107 and NIK_audit_native_20261107; prepend exports to the exact NIK_CLOSURE_PINS LEAN_PATH. Seed reused 121 hashed NIE/NHP/NGK export records, copied zero object bytes and 3,328,187 staging input bytes. NIK_EXPORT.json pins retained outputs; NIK_CLOSURE_PINS.json.xz pins the actual resolved module closure, including Aeneas. Own Rust/extraction target scratch was removed after verified export; the cache is retained. Locked SDK/CPI source bytes match frozen-checksummed crate archives. Source-to-ELF pins are inherited only: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4, devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299, Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
