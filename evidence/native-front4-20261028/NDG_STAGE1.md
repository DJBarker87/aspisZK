# Stage 1: extraction and first controls

E001 PASS: five safe references extracted using NCO binary pins, Rust nightly2026-09-17 and optimized compilation. L001/L002 compile the unedited generated Types/Funs; L003 proves NDG_MetadataBridge.buffer/metadata/owner/key against AdapterRwModel. Every top theorem prints standard axioms only (buffer: none). These are exact model/reference equations, not a whole SDK extraction instance.

K001 PASS / K002 assertion FAIL: 32-byte pointer-copy control with exactly KMX_copy_stubs.patch (bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67). Deployed program features recorded; frozen graph441 packages/1491edges and Cargo.lock unchanged. No function pointer, SHA implementation or field multiplication reached. Native getters/metadata/ID contract and inverted-ensures controls follow serially.

Getter domain audit: current harness constructors use bytes=Err(InvalidAccountData), length=Ok(arbitrary usize). This is a restricted native class; real successful snapshots do not establish it. Accordingly even passing getter contracts are not whole-caller closure and the domain mismatch is a finding. The Lean getter equations are general on all cohort OwnedAccount values. Broader successful-byte native association remains required.

Resource records are in NDG_ATTEMPTS.jsonl and per-attempt receipts: exact argv/source hashes/revision, dependencies, exit/wall/peakRSS/swap/caps/axioms. No cap increased. One scoped command at a time. Setup imported a copied private cache and pinned all Aeneas objects; NDG_COHERENT_OBJECT_PINS additionally records the coherent18968-object snapshot without changing it.
