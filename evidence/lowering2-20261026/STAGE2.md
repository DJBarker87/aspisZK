# Reproducible release rebuild

Actual private build source revision: 8953c28138c7e3bc31a9109e84ab3a9864090057
(evidence-only stage-0 commit; shipped bytes equal starting 9e23364d3563).
All 1,243 tracked uploaded files were rehashed on the host after compilation.
Pinned cargo-build-sbf 3.1.13 / platform-tools v1.52 / rustc 1.89.0-dev,
existing release features and deployment-ID environment, locked offline builds,
-j4 and explicit 6G/8G/Swap0/Tasks64 caps. All selected local crates were
recompiled, using a private copied warm cache and unchanged diagnostic wrapper.
No crates/, programs/, candidate or shared build workspace was edited.

| Target | Exit | Wall s | Peak RSS KiB | Cgroup peak bytes | Swaps | SHA-256 |
|---|---:|---:|---:|---:|---:|---|
| default | 0 | 26.907 | 685776 | 1329094656 | 0 | f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 |
| devnet | 0 | 26.046 | 685980 | 1193914368 | 0 | 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 |
| Pool | 0 | 26.627 | 681900 | 1150156800 | 0 | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 |

Initial default-v1 failed before compilation (exit1,0.131s,35904KiB,swap0):
private snapshot omitted optional z4/Cargo.toml. Default-v2 adds the actual
tracked optional dependency manifests/sources; no cap or source modification.
Budget now SBF4/6, Kani0/0, Lean0/10. No timeout or memory kill occurred.

Low2_build_manifest.json records tool hashes/versions, full compiler arguments,
source hashes, compiler dependency files, generated-input hashes, features,
program IDs, artifact sizes/hashes and exact capped receipts. The old capped.py
embeds its historical source_revision field: original receipts are preserved,
and actual_build_source_revision explicitly records the real private source.
Default/devnet share the identically featured private target's final dependency
file; both compiler invocation snapshots and distinct program-ID environments
are retained, and repository bytes were unchanged throughout.

The compiler depfiles identify157 distinct repository Rust inputs (132 default/
devnet and133 Pool); all157 have source pins in the census. Other inventoried
Rust files include tests/examples and feature-disabled modules and are not
represented as compiled. Cargo manifests/lock are build inputs, not Rust units.
No Lean theorem was added; #print axioms N/A; exact S4 audit is reused.

Source census refinement adds src/Cargo.lock associations: now2,794 exact
references plus14 bridged, same479 unique file/hash pins, no mismatch.
