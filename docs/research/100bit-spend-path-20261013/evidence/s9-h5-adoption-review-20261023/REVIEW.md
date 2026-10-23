# H5 review-only adoption delta

The owner explicitly approved +12,214 CU per verification/settlement phase against the previously selected comparator artifact. This changes the compute allowance only. The transparent protocol, two-transaction verification/settlement scope and100-bit security target are unchanged.

`h5-review.patch` applies the exact measured candidate: weights ab55509e54218a2bfe7dd2d5e1b14216e3303961c16c181ce2e03d40f6b7678b; fast pairing7f75b58bfcaf7f586acb0152671e42565a549a8ace2b90dab794533dcdb6335e; owned adapter246d96b479ef552b485a51a2a3d4c4dbe1ff4ef9c0527b6f9a872f296b60576b. The caller source09ce3b480cf772c843315b9bcdabd9bf266f4065e5a524ae2a4d5560ea4feaf3 stays unchanged. `git apply --check` passed; shared Rust was not edited by this worker. Root owns application, PR and source/artifact freeze.

The candidate preserves callback-free C arithmetic and uses the tail-slice zero scanner. The exact old/new scanner source equivalence is proved for all valid byte slices, including rejected inputs, empty input and every nonzero position, with the real SDK result/error type. See sibling lean-candidates/s4-zero-scanner-all-input-v1-20261023. C arithmetic/constructor semantics keep their existing source-cut/runtime trust boundaries; this review is not a complete100-bit release claim.

`source-pins.json` lists exact before/after whole-file hashes. `changed-declarations.json` records textual function-span changes:19weights declarations,11fast-pairing declarations and require_zero. It is a source inventory, not a replacement for the final whole-cone re-pin and coherent release replay. Full-file hashes also cover annotations and non-function text.

Alpha's isolated Core explicit7/6writes candidate is not included here. If adopted, it adds a fourth source delta and its own source-refinement/pin inventory. Runtime evidence transfers by exact ELF identity only; a different artifact requires the affected artifact gates to be assessed again.

## Gates and reuse

The exact H5 ELF is b5cb382b1738a016b2463d2388fd38523e55577bf8053b7b4f68aee482fa4d5b. Its existing six saved SBF fixture comparisons, one retained full OS-mask proof, and strict linked-ELF stack audit are reused. No unchanged six-fixture/full-mask replay was run during these adoption gates. The measured maxima remain +12,214 stage1 and +2,294 settlement on the six fixtures; the retained OS-mask sample gives +12,214 and +2,299. These are measurements, not analytical worst-case cost bounds.

New meaningful optimized native gates target the exact H5 sources: two existing weight/helper units (including512four-output Libra cases), four integration suites for pairing/dots/weights/shared contraction, and the existing actual SDK adapter differential suite with1,200distinct counter0mutations. The shared-contraction test is a harness-only retarget of the existing test to the ACTUAL H5 library; its old separate candidate test and retained baseline are preserved. Nonzero borrow-counter runs remain diagnostics.

The old readonly13mutation report is tied to another artifact/format and is not reused. The current-format adapter replay originally disabled metadata injection with a stub. The isolated harness restores the full existing7stage1/8stage2 cases, enables LiteSVM0.16's empty persistence-internal feature to expose its test insertion API, and changes only its compute-delta guard from12000to12214. Both original stub/driver and updated hashes are retained. Controls and negatives all disable signature verification consistently. This checks synthetic loader-to-AccountInfo metadata rejection and protected frames, not signed-state reachability or custody.

All jobs use optimized Rust, j1, exact locked/offline inputs, warm pinned host targets and independent cgroup caps with zero swap. Named phase receipts distinguish compilation from arithmetic/runtime. Failed snapshot/include/filter attempts are retained and are not accepted gate results. No SBF cache was used after Alpha received exclusive ownership; no keys or binaries are committed.
