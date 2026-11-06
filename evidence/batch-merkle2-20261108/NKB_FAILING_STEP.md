# NKB failing steps

Target not yet established.

Own input preparation initially looked for the shared frozen payload in the NJS input pool. It is retained once under evidence/extract-stage-20261106; NKB_prepare.py now reads that committed source, with its existing SHA pin. No prover was launched by that failed preparation.

NKB_K001 completed successfully. Own collection assumed UTF-8 for every source snapshot and failed on the compressed payload. NKB_run.py now transports arbitrary bytes as base64; NKB_recover.py recovered K001 read-only. No prover resubmission occurred. Validation is unchanged. K002 is the matched semantic failing control.

L002 left a diagnostic goal unsolved after broad simp. L003 named a nonexistent slice specification. These failed elaborations, including their sorryAx diagnostics, are excluded; no accepted theorem uses sorryAx. The source was corrected by unfolding the pinned slice model directly.

Potential emission mismatch: NJS_Extract.verifier.candidate.batch_tree_loop.body returns done(idx,val,none) at rejected node_count, capacity, padding and false verify branches. Its wrapper maps none to fail panic. Frozen Rust returns Err(Merkle) or Err(Parse) on those paths. The raw emission has the same issue; this is not caused by NJS's section-parameter adaptation. K001/K002 establish only the rejected-count terminal native control/frame on d<=16; d=0 is not claimed reachable after a positive complete batch. Reachable rejection and adopted-cohort interpretation still need analysis before attributing any whole-parent obstruction.

K004: matched control of the combined opening/leaf/dedup cut timed out at the unchanged 90-second solver bound; K003 gets no paired native credit. Replacement windows: K005/006 argument prefix, K007/008 dedup. K007/008 have interleaved whole-source additions and are supplemental only; final same-snapshot pairs K011/012 (arbitrary opening byte added) and K013/014 supersede them. Native target names are preserved when the asserted cut is unchanged.

K009: dynamic full-slot first-padding-word rejection timed out at 90 seconds (peak RSS 6,253,720 KiB, swap0). K010 was cancelled before launch. Replacement K015/016 is the exact eight-byte predicate only; symbolic NKB_PaddingFrame induction/frame handles the suffix. The timed-out shape is retired, with no cap or timeout increase.

L009's first preflight misread the phrase `import the` inside our docstring as a module import; the phrase was corrected before any compiler launch. L009's actual compile then exposed a bad indexed proof, wrong wellFormed constructor shape, and heartbeat exhaustion while elaborating the unsplit prefix lemma. The proof was rewritten over list.range and split into NKB_CallerDomain and NKB_CallerPrefix; no heartbeat limit was changed. L011 and L012 were own source layout/parser errors, corrected in source; failed artifacts are excluded.

K011 timed out at the unchanged 90-second solver bound; K012 was cancelled. Its payload-byte claim is excluded; the earlier prefix pair is only argument/provenance support. K017/K018 and K021/K022 are distinct one-iteration std fidelity checks, not a retry of the large shape. K019/K020 isolate only the entered Parse exit.

L017/L019 exposed an omitted lift simplification and dependent-if reduction; corrected L023/L024 pass. L025 exposed tokenization/tuple projection in the strict-leaf proof; corrected L026 passes. L029/L031/L032/L034/L036/L037 exposed callback-projection and local loop-body reduction issues in the total std law; changed proofs isolate each body equation before the loop unfolding, and L038 passes. L033 substituted away identifier names in a diagnostic proof; L035 uses explicit frame rewrites and passes. All failed-source snapshots and automatic sorryAx error diagnostics remain excluded from the successful proof inventory. No new sorry/axiom/admit/native_decide or heartbeat/depth override was introduced.

First combined import L045 stopped on missing NJI_COMBINED_IMPORT: our initial LEAN_PATH omitted ledger16 NJW's additional retained dependencies. This is an OWN selection/input error, not a shared launcher/host fault. NKB_ENV_REPAIR.json appends NJW_PATHS.json without changing earlier priority or any shared object. L048 read-only preflight resolves all15,922 expected closure modules, with zero missing/unknown entries and streamed selected-object/sidecar hashes. The support theorem sources and audit algorithms are unchanged. Environment change explicitly justifies L049 as the second and FINAL combined import. L046/L047 were never launched, replaced by L050/L051. No third import or unchanged full regression is authorized.

Canonical continuation: K024 failed before compilation because an owned config introduced a leading blank Rust flag. K023 also lacked the explicit optimized Rust flags and earns no credit. Corrected K029/K030 repeat the scalar window with optimized flags; K025..K028 were corrected before launch. No timeout was rerun.

Final: full combined audit PASS; remaining failure is row promotion, not a kernel/compiler/audit failure. NKB_CanonicalPrefix.source retains explicit child interpretations and is not a positive row root. The six Merkle rows retain the two scoped findings and their real call dependencies. All original failed/timeout receipts remain; no cap/timeout was raised.
