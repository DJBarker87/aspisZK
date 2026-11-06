# NKK findings

NKK-F1 (K012): worker harness expected raw u32 limbs to survive E::new. Frozen WideExact::new canonicalizes every limb; K012 fails exactly one assertion in the worker reference on arbitrary noncanonical constructor input. This is not a shipped-code mismatch. Replacement compares each returned E with the SAME oracle reply E::new(values), including its normalization. No stronger root or child-success precondition is added. E replies from this generator range over canonical E; the CLOSED decoder's successful replies are canonical, which must be established during association. K replies still overapproximate all four raw u32 words. Original failed evidence retained; no harness name changed and no limit raised.

L010: queryMid clause tactic reached the default 200000-heartbeat whnf limit by trying a deep tail theorem before its eight prefix binds. Retired shape. Replacement removes speculative tail matching, uses explicit eight bind steps and named literal tail, with pure-lift reductions in a new small module. No limit raised.

K001/K002: own scratch lacked frozen tools/r1-builder-reference inputs, then KMX root include. Both are compile failures before proof. Added the previously pinned tool sources and exact supplied KMX include; validation unchanged. No host/lead infrastructure edited.

NKK-F2 (K021): the semantic wrong-cursor control unexpectedly PASSED. The worker used the same cfg flag to flip the implementation cursor and the expected frame cursor, so the two corruptions cancelled. This is a faulty worker control, not evidence of Kani unsoundness. Retained under the original harness name and no credit for that control. Replacement separates the implementation-corruption flag (NKK_bad_view) from frame-expectation corruption (NKK_bad_backing), keeps the property unchanged/stricter, and requires a failing control before association. No rename, timeout or cap increase.

NKK-F3 (K031): proof_digest_stage with an arbitrary byte observation into the57607-byte proof backing reached the90s CBMC timeout. No credit, no larger cap/timeout, no unchanged rerun, and K032's planned inverse is cancelled because there is no positive for that shape. Existing NJJ_K038/039 descriptor/reply checks are retained within their stated domain, but they are not silently promoted to this full byte-frame property. A replacement must split a true arbitrary source window and prove the complete frame/partition transport, rather than zeroing unobserved bytes or using a fake oversized Rust slice. Independent digest/tail/return members continue.

NKK-F4 (K033): public_digest_stage's extra checkpoint-frame observation incorrectly reused a public index (<1880) on the1768-byte checkpoint, so the worker harness failed a bounds check. Replacement uses the independently bounded checkpoint-prefix observation (<1736). No shipped mismatch or stronger caller precondition. The old K031 byte-observation shape also contained this invalid extra observation and remains retired; it is replaced by the successful full-heap modifies contract K042 with K046/K047 controls, not silently reclassified as a proof of byte-frame failure.

K031 replacement: slice_fidelity_contract/real/unimplied/modifies controls K032/K037--041 pass/fail in the required pattern for borrowed slices and Result<Unit,Error>. K042 proof_digest_frame_contract passes with exact modifies(calls,ptr,len), protecting proof/stored bytes and log.reply; inverse ensures K046 and out-of-footprint reply write K047 fail. This is P6/D188 option-A native-contract semantic transport, reclassification, no new trust. Source/actual-log instantiation remains a Lean obligation.

## F5: own export paths input omitted

NKK_L019 exited1 after copying the selected objects but before closure pinning: own runner did not upload NKK_PATHS.json used by NKK_export.py. The client collector then failed trying to fetch the absent digest. The submitted receipt and diagnostics were recovered read-only, not resubmitted. Own runner now uploads paths and the read-only retention script, and collects their reports. NKK_L020 is the repaired export (same-or-stricter closure/hash validation), with retention included; L021 verifies it. No proof/audit rerun, shared infrastructure change or deletion.

## Allowance accounting correction

The inherited client initially limited numeric L labels to100, including setup/link/audit/export jobs. At that point only89 actual Lean compiler invocations had run. Own runner now enforces the user's100 actual Lean invocation maximum from terminal receipts (and50 actual Kani/zero extraction), independently of labels; it does not weaken admission, resource, source or audit checks. Additional source joins consume the remaining compiler allowance. The second combined audit is justified by these new sources, not an unchanged regression.

## F6: query tail speculative reduction

L104 hit the unchanged200000 heartbeat limit in isDefEq while a repeat-first rfl speculatively compared the full six-bind continuation. That shape is retired. L105 names each of the six raw bind prefixes and the validate reply explicitly before checking the literal emitted-try tail. No cap, timeout or elaboration limit was raised.

L105 reached the now-small emitted-try tail and failed definitional equality; L106 split the full actual Result and passed. L108's generic simplification stopped before reducing the first Result bind; L109 names and rewrites each actual query-window Result in order and passed. Both original failed receipts remain; neither was a timeout or memory kill.

## F7: final grouped raw walk exceeded the scope timeout

L113 (second full combined raw walk, new110-root source set) exited124 at180s after proof0..proof9 completed with exit0; final proof10 did not complete. The old first-audit proof10 artifact is excluded from final acceptance. No cap/timeout increase and no full rerun. L118 isolates only final proof10 (the remaining10 roots), same driver/import/object pins and limits. NKK_FINAL_WALK_MANIFEST.json selects each final group from its exact parent attempt; final verification checks the ordered group matches the final110-root inventory and all roots have equal raw/Lean standard axioms. NFX/source/export checks then continue without any further Lean or Kani invocation. Full combined audit count remains two.
