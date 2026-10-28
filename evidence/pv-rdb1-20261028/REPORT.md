# Deployed class-B row repair

**V186 RESTORED at its existing callback/library source-law boundary; eleven rows remain SUSPENDED. Privacy target not yet established.** No behaviour counterexample was found. A rejected historical source gate is not a behaviour finding.

Branch `codex/pv-rdb1-20261028`, exact assigned worktree retained. Base `6273e6206164ac60fbc68a49fa888f98b87476f1`. Host `/home/dombarker/project-offloads/codex-pv-rdb1-20261028/`. No push, crates/programs edit, ELF rebuild, key creation or cleanup. Shared rulings including (x), (k), (k'), (r), (r'), (r''), (s), and the host-restoration flag were read.

## Restored source association

[V186 record](rows/V186.json), [deployed complete-body binding](v186-structural.json), [final binding receipt](v186-final-binding/receipt.json), [source pins](v186-input-source-pins.json), [focused Lean receipt](54701-receipt.json).

Before: `PV_CBL_Op35Source.default_empty` states, for the selected op35 dictionary and every T, `(selected ops).op35 T = ok (alloc.vec.Vec.new T)`. The Lean/model statement stood; its native association was suspended after sysroot drift.

After: **the same equation, carrier, quantifiers and Result conclusion**. The complete deployed `Default for Vec<T>` body and the exact owned Rust reference used by the original extraction are both `Vec::new()`. Both resolve to the same deployed monomorphization, so the source equality holds for an arbitrary shared constructor, including every abstract Result variant. This is `PV_RDB1_V186.complete`; `selected_result` specializes it to the retained model result. The gate checks the original emitted reference equation too.

The changed constructor's body constructs a RawVec and sets the Vec live length to zero. `empty_from_zero_length` proves that any vector value carrier of length zero equals `Vec.new`, and `constructor_value` audits the empty list projection. Thus the changed dangling-pointer construction (`as_nonzero` versus the old `as_nonzero_usize`) needs no historical/deployed pointer equivalence premise for this row: neither default nor its reference dereferences that pointer or allocates. The constructor is shared, and its live length is zero. ZST capacity representation is not silently changed to zero.

Evidence class: **structural (K-1 substitute)**. This restores the existing op35 native-to-reference source association, not a kernel proof of Rust/LLVM/machine semantics. Existing runtime carrier, compiler, executable, allocator/world and side-channel obligations keep their original boundary. No dictionary or endpoint proof was edited. The new theorem is not presented as a replacement endpoint theorem.

## Row dispositions

Every row has an individually committed JSON record with its original closing theorem, before/after disposition, exact reason and fresh evidence references.

| Row | Status | Remaining native-link obligation |
|---|---|---|
| V164 | SUSPENDED | Complete compressor/reference deployed binding; changed NonNull laws and 27 conservative edges |
| V170 | SUSPENDED | New slice/drop pointer construction into existing u32/Global world law |
| V178 | SUSPENDED | Deployed truncate/separator/path and allocator laws; 609 conservative edges |
| V181 | SUSPENDED | Complete capacity checker/binding and deployed Layout/allocator law; 29 edges |
| V182 | SUSPENDED | Root gate passes; transitive extend/allocation/NonNull laws and 117 edges remain |
| V183 | SUSPENDED | Deployed repeat/layout and allocator-world bridge; 29 edges |
| V184 | SUSPENDED | Root gate passes; deployed NonNull cast law and six edges remain |
| V186 | RESTORED | Exact shared deployed constructor binding, as described above |
| V187 | SUSPENDED | Root gate passes; complete deployed iterator/from_fn/move binding and six edges remain |
| V195 | SUSPENDED | Root gate passes; deployed callee binding, panic attribution and 131 edges remain |
| V198 | SUSPENDED | Complete writer checker/binding, pointer laws, panic attribution and ten edges remain |
| V219 | SUSPENDED | Complete boundary-sum checker/binding, changed pointer laws and 29 edges remain |

The edge counts are the retained conservative MIR envelope counts, not proven reachable execution counts. [Fresh source audit](source-audit.json) checks attributed installed files without resolving those edges. No root-body match or finite fixture is promoted to complete transitive correspondence. The unrecovered complete checkers for V164/V181/V198/V219 are reported as gaps, not replaced by a different successful checker.

## Configuration and validation

Exact client root: `tools/r1-cost-probe`, `devnet_spend`, `r1p-check,aspis-r1-cost-probe/ct-host-prover`, rustc **1.94.1**, release opt3, debug assertions and overflow checks off. The exact 487-unit graph was reproduced with `--locked --unit-graph`; no code generation occurs in that capture. [Resolved units](resolved-features.json) include every crate's features and effective profile, including build-script profiles. Every scope/Lean receipt references its SHA-pinned configuration; project fixtures additionally retain their actual resolved dependency features. Std-only fixtures link std/alloc/core directly and have no feature-bearing project dependency.

All 172 core/statement Rust files and manifests match this branch's HEAD in the read-only replay source tree. All 2,048 attributed standard-library source checks match the installed 1.94.1 files. All 5,673 external Lean objects match the coherent privacy replay manifest before the first compile. Only own new PV_RDB1 modules are imported as project modules; own import source/blob/object fingerprints are recorded for dependent audits.

Finite native validation passed:

- V170: 260 paired u32 drop/world cases.
- V178: 774,256 path pairs; V182: 5,679,337 append pairs.
- V181: 1,025 capacity pairs; V186: empty default/new u32 headers without allocation.
- V183: 2,160 reserve pairs, including injected failures, overflow and ZST.
- V184: 99 non-Copy payload cases plus 33 Drop-bearing ZST cases.
- V187: 606 non-Copy ownership pairs plus 99 ZST pairs.
- V195: 108,309 serializer pairs, all 32 bytes; V198: 4,101 writer pairs, all 16 bytes.
- V164/V219: 768 compressor and 128 boundary pairs; supporting 128 polynomial pairs.

All of these are **finite validation**, not unbounded native proofs. Historical Kani evidence is neither rerun nor re-credited. K-1/K-2 restrictions remain; no contracts, copy stubs or chained arithmetic Kani route was used. No XR imports or definitions were used.

## Premise accounting and handoff

Removed: the V186 deployed default-to-owned-reference association obligation at its existing library source-law boundary. Retained: the other eleven native links, all endpoint premises including E1/E2, real RunJoin, client route, compiler/executable correspondence, L1/L2/L3. Added/changed trust items: **none**; T remains exactly entropy_law, entropy_kernel, observation. The simulator and observer are unchanged. No claim that `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` is established.

Next deliverable: a deployed pointer/slice-construction law for V170, followed by its complete destructor/world binding, or complete deployed NonNull/move bindings for V184/V187. Those missing laws, rather than further unchanged fixture runs, are what the suspended rows require.

## Final focused replay and budget

Combined audit **54797**, focused universal V186 bridge replay **54798**: exit 0, only `propext`, zero swaps. Both are new modules; no unchanged full regression ran. The original dictionary theorem is reused unchanged by the source binding; the focused replay checks the new native-link bridge and empty-value consequence, not the package-wide endpoint import cone.

Totals: **4/100 Lean attempts** (54700 initial, 54701 expanded zero-length law, 54797 audit, 54798 replay), **20/120 native scopes**, **0/0 Kani**. No refusal, cap increase, killed job, transient transport loss or failed compiler run occurred. Some historical structural expectations reject the deployed sources, as itemized above; the overall capture script's exit 0 does not turn those row gates into passes. Peak Lean RSS 2,629,236 KiB; peak native RSS 565,568 KiB; all swaps zero. Full target, source revision, exit, wall, RSS and axiom lines are in each receipt. [Final machine-readable audit](audit.json).

Work stops after removal of V186's native-association obligation, as permitted by the shared completion rule; the remaining budget is unspent, not exhausted. The other eleven rows stop at the specific missing proof/binding named in their records. No new universal claims are merely proposed as proved. Host cargo targets and verified ELF fixture executables were removed after recording available SHA256/size data in [cleanup.json](cleanup.json); shared Lean objects and source evidence are retained. No keys were created or removed.
