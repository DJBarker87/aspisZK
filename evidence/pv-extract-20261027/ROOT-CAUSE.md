# Extraction preflight root cause and diagnostic results

## Pinned guard

Host `/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor/base/src/Main.ml:730-761`. The reference visitor is :745-752, scans all `f.signature.output` at :756, throws at :760-761. Generator `tools/prover-rw-20261023/rng-extractor/reject-drop006.py:8-36` (host same relative script, :24 is the reference test). Candidate007 patch qualifies the visitor as `Types.iter_ty` and constructor as `Types.TRef`; the policy is unchanged. Exact pinned Main SHA256 `da1cd6085dd0d0881e8632c12a35091baa096a62c28d5db8068cb1f581e64f23` was checked before and after this job.

It rejects **any syntactic reference anywhere in any function output type in the entire imported LLBC**, including foreign opaque declarations, nested `Option<&T>`, and helper `&mut` outputs. It does not restrict to selected exported roots, inspect reachability after passes, or distinguish shared from mutable references. Independently it rejects every structured Drop statement. Both guards run before pre-passes, borrow-checking and emission. This is not Charon's rustc borrow checker rejecting Rust.

History: commit `bb9ec678e231a44280e1463d189d00885a7f4cd1`, “Check refined error operations and reject unsupported drop paths”, 2026-10-24. The script docstring states conservative whole-crate rejection, no Drop erasure, and no implementation of destructor or escaping-reference semantics. Its inserted comment says the inherited Drop path does not call drop_glue, regardless of drop_as_no_op. This is a soundness boundary, not merely an optimization. LOG D191–D208 records failed loan/Drop implementations and no adoption; D251 on research identifies op223 as a shared obstruction. We do not infer that arbitrary ref-returning functions are supported just because a no-guard translation exits zero.

## Isolated experiment

Own host root `/home/dombarker/project-offloads/codex-pv-extract-20261027/`. The pinned source/tools and launcher are untouched. `prepare_host.py` creates `pipeline/{base,charon,deps}` with source/cache exclusions; `build_diagnostic.py` builds the same copied backend with only the Main preflight block removed (both conservative checks), release OCaml profile, four jobs, pinned Docker image, 6G/8G/noSwap/64 limits and fresh before/go admissions. The initial source-copy retries encountered a root-owned build-cache lock/destination permissions; these were file-copy failures, not compiler attempts. A fresh `pipeline/` copy excludes caches. The build passed in 56.21s, GNU max RSS590236 KiB, cgroup memory peak1894674432 bytes, swap0. These are different metrics.

Fresh Charon runs on the copied source use pinned Charon0.1.223, nightly-2026-06-01, `--preset aeneas --mir built` (then optimized), release/offline/jobs4, start-from exact logup compressor and include exact compressor/lift. Both pass. Exact command arrays, output/time logs, before/barrier admission and source revision are in `charon-op223-{001,opt-002}/`; corresponding Aeneas commands and stack traces in `aeneas-op223-{001,opt-002}/`. `output-hashes.json` records input LLBC, tool and generated output hashes; there is **no** op223 Lean output hash because neither attempt emitted Lean.

Both op223 Aeneas variants fail exit2 with `Not_found`, at `interp/InterpReduceCollapse.ml:1991` (`AbsId.Map.find abs_id !nabs_map`), in `collapse_ctx_following_sequence`, called by loop-context target matching. That code remaps IDs in a sequence of shared borrows after context merging. The absent mapping is an internal invariant failure; no sound replacement is asserted here. The initial preflight therefore masks a real downstream loan/context obstruction for this graph.

The root `compress_tagged_tuple(tag, values: &[M31], lambda) -> QM31` returns an owned value with only four u32 limbs; no reference or authority escapes its result, and no destructor-bearing owner is created by its source body. Its loop introduces a local shared slice iterator, whose `next` returns `Option<&M31>`; each limb is copied and accumulated. Thus the *public escaping-result* rationale does not apply to this root. But iterator shared loans still require correct internal processing across iterations: return-by-value alone does not justify bypassing the failed context match. No extraction receipt usable for a source row was obtained.

## Other affected graphs, no-guard diagnostic only

All invocations use copied LLBC inputs in own `inputs/` and the diagnostic binary, strict joins/abort-on-error retained, one capped scope at a time. Hashes identify the exact graph tested; historical sources may contain shims and broader inclusions. Fresh Charon was run for op223; prior Charon input receipts were reused for the other graphs. This is not a claim that every possible MIR selection fails.

| op | Aeneas exit | first downstream obstruction / emission |
|---|---:|---|
|79|2|same InterpReduceCollapse.ml:1991 missing shared-borrow ID|
|132,133|2|TypesAnalysis.ml:237; active_counts array of mutable references, source hiding.rs:107-110|
|205,216|2|ADTs containing nested mutable borrows unsupported|
|212,217,219|2|mixed mutually recursive generic-array iterator/trait groups, Interp.ml:103|
|215|2|new value/destination type mismatch, InterpPaths.ml:264; wrapper.rs:171|
|222|2|same InterpReduceCollapse.ml:1991 missing shared-borrow ID|
|223 built/optimized|2|same missing shared-borrow ID; no Lean emitted|
|249|2|can't copy a mutable borrow|
|258|2|could not join contexts, InterpJoin.ml:1680; ct_pole.rs:23-25|
|36 reference variant|0|owned-index/reference helpers emitted, not shipped generic Vec→Array; Types/External/Funs typecheck42400,42402,42403|
|224 wrapper variant|0|wrapper emitted with opaque rows/helper/map_err calls; Types/External/Funs typecheck42401,42404,42405|

No generated external template was installed. For the two emitting graphs, opaque declarations were represented as explicit universally quantified `ExternalFuns` fields, with exact generated bodies retained and imports relocated. Those checks establish well-typed emitted control with parameters, not the opaque functions or destructor behavior. Original templates are retained only by hashes; no new axiom is introduced. The op36 input is a candidate reference; op224 is a wrapper whose dependencies remain opaque, and whose graph also had a Drop guard. Neither result discharges a row.

Additional source-loan obstruction from cb3: op253/V260 `Weights::raw`, weights.rs:223, returns a value but borrows tensor/extra arrays from self. Owned split probe fails `InterpBorrows.ml:2731` at resume6_owned_weights.rs:8 in shared-loan cleanup. This is a different downstream failure, not this syntactic preflight. It is included in the design comparison and not silently treated as solved by an index loop.

## Present boundary

No `PV_Ext_Op223Source.op223_source` is published, since there is no accepted shipped compressor extraction. V240 stays OPEN. V164 retains exactly `ops.op223 = @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)` as P_source_p6, together with its existing P_proof_bytes and reservation equation. No endpoint/deployment premise changed; zero removed. Target not yet established. Next: route comparison and reviewable host-only patch, with pinned-guard extraction of its leaf as a feasibility check.
