# K-3 applicability conditions

The tool defect is reproduced in pinned Kani 0.67.0 under deployed features, frozen selected dependency graph, unchanged frozen lock and offline compilation. No compiler repair or quarantine lift is claimed. Every run keeps NBZ_native / NBZ_return_carriers / NBZ_mark_none names. The native Rust property `None.is_some()` is false independently of static state.

## Mechanism and decision

The retained NEF_K2_ROOT_CAUSE.md identifies the exact compiler mechanism, with pinned source hashes in NEF_TOOL_SOURCE_PINS.json: codegen_const_allocation reuses alloc_map entries keyed by Allocation value; codegen_static registers a mutable initializer in the same map. A same-key allocated constant materialized after that registration can read the mutable symbol. A reached write before the constant read can therefore change its value. Stable-fingerprint traversal order matters. Equality of visible initializer bytes alone does not establish key equality or order. Scalar immediate constants can bypass this path. These are necessary ingredients for this diagnosed route, not a complete theorem excluding other tool defects.

The checked script NEH_scan.py uses a deliberately broader decision procedure: any static token, unresolved pinned Rust input, include/macro definition or absent Rust input is AFFECTED. Otherwise it reports UNAFFECTED **for the recovered receipt-pinned inputs only**. It does not infer a missing dependency closure or remove K-2 quarantine. AFFECTED includes read-only statics and comments/lifetimes, so it is a suspension/inspection overapproximation, never a bug verdict. No zero/None/byte-pattern whitelist is used. NEH_check.py checks every retained minimal source and requires every observed false-pass example to be AFFECTED; boundary tests cover unresolved inputs, macros and local records. No source-only classifier can establish compiler allocation order for arbitrary Rust expansions; unresolved closures remain suspended.

## Finite matrix

All tested None values here are Option<NonZeroUsize> unless specified. Each entry has the exact source and complete receipt under NEH_Knnn.

| Attempts | Static / constant shape | Verdict for deliberately false property |
|---|---|---|
| K005,K006,K018,K019 | zero usize; write one; None as NonZeroUsize/reference/function pointer; original two-counter form in K019 | incorrect SUCCESSFUL |
| K003,K007,K008,K009,K013,K014,K015 | scalar/array constants; unequal initializer bytes; byte-pattern constants | correctly FAILED in these tested shapes |
| K011,K012,K017 | unwritten usize / local scalar / unwritten static with None | correctly FAILED |
| K020 | AtomicUsize::new(0), store(1), None | incorrect SUCCESSFUL |
| K021 | Sync wrapper of UnsafeCell<usize>::new(0), write(1), None | incorrect SUCCESSFUL |
| K022 | zero usize write; additionally assert Some on explicit unwritten static None | FAILED; does not establish whether a later literal is corrupted |
| K023 | usize initializer one, write two, literal None | FAILED |
| K024,K025 | byte-array initializer / u32 initializer, write one, literal None | FAILED |
| K026,K027,K028 | u64 zero / Option<NonZeroUsize> None / [usize;1] zero, write one, literal None | incorrect SUCCESSFUL |
| K029 | zero usize read without a write, literal None | FAILED |

K001/K002 were setup/selection failures; K004 had an Observer type mismatch; K010/K016 used std in a no_std crate. They give no semantic evidence. Corrected sources use fresh attempts; no timeout or memory kill was rerun. K020/K021 show that restricting the ban to static mut would be unsound. K023–K029 support initializer-key/write dependence, but their failures do not certify those shapes universally unaffected. Static initializers of nonzero equal patterns and explicit unwritten-static observations beyond K022 remain diagnostic gaps, not exemptions.

No Lean theorem is asserted for Kani's compiler implementation. Axioms audit: N/A. No security bound, frozen source, artifact or trust item changes.

The final inventory additionally flags unknown function-like macros, attribute macros and nonbuiltin derives; this deliberately strengthens the initial scanner. For K022 the explicit unwritten-static `is_some()` assertion is the failing check at NBZ_native.rs:5:43. Thus the unwritten-static observation was not corrupted in that concrete experiment. K022 still gives no universal read-only-static exclusion.
