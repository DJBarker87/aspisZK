# from_fn loop-join diagnosis and guarded matcher candidate

This packet records the v2 Aeneas diagnostic and a source-only v3 matcher
candidate. It does not contain an accepted semantic repair, a generated Lean
proof, or a run of the v3 candidate.

The v2 Aeneas statement trace reaches the first failing loop `continue` after
the `Guard::push_unchecked(item)` call (Rust core `array/mod.rs`, lines
949–957). After the call the trace still shows the updated reference
`MB@22` and an ended-ignored-mutable-borrow abstraction linking it to the
old Guard loan. At the following loop `continue`, the projected context
maps `Guard.array_mut` to bottom, while the source loop context still
carries the old mutable loan through the Guard (`MB@11` / `ML@11`). The trace therefore
localizes this failure to the call’s post-state abstraction, not the earlier
length read. The selected v2 LLBC declares `try_from_fn_erased` transparent
but `Guard::push_unchecked` Foreign/Opaque; this is the relevant missing body
boundary. The source body was inspected and updates `initialized` and the
selected MaybeUninit element; that inspection is not itself a proved
field-preservation theorem.

The separate v3 source candidate tightens the `TTraitType` context-match
special case. It accepts only structurally equal projections and uses a new
visitor that descends into dyn-trait internals even when
`type_analysis_ignore_dyn` is enabled. This prevents the older config-sensitive
region visitor from treating a region hidden inside `TDynTrait` as absent.
The v3 matcher source is pinned at SHA-256
`0d2ab7873780feaea346facc38f5429144153f6e93a08aef636509505216bb18`; its
delta from v2 is `source/v2-to-v3.patch`. No v3 build or runtime test is
claimed.

`review/test_trait_type_guard.py` is a predicate-level Python model only. It
tests structural equality and rejection of differing clause/item/generic
arguments, nested regions, and other constructors. It is not an OCaml matcher
unit test and does not test the strict v3 visitor implementation. The earlier
v2 matcher review and its config-sensitive visitor limitation are retained in
`review/README.md` as historical context.

The LLBC source input to the v2 trace is SHA-256
`32f4b2416a2566ab2ceb6bd04f10a1b601e765fab9217a4fe3501cab0b0340a4`. Its
recorded Charon provenance is Rust `1.98.0-nightly (14210df0e 2026-05-31)`;
the extracted `array/mod.rs` hash is `fa149bb7f1e856350ccbf94cd402f368ec7f613b8a1d1eeeafffe85b5e75277f`.
This is not the frozen SBF Rust 1.89 toolchain. The exact v2 trace command,
limits, exit, RSS, and swap are in `trace/receipt.json` and `trace/run.time`.

## Changed selector preflight

D18's later, selector-only Charon output is recorded in
`selector-output.json`: `/tmp/s4-fromfn-guard-transparent-v1-20261022.llbc`,
SHA-256 `551bbefc19ef647c0670f119bfac8f2589d677169c49101fc7b584d0b71fa3bc`.
It changes `Guard::push_unchecked` (Fun 21) to a transparent structured body;
its Guard drop glue is also transparent, but forwards to `core::array::drop`
(Fun 35), which remains Foreign/Opaque. `MaybeUninit` (type 7) is transparent
but represented as an LLBC `Union` with `uninit` and `value` fields. Therefore
the transparent-push output is not yet known to be translatable by Aeneas.

The local source checkout `external/aeneas/ZK-aeneas-v5-outer`, HEAD
`4e677bf5e9ac8577127e76488d98533123035401`, has explicit unsupported-union
branches: `TypesAnalysis.ml:513`, `InterpExpansion.ml:711`, and
`PureMicroPassesGeneral.ml:1674–75`. Those source file hashes are available in
the local checkout, but binary/source identity for the selector-runner's
Aeneas executable is not established here. This is a preflight blocker, not a
claimed runtime failure. No Aeneas run was made on the changed selector LLBC.
The LLBC also leaves `usize::unchecked_add` (Fun 33) and array drop (Fun 35)
Foreign/Opaque; these are additional concrete boundaries after
`push_unchecked` becomes visible.

Do not interpret the v2 mismatch as evidence about the transparent-body LLBC.
