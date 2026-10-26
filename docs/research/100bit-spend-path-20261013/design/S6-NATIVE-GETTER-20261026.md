# Native same-box S6 getter boundary — 26 October 2026

**Established:** on every initialized typed native terminal statement in a
live Box, the release `semantic_public()` selects the correct payment variant
and returns pointers to that SAME statement's payment and lane_transition
fields. `common()` and `nullifier()` also return pointers into that same owner.
This is a source-tool certificate under Kani's native allocation model, not a
Lean theorem or complete S6 closure.

Exact target: `proofs::boxed_semantic_borrows_same_statement` in
`tools/s6-native-getter-20261026/proofs.rs`. It directly calls the unchanged
release methods from `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs`
and uses the original native r0 Public enum. It does not replace the enum,
statement, payment, lane, getter, Box or allocator with a simplified carrier.
No source change/adoption is proposed. The current source freeze is
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.

All native statement fields are independent symbolic scalars, including all
32-byte bindings, every raw M31 coordinate and both twenty-digest frontiers.
Both enum variants are covered. No canonicality, validity, successful decoder,
byte-output equality or child-return hypothesis is imposed. Safe native struct
constructors and literal arrays initialize the fixture; no unsafe/transmute,
getter/decoder stub or kani::assume is used. The generator reads every field
of all six native structs from the pinned source and emits each array
coordinate independently; Rust checks the actual native field types and array
sizes. `generate.py --check` verifies the maintained constructor source.

This is TOTAL for the getter projection over the admitted initialized typed
state in the Kani normal-allocation model. It is not decoder totality or total
SDK execution. Native allocation failure/abort, private-memory interpretation,
initializedness of an actual decoder output, SDK/account/runtime effects and
source-to-SBF lowering remain outside this result. The fixture's safe
construction is not a proof of those properties in the enclosing execution.
The default Kani allocation model is retained; uninit checking is not enabled.

The positive check passes **118 assertions, 2/2 variant covers**:
exit 0, 14.289762828s, peak RSS 235688KiB,
swap 0. Scope MemoryMax4GiB/High3GiB/MemorySwapMax0, no pressure/OOM.
No different-owner substitution is allowed: `wrong_box_negative_control`
constructs a second live Box with all native values copied identically, then
asserts that its selected references belong to the first. It fails exactly
that assertion, **1/82 failed**, exit 1,
12.855104754s, 260188KiB RSS, swap 0.
All other safety/unwinding checks pass. The control used a 2GiB/High1536MiB/
SwapMax0 scope and reused the exact successful native compilation.

Source-only packets retain all exact source/tool/sysroot/import pins,
commands, environments, stdout/stderr, timing, fresh admissions, cgroup peaks
and events. Six path-only packages and their production features are pinned;
fixture manifests omit only dev/test declarations. Every native source in the accepted v5
check is byte-identical to the release Git source, with no proof attributes
or body edits. #print axioms: N/A (Kani). No Lean axiom is added. Kani's
compiler warns about unsupported constructs in unrelated crate functions;
its reachability checks are retained, and the reached positive target passes.
The explicit `-C opt-level=3 -Z mir-opt-level=0 -C overflow-checks=yes` flags
and one build job are recorded, independently of Cargo's generic dev label.

Retained failed/preflight attempts:

- v1:6GiB reservation denied, no scope/compiler.
- v2: compile stopped at missing frozen cfg(kani) tree reference,15.44s,
  551624KiB, zero swap; no solver.
- v3: compile stopped at missing frozen glue include,12.91s,552328KiB,
  zero swap; no solver. The reconstruction preflight now resolves all literal
  Rust path/include dependencies recursively from the immutable source.
- v4: generic Arbitrary array constructors timed out at122.02s,
  2805580KiB RSS, zero swap, no OOM. Loop inventory identified generic array
  constructors. Replaced them with safe independent scalar/literal constructors
  preserving the full typed domain; no timeout or memory increase. Final v5
  leaves ALL native source bytes unchanged and has no Arbitrary derives.
- v5 negative: compilation succeeded, but a new 8GiB reservation elsewhere
  made the fresh verify-phase admission fail. No negative solver launched.
  v6 reduced its own cap to2GiB (positive predecessor cgroup peak610410496B),
  reused the identical successful compilation, then ran the negative control.

Before/after enclosing obligations: the existing S6 source/model theorem still
has the SAME SDK extraction, reconstructed-statement identity and native
ownership/runtime prerequisites. No enclosing theorem premise was removed by
this certificate alone. The concrete native getter association is now checked
instead of justified solely by equal values; actual decoder-to-native-object
and SDK stage1/extraction composition are the next consumers. L176 remains
open for that native decoder/ownership/error/cleanup join. L179 belongs to the
S2 owner; L186 to release lowering. S1 preparation model/field composition now
has the lead's SAP owner and is not duplicated here. Whole S1/S2/S6 and the
per-attempt 100-bit target remain **not established**.

Validation: `python3 tools/s6-native-getter-20261026/check.py` (PASS).
Evidence: `evidence/s126-current-caller-20261021/s6-native-getter-terminal-v1/`.
No binaries, GOTO, LLBC, ELF or native build cache are included.
