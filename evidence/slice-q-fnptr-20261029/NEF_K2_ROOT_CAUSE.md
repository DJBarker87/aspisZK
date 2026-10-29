# K-2: mutable-static / constant allocation alias, with false PASS

**New result:** NEF_K002 verifies a false assertion for a literal None. The earlier bounded KNC direction result does not generalize. Quarantine remains; no tool correction is adopted.

## Reproduction and diagnosis

All experiments use the original `verifier::candidate::NBZ_native::NBZ_return_carriers` / `NBZ_mark_none` names. NEF_K001 reproduces `assert!(obs.is_none())` FAIL for literal None under the deployed library features. It uses no copy, KMX stub, contract, allocation, or indirect call in the reached harness. NEF_K002 changes the assertion to `is_some()` and restricts the arbitrary i to exactly 1. It reports **0/58 failed**, exit 0, 5.014 s, peak RSS 292960 KiB, swap 0. Optimized native replay NEF_I002 gives positive is_none exit 0 and negative is_some exit 101. This is a reachable false PASS, not a cover, unsupported-feature warning or solver timeout.

NEF_I001 dumps the K001 GOTO binary. At the call to NBZ_mark_none, the source `None` is emitted as:

```
NBZ_mark_none(*(cast(cast(address_of(NBZ_Q), unsignedbv[8]*), OptionFn*)), phase)
```

Immediately before this, GOTO assigns i into NBZ_Q. Thus the supposedly constant None bits are the current mutable counter bits. The callee correctly tests those wrong bits against NULL. At i=1 this models Some, while the native source passes None. NEF_K003 changes only NBZ_Q's initializer from 0 to 2, leaving its runtime write of 1 intact: the false is_some assertion now FAILS. This is a causal allocation-content control, not a rename workaround.

## Compiler mechanism

Read-only source checkout Kani tag kani-0.67.0, commit `4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d`:

- `context/goto_ctx.rs:77`: `alloc_map: FxHashMap<Allocation, String>`.
- `codegen/static_var.rs:18-29`: codegen_static obtains the evaluated initializer and passes the static's mangled name to codegen_alloc_in_memory.
- `codegen/operand.rs:130-140`: constants not handled by try_codegen_constant use codegen_const_allocation and are loaded by dereferencing the returned address.
- `operand.rs:492-509`: codegen_const_allocation looks up the Allocation by value and reuses its previously registered symbol.
- `operand.rs:595`: codegen_alloc_in_memory inserts **every** allocation, including a mutable named static initializer, into that same map. Its key omits symbol identity and the caller's is_definitely_const / has_interior_mutability distinction.

A zero initializer registered for NBZ_Q can therefore become the backing symbol for a same-key None constant. `kani_middle/reachability.rs:71-72` sorts reachable MonoItems by their stable fingerprint; `to_fingerprint` hashes the internal MonoItem in the rustc stable-hashing context (lines 476-485). `compiler_interface.rs:160-186` then codegens functions and statics in that one interleaved order. Changing module identity changes these fingerprints and hence can change whether the mutable static initializer is registered before the constant is materialized; this explains the existing module-name sensitivity without treating a rename as a repair.

Primary source: https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani-compiler/src/codegen_cprover_gotoc/codegen/operand.rs . Source hashes are in NEF_TOOL_SOURCE_PINS.json.

## CBMC exclusion

Read-only CBMC tag cbmc-6.8.0, commit `cdee49cb1a32c6d6703cebf6ae67161977264ad4`. `src/goto-programs/remove_function_pointers.cpp:379-452` rewrites indirect calls into guarded candidate calls and asserts/assumes false on fallthrough. The K001 reproducer contains only direct calls; its malformed literal read already exists in the pre-verification GOTO. Function-pointer removal is not the root cause of this reproducer. Niche decoding (`rvalue.rs:971-1039`) correctly tests the wrongly supplied backing memory.

## Exposure / limits

The demonstrated trigger is a constant lowered through codegen_const_allocation whose Allocation key matches an already registered writable static initializer, followed by a write to that static before reading the constant. Option<fn> is one affected carrier. Both false FAIL and false PASS are demonstrated. Native arithmetic, scalar immediate constants and all unrelated passes are not invalidated merely by this example; conversely, this mechanism is broader than a theorem that all function-pointer cases are only over-approximated. Exact additional carrier controls are recorded separately. A matching key, registration order and reached write/read are needed; a text name match alone is insufficient.

No pinned toolchain was modified or patched. A tool fix would need to separate constant interning from mutable named statics (and validate static identity, relocation, interior mutability, cross-crate and order cases), then rebuild in a sandbox and replay controls. This worker instead supplies an independently checked source specialisation route, proposed for lead review only.

## Additional carrier controls

NEF_K004 (Option<NonZeroUsize>) and K005 (Option<&u8>) also falsely PASS is_some for literal None under the identical runtime counter write. K006 (one-element usize array) and K007 (immediate usize) correctly FAIL their false equality to 1. These are observed carrier controls, not an exhaustive characterization of every allocated aggregate. NEF_R005 supplies optimized native failures for all four false properties. The Option cases broaden exposure beyond function pointers; scalar immediates bypass codegen_const_allocation as shown in operand.rs:152-190. This finding warrants lead review of writable-static/allocated-constant interactions in prior oracle-log harnesses; this worker changes no other lane's credit.
