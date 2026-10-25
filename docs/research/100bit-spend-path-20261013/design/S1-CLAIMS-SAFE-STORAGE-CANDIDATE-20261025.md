# Claims safe-storage candidate: NOT ADOPTED

**S1 remains OPEN. No enclosing source/caller premise was discharged.**
The previous goal turn made progress by isolating the Kani layout failures
and checking the actual allocator path. This continuation tested the remaining
row-step route and produced the isolated candidate below; it does not re-label
either result as a whole Claims proof.

## Why another initialization-check retry is insufficient

The fixed full-word sampler and checked slice construction from
`S1-NATIVE-INIT-LOCAL-20261025.md` are reused. Allocation setup is changed to
`Box::<Claims>::new_uninit()`, keeping the full real boxed carrier and original
native row-write function. Smallest compile-only attempt `s1-init-step-v1`
passes. Changed full verification `s1-init-step-v2` fails 2 of 712 checks:

* Kani rejects raw-pointer/union interaction at the prefix row write's
  `out.as_mut_ptr()` operation. This is the same operation used by the frozen
  native row step; using an alternate allocation setup does not solve it.
* The proof-harness static `Option<r1_wire::Error>` has an unsupported niche
  layout. This second limitation is in harness bookkeeping, and is not a
  claim that frozen Claims stores such an option.

Zero of the three covers are satisfied in this failed run. No result is
promoted to initializedness proof, arbitrary-heap transfer, or whole-function
totality. No initialization check was disabled and no allocator/SDK behavior
was replaced with an opaque success assumption. The separate actual frozen
allocator attempt remains blocked by `TryReserveErrorKind` niche-layout
support, as retained in the prior packet.

## Concrete source candidate

`rust-candidates/s1-claims-safe-storage-20261025/r1_semantic.rs` is a complete
copy of frozen `25866ec331cc7ce27dd9956609c11d32fa8fa58a` with only the private
`claims` function replaced. `claims.rs` and `candidate.patch` expose the exact
edit. The integrity gate reconstructs the complete candidate from that one
replacement and checks the full source hashes.

The candidate validates record 25 first, obtains three initialized zero rows
with the existing fallible `heap::filled`, converts that storage to the same
`Box<[[QM31;29];3]>`, then assigns decoded rows at offsets 0, 29 and 58 using
safe indexing. The storage-to-box conversion occurs before the first decode.
The signature, complete field/error types, decoder call order, early-return
operator and allocation-error mapping are retained in the source. The zero
values are overwritten by all three successful decodes. No `unsafe` block is
present in the candidate function; its standard-library/helper dependencies
still need their own source/runtime bindings.

These are structural properties of the candidate, **not established native
equivalence**. The extra slice-to-array conversion error maps to
`Error::Allocation`; showing this branch unreachable requires the actual
length-three result from `heap::filled` and the standard conversion binding.
The candidate also writes initial zero rows, so neither identical execution
effects nor equal CU/stack cost is assumed.

## Required source decision and gates

There are two distinct routes to the unchanged release contract:

1. Keep the frozen body and supply a sound native initialization/allocation
   proof through its union pointer operations and real fallible allocator.
   Current Kani 0.67 checks are unsupported at those points. Disabling checks,
   deleting rejected/error paths, or substituting a successful allocation is
   insufficient.
2. Consider this isolated safe-storage candidate for a future source freeze.
   Before adoption it needs actual extraction and complete caller installation,
   all-outcome source equivalence or an explicitly reviewed replacement source
   refinement, and the affected source/artifact/CU re-pins. Nothing here
   authorizes silently moving the existing security proof to it.

Specific open gates for route 2:

* Prove fallible allocation/rejection, initialization and cleanup, the
  length-three conversion, and returned values on every decoder error/success
  path. Preserve the actual record identity, three offsets and query order.
* Audit the two concrete allocation paths and their Rust/allocator behavior.
  Equal requested payload sizes do not prove equal allocations, reallocations,
  failure timing, drop behavior or complete runtime effects.
* Extract the complete changed function and consume its actual body in the
  existing S1 caller theorem. Reuse the already checked full row-step and
  bounded three-row composition where their actual bindings apply. A new
  abstract `Claims` parameter is not a concrete instance.
* Run affected stack/CU/two-transaction checks and source/tool/artifact
  re-pinning, followed by the coherent enclosing replay. These are PREPARED
  obligations, not checks performed here.

No source decision is taken by this packet. Production, S2 and the other
owners' tracks are untouched. S6's remaining coherent shared implementation
join remains with the lead. The 100-bit per-attempt target, wire format and
two-transaction requirement are unchanged and **not yet established**.

## Validation and evidence

The candidate function's exact body, with only its original imports in a
minimal probe module, passes ordinary Rust type checking against the actual
frozen wire and core helpers. The rest of the full copied semantic module is
retained for review; this focused job does not claim to compile the complete
SDK/release dependency graph. It runs no theorem, SAT check, LLVM/SBF artifact
build, Aeneas extraction, runtime suite or equivalence proof.

| Target | Exit | Wall s | time RSS bytes | Observed aggregate RSS bytes | Swaps |
|---|---:|---:|---:|---:|---:|
| `s1-init-step-v1`, compile only | 0 | 1.573063 | 295845888 | 329482240 | 0 |
| `s1-init-step-v2`, unsupported verification | 1 | 2.250217 | 198295552 | 214155264 | 0 |
| `s1-claims-safe-typecheck-v1`, candidate type check | 0 | 3.404784 | 504578048 | 506675200 | 0 |

All local jobs use the shared atomic compiler lock, one Cargo job and the
2 GiB aggregate-RSS/64-process/180-second watchdog. No watchdog fired and no
unknown lock was removed. As before, sampled aggregate RSS is not a complete
historical peak census. These are focused Mac jobs; no Linux cgroup/no-swap
policy or Linux/SBF equivalence is inferred. No NUC/SSH operation ran.

The typecheck newly pins the full host sysroot library file set as well as
Rust/Cargo/top-level dylibs, all source inputs, command and environment before
and after. It does not retrospectively extend the earlier Kani receipts'
tool/import census. Exact nightly remains Rust commit `53732d5e0`, Kani 0.67
uses the separately pinned official Mac bundle. `#print axioms`: N/A for all
three jobs, no Lean declaration was added or compiled.

Source-only evidence is under `evidence/s126-current-caller-20261021/`:
`s1-init-step-20261025`, `s1-init-step-v1`, `s1-init-step-v2`, and
`s1-claims-safe-typecheck-v1`. The immutable prior packet is reused by hash;
no unchanged proof or full manifest was replayed. Its checker and the new
source/scope/hash checker pass:

```
python3 tools/s1-init-local-20261025/check.py
python3 tools/s1-init-step-20261025/check.py
```

Pinned raw source/log whitespace is retained. Maintained tools/design files
are checked separately. No binaries are committed.
