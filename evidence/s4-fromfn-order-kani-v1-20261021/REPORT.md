# Focused Kani checks: `from_fn` ordering and `Q::from_limbs`

These are source-cut operational checks under Kani 0.67.0 and its Rust 1.93.0-nightly toolchain (rustc commit `53732d5e076329a62f71d3c6901886ce8a71e812`, LLVM 21.1.5). They do not establish Lean/Aeneas correspondence, or identity with the frozen SBF Rust 1.89.0 toolchain (rustc commit `29483883eed69d5fb4db01964cdf2af4d86e9cb2`, LLVM 20.1.7).

## `std::array::from_fn`

The harness calls the actual `std::array::from_fn` and supplies arbitrary arrays of precomputed `(output, next_state)` values plus an arbitrary initial state. The closure records each index, state before/after, and returned value. It compares every element and event against explicit calls in order, and compares final state and call count. It covers N=4 and N=8 in `kani-v7`, and N=29 in `kani-v9`.

| Run | Source SHA-256 | Result | Time / peak RSS | Scope |
|---|---|---|---|---|
| v7 (N=4,8) | `a5f11a27423efcf797523d7f1cc1d70e335b2c29d27229525b8571c9525a919a` | 330 checks, 8 unreachable, 0 failed | 2.969 s / 209,792 KiB | High 2 GiB, max 4 GiB, swap 0 |
| v9 (N=29) | `c5fe1ab41866c6a2dce9e618ea955e039134d0309cda764c758edaa87fbc5daa` | 355 checks, 8 unreachable, 0 failed | 13.636 s / 1,649,824 KiB | High 2 GiB, max 4 GiB, swap 0 |

Both used unwinding assertions and report zero swap. The harness has no user-authored `kani::assume`, stubs, contracts, or disabled unwind assertions. The Kani logs do show the standard library's `NeverShortCircuit` impossible-residual branch as `assume(false)`; that branch is unreachable in the harness. Kani's unsupported-construct checks for `panic_nounwind_fmt`, `Location::caller`, and `same_allocation` report `SUCCESS`; no such check is `UNDETERMINED`. Eight unreachable checks are reported per proof. These details are retained in each raw log.

## Four-limb Q constructor

The source-cut harness uses the exact retained predicates from the frozen `canonical::Q::from_limbs` source (`x.iter().all(|&v|v<P)`) and the isolated candidate (`a<P && b<P && c<P && d<P`). `check-q-source.py` verifies the original/candidate snapshot hashes against `source-pins.json` and checks those expressions against the Kani cut. The Kani proof compares the `Option` branches and, on `Some`, all four coordinates individually to avoid delegating the check to an aggregate memory comparison.

| Run | Source SHA-256 | Result | Time / peak RSS | Scope |
|---|---|---|---|---|
| q-v2 | `33388a99f87c9e17f6738ffb1ffecb57648a7cd26a1fe6cca15e9ccddf941294` | 72 checks, 1 unreachable, 0 failed | 0.415 s / 135,348 KiB | High 2 GiB, max 4 GiB, swap 0 |

q-v1 is retained as a failed diagnostic: equality on the aggregate `Option<Q>` lowered to a `memcmp` loop and hit an unwinding assertion. q-v2 replaces only that assertion with the four fieldwise comparisons; no unwind setting was relaxed.

## Standard-library source availability and correspondence boundary

The Kani log identifies its expanded implementation under the Kani runner's `library/core/src/array/mod.rs`; that `rust-src` file is not installed in the runner. The frozen SBF build reports Rust 1.89.0/LLVM 20.1.7, but its sysroot `library/core/src/array/mod.rs` is also absent. The retained Aeneas translation audit records `core::array::from_fn` as external and says no exact source function was found in the inspected Std files. The only local Rust source tree found is for a different `nightly-2026-06-01` toolchain, so it is not used as evidence for either pinned compiler. No large Rust source tree was downloaded. Consequently, the Kani result validates the actual Kani toolchain's `from_fn` behavior for these bounded harnesses, but source-body identity across Kani, SBF, and Aeneas/frozen extraction remains open.

For Kani only, I fetched the two small upstream files from the exact compiler commit. `check-critical-bodies.py` pins the `from_fn`, `try_from_fn`, `try_from_trusted_iterator`, `try_from_fn_erased`, `Guard::push_unchecked`, `NeverShortCircuit::wrap_mut_1`, and `NeverShortCircuit::branch` bodies by source file SHA, line span, and whitespace-normalized body SHA. No body comparison against the SBF fork is claimed: its exact Rust commit is not exposed by the retained `rustc -Vv` record, and its source file is unavailable. `toolchain-pins.json` records the compiler binary and source limitations.

The proofs use arbitrary precomputed callback traces rather than the Aspis callbacks. They validate fixed-array call order, output placement, and state threading under a named Kani/Std boundary; they do not discharge the frozen caller, source adapter, or Lean proof obligations.
