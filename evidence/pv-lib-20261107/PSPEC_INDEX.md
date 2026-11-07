# PLIB frozen row specification index

Target not yet established. Revision 1: 29 specifications; no ledger closure or row-proof consumption.

Read PSPEC_COMMON.md as part of EVERY row. Inputs are pinned by INPUT_REVISIONS.json and INPUT_MANIFEST.json. This is a normative Markdown contract package; it is not a claim that 29 Lean contract declarations or candidates compiled.

| Row | Specification | Source function |
|---|---|---|
| `thread:f170` | [PSPEC_thread_f170.md](PSPEC_thread_f170.md) | `std::thread::local::impl[inherent]::try_with` |
| `thread:f17` | [PSPEC_thread_f17.md](PSPEC_thread_f17.md) | `std::thread::local::impl[inherent]::with` |
| `thread:f2` | [PSPEC_thread_f2.md](PSPEC_thread_f2.md) | `aspis_r1_cert_check::native_workers::is_worker` |
| `thread:f5` | [PSPEC_thread_f5.md](PSPEC_thread_f5.md) | `aspis_r1_cert_check::native_workers::impl[inherent]::enter` |
| `thread:f361` | [PSPEC_thread_f361.md](PSPEC_thread_f361.md) | `std::thread::lifecycle::spawn_unchecked` |
| `thread:f270` | [PSPEC_thread_f270.md](PSPEC_thread_f270.md) | `std::thread::scoped::impl[inherent]::spawn_scoped` |
| `thread:f166` | [PSPEC_thread_f166.md](PSPEC_thread_f166.md) | `std::thread::scoped::impl[inherent]::spawn` |
| `thread:f15` | [PSPEC_thread_f15.md](PSPEC_thread_f15.md) | `aspis_r1_cert_check::native_workers::ordered_map_inner::impl[3]::call_once` |
| `thread:f208` | [PSPEC_thread_f208.md](PSPEC_thread_f208.md) | `std::thread::scoped::scope::impl[24]::call_once` |
| `thread:f220` | [PSPEC_thread_f220.md](PSPEC_thread_f220.md) | `core::panic::unwind_safe::impl[26]::call_once` |
| `thread:f316` | [PSPEC_thread_f316.md](PSPEC_thread_f316.md) | `std::panicking::catch_unwind::do_call` |
| `thread:f318` | [PSPEC_thread_f318.md](PSPEC_thread_f318.md) | `core::intrinsics::catch_unwind` |
| `thread:f219` | [PSPEC_thread_f219.md](PSPEC_thread_f219.md) | `std::panicking::catch_unwind` |
| `thread:f125` | [PSPEC_thread_f125.md](PSPEC_thread_f125.md) | `std::panic::catch_unwind` |
| `thread:f6` | [PSPEC_thread_f6.md](PSPEC_thread_f6.md) | `std::thread::scoped::scope` |
| `thread:f1` | [PSPEC_thread_f1.md](PSPEC_thread_f1.md) | `aspis_r1_cert_check::native_workers::ordered_map_inner` |
| `thread:f0` | [PSPEC_thread_f0.md](PSPEC_thread_f0.md) | `aspis_r1_cert_check::native_workers::ordered_families` |
| `thread:OwnInit` | [PSPEC_thread_OwnInit.md](PSPEC_thread_OwnInit.md) | `OwnInit (composition root; not a separate emitted function)` |
| `slice:f21` | [PSPEC_slice_f21.md](PSPEC_slice_f21.md) | `alloc::slice::impl[inherent]::to_vec_in::impl[17]::to_vec` |
| `slice:f13` | [PSPEC_slice_f13.md](PSPEC_slice_f13.md) | `alloc::vec::impl[4]::clone` |
| `slice:f6` | [PSPEC_slice_f6.md](PSPEC_slice_f6.md) | `core::array::impl[3]::clone::impl[6]::call_mut` |
| `slice:f8` | [PSPEC_slice_f8.md](PSPEC_slice_f8.md) | `core::ops::try_trait::impl[inherent]::wrap_mut_1::impl[8]::call_mut` |
| `slice:f7` | [PSPEC_slice_f7.md](PSPEC_slice_f7.md) | `core::ops::try_trait::impl[inherent]::wrap_mut_1::impl[7]::call_once` |
| `slice:f9` | [PSPEC_slice_f9.md](PSPEC_slice_f9.md) | `core::array::try_from_fn_erased` |
| `slice:f4` | [PSPEC_slice_f4.md](PSPEC_slice_f4.md) | `core::array::try_from_fn` |
| `slice:f5` | [PSPEC_slice_f5.md](PSPEC_slice_f5.md) | `core::array::impl[3]::clone::impl[5]::call_once` |
| `slice:f2` | [PSPEC_slice_f2.md](PSPEC_slice_f2.md) | `core::array::impl[3]::clone` |
| `slice:f1` | [PSPEC_slice_f1.md](PSPEC_slice_f1.md) | `core::array::impl[1]::clone` |
| `slice:f0` | [PSPEC_slice_f0.md](PSPEC_slice_f0.md) | `aspis_statement::state_only_trace::impl[0]::clone` |
