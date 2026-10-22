# S4 `from_fn` Guard-only extraction evidence

This packet records three distinct Charon outputs for the isolated Std
`from_fn` probe. It contains source JSON/LLBC and receipts only; it contains no
compiled executable or Lean object.

1. `attempts/01-union-transparent` is the initial selection experiment. It
   included `MaybeUninit` transparently, producing an LLBC union. That cut was
   not used for an Aeneas run because the retained Aeneas path has unsupported
   union handling.
2. `attempts/02-guard-only-selector` is the supported selective cut. It makes
   the `Guard` type and its push/drop bodies transparent while making the
   `MaybeUninit` type opaque. This is an LLBC inspection result only; it does
   not establish that the remaining opaque operations preserve the needed
   state invariant.
3. `attempts/03-guard-only-cgroup-verification` repeats the exact selector to
   record process-level cgroup evidence. Its LLBC is structurally identical
   to attempt 2 after disregarding only the output path and the ordering of
   `short_names`. Both outputs are retained. The initial run's launcher
   receipt recorded wrapper-scope limits; only attempt 3 records `/proc` cgroup
   membership and limits for the actual Charon, Cargo, and `time` PIDs.

The Rust workspace was `/home/dombarker/project-offloads/s4-stdlib-fromfn-isolation-v1-20261021/source_workspace`, with source hashes recorded in each `source-pins.json`. Charon was pinned by SHA-256
`daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`.
The installed toolchain reported `rustc 1.98.0-nightly (14210df0e 2026-05-31)`;
`library/core/src/array/mod.rs` has SHA-256
`fa149bb7f1e856350ccbf94cd402f368ec7f613b8a1d1eeeafffe85b5e75277f`.
This is the retained 1.98 isolation workspace, not the frozen SBF 1.89-dev
sysroot source. It is therefore a source-analysis candidate and does not by
itself discharge the frozen S4 standard-library boundary.

The supported cut emits 92 functions and 31 types with `has_errors=false`.
`MaybeUninit` (type def 7) is `Opaque`; `Guard` (type def 9) is a transparent
struct. `from_fn`, `try_from_fn`, `try_from_fn_erased`, `Guard::push_unchecked`,
the `Guard::drop` implementation, its drop glue, and slice `get_unchecked_mut`
are emitted as transparent functions. The LLBC still leaves representation
operations such as `MaybeUninit::{uninit,write,array_assume_init,
assume_init_drop}` and `usize::unchecked_add` foreign/opaque. No Aeneas result or
semantic theorem is claimed here.

For the process-level run, PIDs 1148420 (`time`), 1148421 (Charon), and 1148451
(Cargo) all reported the same cgroup path:
`/user.slice/user-1000.slice/user@1000.service/app.slice/aspis-s4-fromfn-guard-cgroup-verify-v1-20261022-charon-1148377-1792641271108772976.scope`.
Each process's sampled cgroup limits were `memory.high=1073741824`,
`memory.max=2147483648`, and `memory.swap.max=0`. The extraction exited 0 in
0.404 seconds; reported peak process RSS was 131120 KiB, process swaps were 0,
and no timeout or OOM event was recorded. The sampled cgroup peak and process
RSS are different metrics; the recorded PID paths establish that the processes
were inside the capped scope.

`check_packet.py` verifies the retained LLBC hashes, successful extraction
receipts, the two-output structural comparison, key emitted transparency
properties, and absence of compiled/binary artifacts. Run it from this
directory with:

```sh
python3 check_packet.py
```

The LLBC structural comparison is intentionally precise: attempt 2 and attempt
3 have identical declaration/body/type content and identical `short_names`
entries as a multiset. Their only structural differences are
`translated.options.dest_file` and `translated.short_names` list ordering.
