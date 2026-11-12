# 7. `p_r1_check` (not rewritten)

File: `docs/research/v8-r0-zk-20261009/z4/z9e.rs`, lines 607-614 on the branch
(unchanged from the pin).

The function is the shell around the pure core. In eight lines it installs a
process-wide panic hook once (`install_quiet_hook`, a boxed `dyn Fn` closure, the
`dyn` type reported at 507:38), sets a thread-local flag, reads the wall clock,
runs `transport_gate(..) && p_r1_stages(ch, &mut clk)` inside
`std::panic::catch_unwind(AssertUnwindSafe(|| ..))`, clears the flag and returns
the verdict with the timings accumulated in `clk`.

The reported "Can't copy a mutable borrow" at 611:126 is the `&mut clk` captured
by the closure given to `catch_unwind`. Passing the clock by value into the
closure would remove that message but is not behaviour-preserving as it stands:
when the check panics (which is a rejection), the timings accumulated up to the
panic are returned today, and a clock moved into the closure is lost with the
unwinding. And it would not make the function translate: the panic hook, the
thread-local flag, `Instant::now` and `catch_unwind` remain, and none of them is
first-order code.

So this is not a small local change, and it was not made. The function's pure
content is already separate: `p_r1_core` / `p_r1_stages` (same file) are the
verdict with no clock, no thread and no process state, and `r1p_tests.rs` compares
the shell with the core. The shell stays an opaque item with the contract
"verdict = transport gate passes and `p_r1_stages` returns true without
panicking".
