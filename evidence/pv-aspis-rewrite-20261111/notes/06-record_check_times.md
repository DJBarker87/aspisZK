# 6. `record_check_times` (thread-local timing store)

File: `crates/aspis-r1-cost-probe/src/prover.rs` (module is
`#[cfg(feature = "prover")]`; the timing code is `#[cfg(feature = "r1p-check")]`).

## Readers of the thread-local, all read before the change

`CHECK_TIMES` is private to `prover.rs`. It is written in one place and read in
one place, `prover::take_check_times()`, which empties it. Callers of
`take_check_times` in the tree:

* `crates/aspis-r1-cost-probe/examples/r1p_retry_gate.rs` lines 45, 56, 87, 91:
  empties the store, calls `prove_masked_attempt` (or `prove_masked_retrying`),
  then reads it and expects one record per attempt.
* `crates/aspis-r1-cost-probe/src/prover_retry_tests.rs` lines 86, 88, 104: the
  same pattern around `prove_masked_retrying`.
* (new) `tools/r1-cost-probe/src/bin/pv_bytes_gate.rs` and the new client test.

Every reader reads after a public proving call has returned. None reads from
inside a callback that runs during a proving call.

## Old shape

`public_check` ran the checker, then called the private function
`record_check_times(times)`, which pushed the record to the thread-local; then it
turned the verdict into `Ok(())` or `Err(Rejected)`. `public_check` is called from
`prove_from_semantics`, which is called from `prove_masked_with_attempt`, which
is called from the public functions `prove_masked_attempt` and
`prove_masked_fixture`; the retry loop `retry_attempt` called
`prove_masked_attempt`.

## New shape

* `public_check`, `prove_from_semantics` and `prove_masked_with_attempt` take one
  more argument, `times: &mut CheckTimesLog` (`Vec<R1CheckTimes>` with the feature
  `r1p-check`, `()` without it), and `public_check` pushes the record to it at the
  place where it used to call `record_check_times`. These three are private.
* `prove_masked_attempt_timed` (new, public) is the former body of
  `prove_masked_attempt` with that argument. `retry_attempt` calls it and passes
  its own `times` argument on, and `prove_masked_retrying_from_timed` (new,
  public) is the former body of `prove_masked_retrying_with` for an explicit
  provider, with that argument. None of these touches thread-local state.
* The public functions with unchanged signatures, `prove_masked_attempt`,
  `prove_masked_fixture` (and through it `prove`), `prove_masked_retrying_with`
  (and through it `prove_masked_retrying`), are shells: each creates a
  `CheckTimesShell`, passes its log down, and returns the result. Dropping the
  shell appends the log to the thread-local, in order. `record_check_times` is
  gone; its one effect is the body of that `Drop`.

No public signature changed. New public items: `prove_masked_attempt_timed`,
`prove_masked_retrying_from_timed`, `CheckTimesLog`, `CheckTimesShell`.

## Why the behaviour is the same, and the one place where it is not

Proof bytes, the audit, errors and their order, nonce reservations, hash calls and
randomness do not involve the timing records at all: the only change on those
paths is one more reference passed down and a `Vec::push` in place of a
thread-local push at the same program point.

For the store: after a public proving call returns, the thread-local holds exactly
the records the pin would have put there during that call, in the same order (one
per P_R1 check actually run, including rejected checks, none for a forced test
verdict). The shell is dropped when the public function returns and also when it
unwinds, so a panic after a check still leaves that check's record, as before.

The difference: the records of a call now arrive in the store when the call ends,
not at each check. Code that runs on the same thread during a public proving call
and reads `take_check_times()` would have seen the earlier attempts' records at
the pin and now sees none until the call ends. The only caller-supplied code that
runs during such a call is the `next_attempt` / `proof_account` callback and the
`hash` function pointer. No such reader exists in the tree (list above). This is
a change in the timing telemetry only.

## What the extraction should take as roots

`prove_masked_attempt_timed` in place of `prove_masked_attempt`, and
`retry_attempt` / `prove_masked_retrying_from_timed` in place of
`prove_masked_retrying`: these have the proving behaviour and no thread-local.
The shells are four-line wrappers whose `Drop` is the telemetry.
