# S6 selected-terminal guard audit

Status: source-static evidence only; it is not a literal Rust refinement or a
payment-correctness theorem.

The S6 upper-bound route needs to delete only the terminal equality rejection
after a real accepted execution has constructed its semantic context.  The
selected direct call site is `performance_verifier.rs::semantic`: it computes
the ten semantic challenges and the 84 point-claim projection, calls
`payment_terminal`, then compares its returned field value with `s.claim`.

The static audit in `experiments/s6_terminal_effect_audit.py` fixes the current
source hashes and checks the direct terminal body for the shared SHA transcript
API (`Transcript`, `sha2`, `HashFn`, `hash(` and `solana_program`).  It also
checks that the selected private-transfer and withdrawal compiled terminal
symbols, and the selected mask evaluator, are present in the direct route.
The generated terminal module imports field/Poseidon arithmetic and does not
import that shared SHA API.

Thus, at this source-static boundary, removing the *Boolean equality decision*
does not remove an observed operation of the SHA transcript used by the later
ordinary suffix.  The valid direction is one-way:

`selected accepted run -> same parsed body and dynamic semantic prefix ->
guard-relaxed suffix run`.

This does **not** show that the computed terminal value is correct, that the
source is effect-free in a machine-semantics sense, that Rust refines the Lean
script, or that the relaxed program has the same acceptance distribution.  In
particular, the existing `SelectedTerminalCallback` remains an unresolved
source-refinement interface.  The audit only removes payment validity as an
unnecessary precondition for this local accepted-run inclusion.

Reproduce from the repository root:

```sh
python3 docs/research/v8-completion-fs-extraction-20260911/experiments/s6_terminal_effect_audit.py
```

Changing either audited source changes the recorded hash and requires rerunning
the audit before this evidence can be reused.
