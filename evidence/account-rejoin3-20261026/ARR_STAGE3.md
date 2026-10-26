# ARR stage 3: acceptance does not repair an off-path global oracle factory

ARR_OffPath.factory_forces_reads (071) proves a necessary condition for exactly
this factory schema, with fixed `hashv` and arbitrary `Program Bytes State X`:

    ∀ K, accepts (eval K p).2 → ∃ sha256, P1 sha256 K ∧ RuntimeSyscall hashv sha256

For ANY accepted execution in H, EVERY flattened input where hashv returns a
digest must occur among that execution's issued addresses. Proof: alter H at an
unqueried returning address. ARR_OffPath.incompatible_same_run constructs K
with `eval K p = eval H p` but no global compatibility with hashv. All adaptive
choices, full original cost and outcome remain literally unchanged.

ARR_FactoryLoss.same_execution (075) retains ANY predicate of the complete
original run in that counter-world. ARR_FactoryLoss.bounded_no_factory gives
the explicit sufficient obstruction: a nonempty accepted class, uniform issued
budget N < 256^32, and fixed hashv returning on all valid one-part 32-byte
messages. It then refutes the global factory. `return32` is an EXPLICIT extra
condition in this negative diagnostic, NOT new adopted trust and NOT a theorem
about the pinned native runtime. Without that condition, 071 needs only ONE
unqueried returning address.

This is stronger than the inherited fixed-H warning: even an acceptance guard
cannot discard the counter-world, because the entire execution is identical.
A proof of ARQ_WorldSupport.Supported would project exactly the forbidden
oracle-witness schema by taking each NativeAt.sha256/p1/syscall. Concrete account
instantiation is not compiled here because the account closure remains missing.
No full Rc10 independence/counterexample, bank fixture, actual deployed attack,
or proof of actual native return32 is claimed. A bank/game predicate encoded in
the run is preserved by the generic theorem; the actual same-run bank/native
representation still needs construction.

Replacement target: an execution-indexed oracle/native interpretation (or an
on-reached-call factory with its proved ROM/measure transport), rather than a
fixed closed hash dictionary's global P1 in every world. Do not add global
Supported or return32 as a trusted top premise to conceal this obstruction.

Symbolic preflight: 072 hit the default recursion limit while proving finite
state freshness directly on a concrete function-space Finset. No cap/depth
option was raised. The replacement isolates ABSTRACT cardinality transport in
ARR_FiniteFresh.missing (073), then instantiates it in ARR_FreshState (074),
then the consumer (075). No concrete 256^32 universe was enumerated. All pass.

ARR_CoveredExamples (076) proves reached-read coverage inhabited in the ideal
H-indexed dictionary and also on pure rejected source steps. These are ONLY
certificate examples, explicitly NOT headline non-vacuity or a fixed native
extraction witness. Headline joint real-byte non-vacuity remains open.

75 actual Lean invocations through076:65 pass,10 excluded failures;002 remains
prelaunch only. 0 Kani. All new printed theorem axioms are standard-only.
Additional unchanged dependency builds044-070 passed. Their local queue wrapper
was stopped AFTER attempt070's compiler and receipt collection completed, with
no live child left; wrapper exit137 is an intentional LOCAL orchestration stop,
not a memory-killed/timed-out Lean job. No host scope/compiler was killed.
The direction changed to the independent off-path proof before resuming needed
dependency work with the remaining budget.

Uncompiled coverage/carrier/native-account/game-padding drafts were moved to
*_PENDING.lean.txt in this receipt directory; none remains an accepted lean/
module. Actual Rc10 top and ledger remain unchanged, zero removal credit.
