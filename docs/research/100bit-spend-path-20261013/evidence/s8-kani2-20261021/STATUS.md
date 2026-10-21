# S8 continuation

Stage 1: three local base/step/exit Kani roots pass (`kani2-04`). This first
preflight is bounded to destination prefixes of length at most three; it is
not an arbitrary-length frozen traversal claim. The step uses the real
`IterMut::next` on an unconsumed suffix, the literal shipped body, and the
owned reducer. No reducer stub. All raw lanes are symbolic U64. Failed CLI,
workspace bootstrap and memcmp-unwinding attempts are retained (01–03).

Lean finite-step induction and production-size step are in progress. No
headline premise removed and no frozen whole-loop timeout rerun.

Stage 2: production-capacity base/exit pass in `kani2-05`; its step times out
at 180s, cgroup peak 6,562,201,600 bytes, zero swap. Replacement `kani2-06`
factors raw[cursor] to one arbitrary selected U64 row and checks all 64
cursor/probe positions in 23.66 solver seconds without stubs. This is a local
read abstraction, not the timed-out whole-loop harness. The arbitrary-vector
read join is proved separately in Lean.

`S8Kani2ReferenceInduction.reference_finish_induction` derives the actual
emitted reference traversal from exactly destination-length many reference
steps. `S8Kani2FinishCertificate.finish_certificate` combines that induction,
the retained concrete reference certificate, and a total mutable-model
traversal with exact pointwise value calls. Its only finish precondition is
destination length <= raw length. All accepted axiom audits are standard.
The mutable model is copied under new module names from the retained
20261019 write-back model, with reuse provenance; no existing Lean module
is edited. The remaining kernel join to the new reference outputs is next.

Stage 3: `S8Kani2FinishReferenceJoin.finish_reference_simulation` now proves
complete pointwise mutable-model/owned-reference agreement, with the raw
read relation derived at each arbitrary index and no value-success premise.
`S8Kani2CallerJoin.p6_certificate` is the named certificate;
`finish_caller_join` transports the caller's exact raw congruence to all
canonical finalized sum coordinates. Both compile with standard axioms.

The P6 source step uses the real Rust iterator over a related suffix/cursor
state. This is not a kernel extraction of Rust's unsafe pointer iterator;
that model boundary is stated explicitly in source-binding.json. Global S8
remains open until S7/R15 identify the actual reached vectors/sums and the
headline interprets its free S8 proposition as the concrete certificate.
No claim is made that a named certificate alone proves any arbitrary S8.

Final isolation stage: all copied mutable declarations, including the slice
and prefix helpers, now have S8Kani2 namespaces. Changed modules and their
dependencies were checked individually again. Final source packet: 13 Lean
modules, 32 standard-axiom audits, six successful Kani roots. Full ledger:
35 Lean attempts and six host attempts, including failures and superseded
namespace versions. Zero swap. `remaining.tsv` and `upstream-status.json`
record why global S8 cannot yet be marked discharged.
