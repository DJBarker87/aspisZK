# Stage 1: native writer on joint witnesses

Before: SdkD_Accepted.accepted_pair_unified exports a Tx1Q Run and reference
writer result; WAdm_NativeAccepted exports native writer separately.
After: CPhy_Accepted.accepted_pair_unified exports BOTH writer results on the
very same Run, prepared value, flushed accumulator, input slices and saved Vec,
inside the original existential and before WhenBound. All SdkD conclusions,
including Tx2N Outcome, remain unchanged. Its proof destructs SdkD's own Run
and applies WAdm_NativeInstall.on_run directly: no second SourceCuts, chosen
execution, output agreement or dictionary compatibility hypothesis is added.
Uni_Install.compose_tx1 is the existing checked equality connecting the union
installation to Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops).

The two explicit owner parameters are exactly WAdm's retained immutable
SessionAPrepare and query SessionAPrimitives, specialized to that installed
Run; no new writer-admission assumption is introduced. Runtime, extraction,
SDK, arithmetic, parser, authentication and WhenBound boundaries remain.
This is a success-conditioned accepted-pair theorem, not all-outcome oracle
transport or an ELF execution theorem.

Ledger delta: L171-remainder/composition REMOVED for this joint endpoint.
Added row IDs: none. L091-L093/L100-L109 remain to be discharged. No global
ledger file is edited (prefix-only assignment).

Non-vacuity: the construction adds a derived conjunct to an existing Run,
without restricting its acceptance. WAdm_Nonvacuity and SdkD_Nonvacuity are
reused within their local stated domains; no joint cryptographic accepted
fixture is claimed.

Validation: CPhy_001, exit 0, wall 2.932285 s, peak RSS 5241012 KiB, swap 0.
Source revision b57e886291a629af05b3fd7bcc497f1fe4f71500 plus exact dirty
source snapshot/hash in receipt. Axioms [propext, Classical.choice, Quot.sound].
Coherent SInt2 workspace and unchanged cached objects reused. Scope verified
6G/8G/swap0/64 tasks; Lean -M7000. Budget 1/100 Lean, 0/30 Kani.
No shipped source/artifact or keys changed; no ELF rebuild trigger.
