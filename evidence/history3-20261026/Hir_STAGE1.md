# Hir stage 1: partial source transcript

Checked Hir_PartialOracle.exact proves result equality and complete successful
read-log equality for every source Result, including error/divergence/rejection.
It does so for an explicitly different partial-syscall experiment: fixed native
failure status is tested before an ideal read. No probability-law equality with
SdkC_Oracle.program is claimed. Hir_PartialPrefix.read_prefix and budget prove
that this experiment only truncates the original ideal log and inherits its
all-world query bound. This does not justify substituting its output distribution.

Hir_CallSource.effect connects the actual selected first/second full wrapper
(including allocation/copy/cleanup) to computed ledger effect on all outcomes,
under the inherited extraction/P1/successful-syscall boundaries. No independent
child-success hypothesis or caller-supplied output/trace is required.

Lean attempts 1–6: 4 passing, 2 failed development statements (reserved name and
prefix witness simplification), retained verbatim. All passing theorem audits
use exactly propext, Classical.choice, Quot.sound. No failed theorem is accepted.
Every receipt contains target, revision, source hash, direct dependency hashes,
exit/wall/peak RSS/swap, cgroup limits and axiom lines. No cap was raised.

Pool extraction: Hir_CHARON001 includes iterator semantics to isolate the prior
borrowed zero-guard obstruction. Optimized extraction passes (17.01355s,573384KiB,
swap0). Hir_AENEAS001 still fails at SymbolicToPureValues.ml:878, source
pair_forest.rs:400–415 (0.33081s,74092KiB,swap0). No Pool lifecycle theorem follows.
The extraction reused the predecessor's source/cache and did not edit its source.
No launcher/tool/monitor repair attempted. No shipped-source counterexample found.

Ledger delta: zero; all six assigned rows remain open in T2R_Top.deployed.
Next: adaptive scheduling with computed store/load association, explicit Q1
accounting, and a source-derived Pool lifecycle instance. L159 untouched.
