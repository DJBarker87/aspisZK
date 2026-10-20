# Constructed protocol privacy endpoint — 2026-10-21

Branch `codex/cx-priv-endpoint-20261021`, base `b9c171232`.

## Stage 1: composed privacy specialization

`R1Z.PrivacyR1FinalProtocol.privacy_R1_protocol` specializes the unchanged
`PrivacyR1Final.privacy_R1_final` to `PhaseProtocolInstanceBin.baseWire` and
the composed `prover`. It removes the universal `R_causal_D80` by
`causal_premise`, the eight `R_commit_D80` families by the constructed
commitment grammar, and D/ι/hι/R_wire_Sem1Uniform by the concrete rows01,
algebraMap injection and sampler_source. Residual premises have the original
quantifiers, specialized to this instance. Typed read coverage is retained
in this stage pending the length/coverage check.

Env J attempt 9603: exit 0, wall 7.44 s, peak RSS 4,060,832 KiB, swaps 0.
Both theorem audits: `[propext, Classical.choice, Quot.sound]`.
Exact source revision/hash, dependency objects/fingerprint, full audits,
diagnostics and timing for attempts 9600–9603 are committed in
`endpoint-attempts-9600-9799.jsonl`. Earlier failures were notation elaboration,
AddressAt unfolding, and transport across non-definitionally-equal finite
universe instances; extensional finite-set equality fixes the latter without
enumerating any universe. No cap or heartbeat override was added.

No existing shared source/object was replaced except this branch's own new
endpoint drafts, snapshotted under `snapshots/codex-cx-priv-endpoint-20261021/`.
All attempts use run-joint.sh, env J, -M7000, MemoryHigh=5G, MemoryMax=7G,
MemorySwapMax=0; the launcher reported 24 GiB populated plus 7 GiB.

## Stage 2: coverage, lengths and joint structural satisfiability

`PhaseProtocolCoverageBin` proves wide=32, semantic/opening exact D79/D81
widths, final=2048, C1=480, C2=128, folded=128 including padding. It proves
the existing framing codec equals the privacy grammar byte-for-byte and
constructs a typed transcript whose Rest equals recP.rest. Together with the
constructed commitment grammar and the ≤480 leaf bound, this proves D84
ReadCoverage at every answer vector, including inconsistent/exhausted ones.
The proof counts fixed-width vectors symbolically. It never evaluates a
large address/tape/answer universe, a field element, an FFT, or a recurrence.

The release endpoint now chooses `publicWidth = (base.pubBytes x).length`.
Thus the public-width fact is reflexive and **no ReadCoverage or public-width
premise remains**. The ROM table construction, qmax=2^64, address membership,
fixed transcript/leaf lengths and sampler are proved model components.
Other numeric premises refer to seed counters/tape dimensions and remain:
the constructor does not choose E₁/E₂, L₁/L₂, or tapeOf.

`PhaseProtocolConsistencyBin.construction_checks` proves coverage, commitment
grammar, universal causality, ROM budget, leaf lengths, decoder locality,
sampler-source equality and embedding injection **together** for every base
and seed satisfying the public-width fact. Its
`structural_hypotheses_inhabited` constructs an explicit finite residual base
and seed, and preserves a given valid witness of the public statement. It
therefore does not rely on an empty HonestProver.Instance or an assumed
inhabitant of the wire/prover structures. The witness uses empty public bytes
and a constant tape only to check structural consistency. It is not asserted
to satisfy the remaining uniform-tape, builder or source-execution premises.
This is the requested construction-owned non-vacuity check, not a proof that
all still-conditional deployed-source premises are jointly realizable.

Final focused targets (all env J; standard axioms only; swaps 0):

| Target | Attempt | Exit | Wall | Peak RSS KiB |
|---|---:|---:|---:|---:|
| R1Z/PhaseProtocolCoverageBin | 9611 | 0 | 4.60 s | 4,060,900 |
| R1Z/PrivacyR1FinalProtocol | 9615 | 0 | 11.71 s | 4,060,324 |
| R1Z/PhaseProtocolConsistencyBin | 9616 | 0 | 8.42 s | 4,048,608 |

Intermediate 9607, 9612 and 9614 were green predecessors. Attempts
9604–9606, 9608–9610 and 9613 retain their local elaboration diagnostics;
none failed for memory pressure. Fixes were explicit arithmetic/index
arguments, reduction of structure projections, precise list/byte transport,
and renaming a reserved identifier. No source was retried unchanged with
unchanged dependencies. Final consistency imports the final endpoint, which
imports the final coverage target; this is the focused dependent bridge.
No full frozen-manifest, Rust, SBF, runtime or reproducibility replay was
run: no source or artifact covered by those gates was changed.
