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
