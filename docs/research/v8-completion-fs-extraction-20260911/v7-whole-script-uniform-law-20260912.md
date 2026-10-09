# Uniform finite-tape law for the whole transcript script

Status: **exact ideal finite-tape transport proved; deployed/adversarial ROM
coupling remains open**.

`lean/FSV8V7WholeScriptUniformLaw.lean` lifts the deterministic whole-script
alignment to an exact PMF equality.  For any bounded causal `Script`, explicit
total/fresh-call room and a sufficiently long finite tape, it proves pointwise
that:

- the current interpreter and V7 `runMachineFromUniformFreshTape` return the
  same value or the same explicit controller-refusal outcome;
- no other V7 resource/programming/fuel halt occurs under those bounds; and
- their final cache, fresh counter and ordered log are literally the same after
  projecting the V7 state.

It then proves equality between the pushforward of the current interpreter on
a uniform recursive `FreshAnswerTape` and the projected V7 uniform machine
law.  A second theorem transports the equivalent uniform
`Fin steps -> Block` representation through the existing tape equivalence.

The source measure here is defined to be a uniform finite tape.  This theorem
does not say that the deployed random oracle, an adaptive adversary's prior
queries, programmed extractor forks or the selected Rust execution induce
that law.  Those are the next coupling obligations.

## Focused evidence

- Base revision: `604fcb4d597382803261bac265f693180f9e0746`.
- Target: `FSV8V7WholeScriptUniformLaw.lean`.
- Source SHA-256:
  `98b9724ba62a74f5877a530312e4312f88f30a927490e824026ee7fe4843faee`.
- Olean SHA-256:
  `4da449409e0e064500b2069fd889f192aab487e1aad344f649299aedfe7c4d3d`.
- Pinned Lean 4.32.0 NUC compile: exit 0, wall 2.82 seconds, peak RSS
  6,539,360 KiB, swap 0.
- Cgroup: `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`, bounded runtime.
- Printed axioms: `propext`, `Classical.choice`, `Quot.sound` only.

No protocol, byte, challenge or verifier check changes.  The body cap remains
40,282 bytes and grinding security credit remains zero.
