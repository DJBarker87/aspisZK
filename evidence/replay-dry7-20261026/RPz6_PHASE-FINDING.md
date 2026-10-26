# Phase identity gate failed; replay chain stopped

The proposed lead-owned RPz6_S1SemanticPhaseV1 removes the duplicate alias
without editing S1SemanticPhaseV1 or any session A source. Its requested theorem
RPz6_PhaseAgreement is **not established**. It fails at line 8 on the retained
larger-cohort view, using the exact dependencies recorded in RPz6_002.json.
RPz6_001 successfully prints BOTH actual inductive declarations:

```text
inductive AspisR1PublicPreparation.verifier.Phase : Type
number of parameters: 0
constructors:
AspisR1PublicPreparation.verifier.Phase.Parsed : AspisR1PublicPreparation.verifier.Phase
AspisR1PublicPreparation.verifier.Phase.Semantic : AspisR1PublicPreparation.verifier.Phase
AspisR1PublicPreparation.verifier.Phase.SemanticPart : Aeneas.Std.U8 → AspisR1PublicPreparation.verifier.Phase
AspisR1PublicPreparation.verifier.Phase.Prepare : AspisR1PublicPreparation.verifier.Phase
AspisR1PublicPreparation.verifier.Phase.CheckpointRead : AspisR1PublicPreparation.verifier.Phase
AspisR1PublicPreparation.verifier.Phase.Merkle : Aeneas.Std.Usize → AspisR1PublicPreparation.verifier.Phase
AspisR1PublicPreparation.verifier.Phase.Query : Aeneas.Std.Usize → AspisR1PublicPreparation.verifier.Phase
AspisR1PublicPreparation.verifier.Phase.QueryPart : Aeneas.Std.Usize →
  Aeneas.Std.U8 → AspisR1PublicPreparation.verifier.Phase
AspisR1PublicPreparation.verifier.Phase.CheckpointWrite : AspisR1PublicPreparation.verifier.Phase
AspisR1PublicPreparation.verifier.Phase.Relation : AspisR1PublicPreparation.verifier.Phase
AspisR1PublicPreparation.verifier.Phase.Final : AspisR1PublicPreparation.verifier.Phase
inductive AspisR1PublicPreparation.FirstCaller.Phase : Type
number of parameters: 0
constructors:
AspisR1PublicPreparation.FirstCaller.Phase.Parsed : AspisR1PublicPreparation.FirstCaller.Phase
AspisR1PublicPreparation.FirstCaller.Phase.Semantic : AspisR1PublicPreparation.FirstCaller.Phase
AspisR1PublicPreparation.FirstCaller.Phase.SemanticPart : Aeneas.Std.U8 → AspisR1PublicPreparation.FirstCaller.Phase
AspisR1PublicPreparation.FirstCaller.Phase.Prepare : AspisR1PublicPreparation.FirstCaller.Phase
AspisR1PublicPreparation.FirstCaller.Phase.CheckpointRead : AspisR1PublicPreparation.FirstCaller.Phase
AspisR1PublicPreparation.FirstCaller.Phase.Merkle : Aeneas.Std.Usize → AspisR1PublicPreparation.FirstCaller.Phase
AspisR1PublicPreparation.FirstCaller.Phase.Query : Aeneas.Std.Usize → AspisR1PublicPreparation.FirstCaller.Phase
AspisR1PublicPreparation.FirstCaller.Phase.QueryPart : Aeneas.Std.Usize →
  Aeneas.Std.U8 → AspisR1PublicPreparation.FirstCaller.Phase
AspisR1PublicPreparation.FirstCaller.Phase.CheckpointWrite : AspisR1PublicPreparation.FirstCaller.Phase
AspisR1PublicPreparation.FirstCaller.Phase.Relation : AspisR1PublicPreparation.FirstCaller.Phase
AspisR1PublicPreparation.FirstCaller.Phase.Final : AspisR1PublicPreparation.FirstCaller.Phase
'AspisR1PublicPreparation.verifier.Phase' does not depend on any axioms
'AspisR1PublicPreparation.FirstCaller.Phase' does not depend on any axioms
```

The exact equality check and full diagnostic axiom result are:

```text
RPz6_sources/RPz6_S1SemanticPhaseV1.lean:8:2: error: Tactic `rfl` failed: The left-hand side
  AspisR1PublicPreparation.verifier.Phase
is not definitionally equal to the right-hand side
  AspisR1PublicPreparation.FirstCaller.Phase

⊢ AspisR1PublicPreparation.verifier.Phase = AspisR1PublicPreparation.FirstCaller.Phase
'RPz6_PhaseAgreement' depends on axioms: [sorryAx]
```

Both are separate nominal inductive types, with the same eleven constructors
and payload types. Neither definition unfolds to the other. The library's
propext is propositional extensionality, not type univalence. A constructorwise
isomorphism would not itself prove equality of these Type-valued constants.
No named standard-axiom proof of their type equality is supplied by the
selected source. This finding is a failure of the requested identity gate;
it is NOT a kernel proof of type inequality or a proof that the two phase
languages have different observable behavior. A failed rfl alone is not a
mathematical impossibility theorem. Historical S1 and Tx1 use distinct nominal
objects, and their semantic equivalence requires an explicit transport proof.

The diagnostic theorem has sorryAx because Lean recovers after a failed proof.
It is rejected. No result from this module is imported, installed, or counted
as green. The failed proposal is retained as .lean.txt evidence. No new axiom,
sorry/admit/native_decide, type equality hypothesis, carrier substitution or
weakened consumer has been added to an accepted proof.

Per lead ruling (2), STOP this chain. Rc7..Rc10 are not launched. The current
smaller selected replay view is unchanged; the larger RPz5 view remains a
probe. It would be misleading to change imports and claim statement identity
before resolving this type identity issue. The requested complete before/after
KERNEL statement comparison cannot run because no coherent fresh top exists.

Recommended next deliverable (requires a revised lead repair scope): prove
explicit bidirectional Phase transports and observer/function congruence for
the actual S1/Tx1 uses, then preserve the complete theorem statement through
those transports. An isomorphism must not be reported as the requested type
equality. Alternatively reconcile a single Phase owner upstream, with all
changed dependents rebuilt. This worker performs neither unapproved repair.

## Attempt receipts

| Attempt | Target | Exit | Wall s | Peak RSS KiB | Swaps | Axioms |
|---|---|---:|---:|---:|---:|---|
| RPz6_001 | RPz6_PhaseInspection | 0 | 1.513933435024228 | 3840724 | 0 | both Phase declarations: none |
| RPz6_002 | RPz6_S1SemanticPhaseV1 | 1 | 1.5595192959881388 | 3836172 | 0 | rejected diagnostic RPz6_PhaseAgreement: sorryAx |

Both use the unchanged S2W runner, one admitted systemd scope at a time,
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean -j1 -M7000
-DElab.async=false. Source revision 0f812d75fc, dirty evidence sources with
exact SHA256 in each receipt. Full argv, selected object hashes, reservation
logs, source hashes, cgroup limits and raw stdout/time/axiom lines are retained
under RPz6_001/ and RPz6_002/. No timeout, memory kill, cap change, admission
retry, unchanged failed-input rerun, Kani, Rust or ELF rebuild occurred.

## Existing transport, for a revised scope

`docs/research/100bit-spend-path-20261013/lean/bridge-verify-prefix-fe80-20261017/ExtractedFirstHelperBinding.lean`
already defines `AspisR1PublicPreparation.FirstHelperBinding.phaseToFirst`
constructor by constructor from producer verifier.Phase to FirstCaller.Phase,
and maps observer callbacks through it before Tx1Model.tx1. This is source
inspection, not a new compile or a type-equality theorem. The current caller's
`CurrentCompactFirstCompositionV1.retainedPhase` is another explicit map,
from the current caller's own Phase. These existing maps support a transport
repair direction; neither makes the two requested types definitionally equal.
